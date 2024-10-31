/*
 *
 *  oFono - Open Source Telephony
 *
 *  Copyright (C) 2008-2011  Intel Corporation. All rights reserved.
 *  Copyright (C) 2010  ST-Ericsson AB.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License version 2 as
 *  published by the Free Software Foundation.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

#include <ell/ell.h>
#include <glib.h>

#include <ofono/log.h>
#include <ofono/modem.h>
#include <ofono/gprs.h>

#include "gatchat.h"
#include "gatresult.h"

#include "veriquecmodem.h"
#include "common.h"

#define MAX_CONTEXTS 255

static const char *cgreg_prefix[] = { "+CGREG:", NULL };
static const char *cgdcont_prefix[] = { "+CGDCONT:", NULL };
static const char *none_prefix[] = { NULL };

//add by puck
#include <pthread.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <ifaddrs.h>

typedef struct
{
    uint32_t thread1_count;
    //uint32_t thread2_count;
	int rmnet_check;
	int retry_count;
    bool found_issue;
    char modem_ip[64];
    char wwan_ip[64];
    int rmnet_state;
    const char *ifname;
    int no_ip_count;
    bool thread1_created;
    bool thread2_created;
	bool pdp_act;
}ql_struct_s;

ql_struct_s ql_data = {
    .thread1_count = 0,
    //.thread2_count = 0,
	.rmnet_check = 0,
	.retry_count =5,
    .found_issue = false,
    .modem_ip = "", 
    .wwan_ip = "", 
    .rmnet_state = -1,
    .ifname = "wwan0",
    .no_ip_count = 0,
    .thread1_created = false,
    .thread2_created = false,
	.pdp_act = false,
};

static void ql_read_wwan_ip(gboolean ok, GAtResult *result,
				gpointer user_data);
static int ql_compare_ips(const char* ip_address1, const char* ip_address2);
static int ql_set_ip_address(const char* interface_name, const char* ip_address);
static void ql_get_ip_address(const char* interface_name, char* ip_address);
static void ql_fix();
static void ql_parse_qnetdevstatus_check(const char *raw_data, int *status);
static void ql_parse_modem_info(char *raw_data, char *modem_ip);
static void ql_read_modem_ip(gboolean ok, GAtResult *result,
				gpointer user_data);
static void ql_read_wwan_ip(gboolean ok, GAtResult *result,
				gpointer user_data);
static void *ql_thread1_function(void *data);
static int check_wwan_modem_ip();
static void ql_qcrmacall(gboolean ok, GAtResult *result,
				gpointer user_data);
//end

struct gprs_data {
	GAtChat *chat;
	unsigned int vendor;
	int last_auto_context_id;
	int attached;
	int rmnet_ready;
};

struct list_contexts_data

{
	struct ofono_gprs *gprs;
	void *cb;
	void *data;
	struct l_uintset *active_cids;
	int ref_count;
};

static struct list_contexts_data * list_contexts_data_new(
				struct ofono_gprs *gprs, void *cb, void *data)
{
	struct list_contexts_data *ret;

	ret = g_new0(struct list_contexts_data, 1);
	ret->ref_count = 1;
	ret->gprs = gprs;
	ret->cb = cb;
	ret->data = data;

	return ret;
}

static struct list_contexts_data * list_contexts_data_ref(
						struct list_contexts_data *ld)
{
	ld->ref_count++;
	return ld;
}

static void list_contexts_data_unref(gpointer user_data)
{
	struct list_contexts_data *ld = user_data;

	if (--ld->ref_count)
		return;

	l_uintset_free(ld->active_cids);
	g_free(ld);
}

static void at_cgatt_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct cb_data *cbd = user_data;
	ofono_gprs_cb_t cb = cbd->cb;
	struct ofono_error error;

	decode_at_error(&error, g_at_result_final_response(result));

	cb(&error, cbd->data);
}

static void at_gprs_set_attached(struct ofono_gprs *gprs, int attached,
					ofono_gprs_cb_t cb, void *data)
{
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	struct cb_data *cbd = cb_data_new(cb, data);
	char buf[64];

	snprintf(buf, sizeof(buf), "AT+CGATT?");

	if (g_at_chat_send(gd->chat, buf, none_prefix,
				at_cgatt_cb, cbd, g_free) > 0) {
		gd->attached = attached;
		return;
	}

	g_free(cbd);

	CALLBACK_WITH_FAILURE(cb, data);
}

static void at_cgreg_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct cb_data *cbd = user_data;
	ofono_gprs_status_cb_t cb = cbd->cb;
	struct ofono_error error;
	int status;
	struct gprs_data *gd = cbd->user;

	decode_at_error(&error, g_at_result_final_response(result));

	if (!ok) {
		cb(&error, -1, cbd->data);
		return;
	}

	if (at_util_parse_reg(result, "+CGREG:", NULL, &status,
				NULL, NULL, NULL, gd->vendor) == FALSE) {
		CALLBACK_WITH_FAILURE(cb, -1, cbd->data);
		return;
	}

	cb(&error, status, cbd->data);
}

static void at_gprs_registration_status(struct ofono_gprs *gprs,
					ofono_gprs_status_cb_t cb,
					void *data)
{
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	struct cb_data *cbd = cb_data_new(cb, data);

	cbd->user = gd;

	if (g_at_chat_send(gd->chat, "AT+CGREG?", cgreg_prefix,
				at_cgreg_cb, cbd, g_free) > 0)
		return;

	g_free(cbd);

	CALLBACK_WITH_FAILURE(cb, -1, data);
}

/*
ql_thread1_function, add new logic, 2024-10-17
case 2: ql_data.pdp_act == false && (ql_data.rmnet_state == 0) && (ql_data.rmnet_check == 1
case 3 : ql_data.pdp_act == ture && (ql_data.rmnet_state == 0) && (ql_data.rmnet_check == 0
case 4: ql_data.pdp_act == ture && (ql_data.rmnet_state == 1) && (ret == 1)
*/
static void* ql_thread1_function(void *data) {
	struct ofono_gprs *gprs = data;
    struct gprs_data *gd = ofono_gprs_get_data(gprs);
	int ret;
	sleep(3); 
    while (1) {
		(ql_data.thread1_count)++;
		quectel_debug(" ql_thread1_function count %d and ql_ofono_verison %s",ql_data.thread1_count, ql_ofono_verison);
		g_at_chat_send(gd->chat, "AT+CGCONTRDP ", NULL, ql_read_modem_ip, gprs, NULL); // check modem ip
		g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);	// check wwan0 ip
		sleep(1);
		ret = check_wwan_modem_ip();
		//g_at_chat_send(gd->chat, "AT$QCRMCALL? ", NULL, NULL, gprs, NULL); // test need to delete.
		quectel_debug("[puck] ql_data.pdp_act: %d;ql_data.rmnet_state: %d ;ret: %d",ql_data.pdp_act, ql_data.rmnet_state,ret);
		//if((ql_data.pdp_act == true) && (ql_data.rmnet_state == 0) && (ret == 1))
		// loop - 1 to handle the case 1,2,3
		if(ql_data.rmnet_state == 0){ // loop - 1
    		if((ql_data.pdp_act == true) && (ret == 1)){ // case-1
				ql_data.retry_count = 5;
		    	quectel_debug("[puck] maybe we found the issue and ql_data.rmnet_check is %d...", ql_data.rmnet_check);
				while( ql_data.retry_count > 0){
					sleep(2);
					g_at_chat_send(gd->chat, "AT+CGCONTRDP ", NULL, ql_read_modem_ip, gprs, NULL); // check modem ip
					g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);	// check wwan0 ip
					sleep(1);
					ret = check_wwan_modem_ip();
					quectel_debug("[puck] ql_data.pdp_act: %d;ql_data.rmnet_state: %d ;ret: %d",ql_data.pdp_act, ql_data.rmnet_state,ret);
	
					if((ql_data.pdp_act == true) && (ql_data.rmnet_state == 0) &&(ret == 1)){ // case 1 and case 3
						if( ql_data.rmnet_check==1){
							quectel_debug("[puck] case-3");	
							ql_data.retry_count--;
						}
						if(ql_data.rmnet_check==0){
							quectel_debug("[puck] case-1");	
							ql_data.retry_count--;
						}
						quectel_debug("[puck] retry_count %d",ql_data.retry_count);
					}
					else{
						quectel_debug("[puck] maybe fixed by ofono and gsmsrv...");
						break;
					}
				}
				if(ql_data.retry_count == 0){
					quectel_debug("[puck] case-1 retry_count: %d; need to fix",ql_data.retry_count);
					g_at_chat_send(gd->chat, "AT$QCRMCALL=1,1", NULL, ql_qcrmacall, gprs, NULL);
					sleep(3);
					if(check_wwan_modem_ip){
						quectel_debug("[puck] udhcpc -i wwan0");
						system("udhcpc -i wwan0");
						sleep(3);
						g_at_chat_send(gd->chat, "AT+CGCONTRDP ", NULL, ql_read_modem_ip, gprs, NULL); // check modem ip
						g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);	// check wwan0 ip
						quectel_debug("[puck] case-1 modem_ip:%s,wwan_ip:%s",ql_data.modem_ip, ql_data.wwan_ip);
					}
					break;
				}
			}// end case-1
			
			else if(ql_data.pdp_act == false){
				if(ql_data.rmnet_check == 1){  // case-2
					quectel_debug("[puck] case-2");	
					g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);
					g_at_chat_send(gd->chat, "AT$QCRMCALL? ", NULL, NULL, gprs, NULL);
					quectel_debug("[puck] before ql_data.rmnet_state: %d",ql_data.rmnet_state);

					g_at_chat_send(gd->chat, "AT$QCRMCALL=0,1", NULL, ql_qcrmacall, gprs, NULL);

					g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);
					g_at_chat_send(gd->chat, "AT$QCRMCALL? ", NULL, NULL, gprs, NULL);
					quectel_debug("[puck] after ql_data.rmnet_state: %d",ql_data.rmnet_state);
					ql_data.rmnet_check = 0;
				}
				else{
					quectel_debug("[puck] no case 1 2 4....");	
					break;
				}
				break;
			}//end case-2
		}

		// loop - 2 to handle case4
		else if(((ql_data.pdp_act == true) && (ql_data.rmnet_state == 1)&& (ret == 1))) {
			ql_data.retry_count = 5;
			quectel_debug("[puck] loop-2,case-4 ql_data.pdp_act: %d;ql_data.rmnet_state: %d ;ret: %d,",ql_data.pdp_act, ql_data.rmnet_state,ret);
			while(ql_data.retry_count > 0){
				sleep(2);
				g_at_chat_send(gd->chat, "AT+CGCONTRDP ", NULL, ql_read_modem_ip, gprs, NULL); // check modem ip
				g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);	// check wwan0 ip
				sleep(1);
				ret = check_wwan_modem_ip();
				quectel_debug("[puck] ql_data.pdp_act: %d;ql_data.rmnet_state: %d ;ret: %d",ql_data.pdp_act, ql_data.rmnet_state,ret);
				quectel_debug("[puck] case-4  retry_count: %d;ql_data.rmnet_check: %d ", ql_data.retry_count ,ql_data.rmnet_check);
				
				if((ql_data.pdp_act == true) && (ql_data.rmnet_state == 1) &&(ret == 1)){ // case 1 and case 3
					quectel_debug("[puck] we have the case-4 need to fix");
					ql_data.retry_count--;
				}
				else{
					quectel_debug("[puck] maybe case-4 fixed by ofono and gsmsrv...");
					break;
				}
				quectel_debug("[puck] retry_count %d",ql_data.retry_count);
			}
			if(ql_data.retry_count == 0){
				quectel_debug("[puck] case-4 retry_count: %d; need to fix",ql_data.retry_count);
				if(check_wwan_modem_ip){
					quectel_debug("[puck] udhcpc -i wwan0");
					system("udhcpc -i wwan0");
					sleep(3);
					g_at_chat_send(gd->chat, "AT+CGCONTRDP ", NULL, ql_read_modem_ip, gprs, NULL); // check modem ip
					g_at_chat_send(gd->chat, "AT+QNETDEVSTATUS? ", NULL, ql_read_wwan_ip, gprs, NULL);
					check_wwan_modem_ip(); // update the wwan_ip
					quectel_debug("[puck] case-4 modem_ip:%s,wwan_ip:%s",ql_data.modem_ip, ql_data.wwan_ip);
				}
			}
		}
		sleep(60);
	}
}


bool hasData(const char *str) {
    return str != NULL && str[0] != '\0';
}

char* read_wwan_operstate(const char* filename) {
    FILE* file = fopen(filename, "r");
    if (!file) {
        perror("Error opening file");
        exit(EXIT_FAILURE);
    }

    char* buffer = (char*)malloc(10 * sizeof(char));
    if (!buffer) {
        perror("Memory allocation failed");
        exit(EXIT_FAILURE);
    }

    fgets(buffer, 10, file);

    fclose(file);

    return buffer;
}

void rmnet_fix()
{
	struct ofono_gprs_context *gc;
	struct gprs_data *gd;
	quectel_debug("rmnet_state :%d",ql_data.rmnet_state);
	
	//check wwan0(0,1,2) 
	if(ql_data.rmnet_state){
		if(ql_data.rmnet_state==2){
			quectel_debug("rmnet works fine do nothing...modem_ip:%s,wwan_ip:%s",ql_data.modem_ip, ql_data.wwan_ip);
			check_wwan_modem_ip();
		}
		if(ql_data.rmnet_state == 1){
			quectel_debug("rmnet ready...need udhcpc -i wwan0");
			check_wwan_modem_ip();
			//system("udhcpc -i wwan0");
		}
	}
	else{ // rmnet_state = 0
		quectel_debug("rmnet need to fix");
		// check modem ip
		if(hasData(ql_data.modem_ip)){ // modem ip good
			quectel_debug("hasData modem_ip :%s and need to AT$QCRMCALL=1,1",ql_data.modem_ip);
			g_at_chat_send(gd->chat, "AT$QCRMCALL=1,1", none_prefix, NULL, NULL, NULL);
			//check wwan0 ip and modem ip, 0--same
			check_wwan_modem_ip();
			// if(strcmp(ql_data.wwan_ip, ql_data.modem_ip)){
			// 	//g_at_chat_send(gd->chat, "AT$QCRMCALL=1,1", none_prefix, NULL, NULL, NULL);
			// 	quectel_debug("wwan_ip modem_ip not same need udhcpc -i wwan0");
			// 	//system("udhcpc -i wwan0");
			// }
		}
		else{
			// no modem_ip and wwan_ip, so let ofono to fix first
			if(ql_data.no_ip_count == 1){
				quectel_debug("Warning: No modem_ip and wwan_ip for the second time! and reset no_ip_count %d",ql_data.no_ip_count);
				ql_data.no_ip_count=0;
				quectel_debug("Warning: No modem_ip and wwan_ip for the second time! and reset no_ip_count %d",ql_data.no_ip_count);
			}
			else{
				(ql_data.no_ip_count)++;
				quectel_debug("try to wait 20s, no_ip_count %d",ql_data.no_ip_count);
				usleep(20000000);
			}
		}
	}
}

static int ql_compare_ips(const char* ip_address1, const char* ip_address2) {
	quectel_debug("");
	quectel_debug("wwan0 IP address: %s\n", ip_address1);
    quectel_debug("modem IP address: %s\n", ip_address2);
    return strcmp(ip_address1, ip_address2);
}

static int ql_set_ip_address(const char* interface_name, const char* ip_address) {
    quectel_debug("");
	char command[64];
    sprintf(command, "ifconfig %s %s", interface_name, ip_address);
    return system(command);
}

static void ql_get_ip_address(const char* interface_name, char* ip_address) {
    struct ifaddrs *ifaddr, *ifa;

    if (getifaddrs(&ifaddr) == -1) {
        perror("getifaddrs");
        return;
    }

    for (ifa = ifaddr; ifa != NULL; ifa = ifa->ifa_next) {
        if (ifa->ifa_addr == NULL) continue;

        if (strcmp(ifa->ifa_name, ql_data.ifname) == 0 && ifa->ifa_addr->sa_family == AF_INET) {
            struct sockaddr_in *addr = (struct sockaddr_in *)ifa->ifa_addr;
            strncpy(ip_address, inet_ntoa(addr->sin_addr), INET_ADDRSTRLEN - 1);
            ip_address[INET_ADDRSTRLEN - 1] = '\0'; // Ensure null-termination
            break;
        }
    }
	quectel_debug("ip_address %s, wwan_ip %s, modem_ip %s", ip_address, ql_data.wwan_ip, ql_data.modem_ip);
    freeifaddrs(ifaddr);
}

static int check_wwan_modem_ip(){
	ql_get_ip_address(ql_data.ifname, ql_data.wwan_ip);
	if(ql_compare_ips(ql_data.wwan_ip, ql_data.modem_ip))
	{
		quectel_debug("wwan_ip and modem_ip are not same");
		return 1;
		//ql_set_ip_address(ql_data.ifname, ql_data.modem_ip);
	}
	else{
		quectel_debug("wwan_ip and modem_ip are the same");
		return 0;
	}
}

static void ql_parse_modem_info(char *raw_data, char *modem_ip) {
    if (raw_data == NULL) {
		memset(ql_data.modem_ip, 0, sizeof(ql_data.modem_ip));
		ql_data.pdp_act = false;
        DBG(" parse_modem_info raw data Null, ql_data.pdp_act: %d\n",ql_data.pdp_act);
		return;
    }

    char *token;
    char *saveptr;
    const char delimiters[] = ",\r\n";
    int i = 0;

    token = strtok_r((char *)raw_data, delimiters, &saveptr);

    while (token != NULL && i < 8) {
        switch (i) {
            case 3:
                strcpy(ql_data.modem_ip, token);
				ql_data.pdp_act = true;
                quectel_debug("modem_ip: %s; ql_data.pdp_act: %d\n", ql_data.modem_ip, ql_data.pdp_act);
                break;
            default:
                break;
        }
        token = strtok_r(NULL, delimiters, &saveptr);
        i++;
    }
}

static void ql_parse_qnetdevstatus_check(const char *raw_data, int *status) {
	
    if (raw_data == NULL) {
        quectel_debug("parse_qnetdevstatus: raw data is NULL\n");
        return;
    }

    // Find the position of ':'
    const char *colon_pos = strchr(raw_data, ':');
    if (colon_pos == NULL) {
        quectel_debug("parse_qnetdevstatus: colon not found in raw data");
        return;
    }

    // Move to the character after ':'
    const char *data_start = colon_pos + 1;

    // Tokenize the data after ':' using comma as delimiter
    char *token = strtok((char *)data_start, ",");
    if (token == NULL) {
        quectel_debug("parse_qnetdevstatus: no data found after colon");
        return;
    }

    // Find the second token
    token = strtok(NULL, ",");
    if (token == NULL) {
		ql_data.rmnet_state = 0;
        quectel_debug("parse_qnetdevstatus: insufficient data after colon rmnet_state %d",status);
        return;
    }

    // Convert the second token to integer
    status = atoi(token);

    // Print the state if it is within the specified range
    if (status >= 0 && status <= 2) {
		ql_data.rmnet_state = status;
        quectel_debug("rmnet_state: %d; status : %d", ql_data.rmnet_state,status);
    } else {
        quectel_debug("parse_qnetdevstatus: unable to parse state");
    }
}

static void ql_qcrmacall(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	const char *apn = NULL;
	GAtResultIter iter;
	quectel_debug("");
	const char *raw_data;
	DBG("ql_qcrmacall ok %d", ok);

	g_at_result_iter_init(&iter, result);

	for (int i = 0; i < g_at_result_num_response_lines(result); i++)
		g_at_result_iter_next(&iter, NULL);
		raw_data = g_at_result_iter_raw_line(&iter);
	quectel_debug("[puck] ql_qcrmacall: %s", raw_data);
}

static void ql_read_modem_ip(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	const char *apn = NULL;
	GAtResultIter iter;
	quectel_debug("");
	const char *raw_data;
	//DBG("ok %d", ok);

	g_at_result_iter_init(&iter, result);

	for (int i = 0; i < g_at_result_num_response_lines(result); i++)
		g_at_result_iter_next(&iter, NULL);
		raw_data = g_at_result_iter_raw_line(&iter);

	quectel_debug(" read_modem_ip raw_data: %s", raw_data);

	ql_parse_modem_info(raw_data, ql_data.modem_ip);
}

//AT+QNETDEVSTATUS?
static void ql_read_wwan_ip(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	const char *apn = NULL;
	GAtResultIter iter;
	int numlines = g_at_result_num_response_lines(result);
	const char *line;
	int num1, num2, num3, num4;
	const char *str;
	quectel_debug("");
	const char *raw_data;
	DBG("ok %d", ok);

	g_at_result_iter_init(&iter, result);
	
	for (int i = 0; i < g_at_result_num_response_lines(result); i++)
		g_at_result_iter_next(&iter, NULL);
		raw_data = g_at_result_iter_raw_line(&iter);

	ql_parse_qnetdevstatus_check(raw_data, ql_data.rmnet_state);
}

//end

static void at_cgdcont_read_cb(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	int activated_cid = gd->last_auto_context_id;
	const char *apn = NULL;
	GAtResultIter iter;

	DBG("ok %d", ok);

	if (!ok) {
		ofono_warn("Can't read CGDCONT contexts.");
		return;
	}

	g_at_result_iter_init(&iter, result);

	while (g_at_result_iter_next(&iter, "+CGDCONT:")) {
		int read_cid;

		if (!g_at_result_iter_next_number(&iter, &read_cid))
			break;

		if (read_cid != activated_cid)
			continue;

		/* ignore protocol */
		g_at_result_iter_skip_next(&iter);

		g_at_result_iter_next_string(&iter, &apn);

		break;
	}

	if (apn && *apn) {
		//Make apn lowercase due to bug in ofonos apn match
		// where ofono do not ignore case

		char *lower_apn = (char *)g_utf8_strdown(apn, -1);
		ofono_gprs_cid_activated(gprs, activated_cid, lower_apn);
		g_free(lower_apn);
	} else {
		ofono_warn("cid %u: Received activated but no apn present",
				activated_cid);
	}
}

static void cgreg_notify(GAtResult *result, gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	int status;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);

	DBG("");

	if (at_util_parse_reg_unsolicited(result, "+CGREG:", &status,
				NULL, NULL, NULL, gd->vendor) == FALSE)
		return;

	ofono_gprs_status_notify(gprs, status);
}

static int parse_number(const char *event)
{
	size_t end = 0;
	int num = 0;

	//Search for first number
	while(end < strlen(event)){
		if(event[end] >= '0' && event[end] <= '9')
			break;
		end++;
	}
	//Parse number (stolen from gatchat/result.c)
	while (event[end] >= '0' && event[end] <= '9') {
		num = num * 10 + (int)(event[end] - '0');
		end += 1;
	}

	return num;
}

static void cgev_notify(GAtResult *result, gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	GAtResultIter iter;
	const char *event;

	DBG("");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+CGEV:"))
		return;

	if (!g_at_result_iter_next_unquoted_string(&iter, &event))
		return;

	if (g_str_equal(event, "NW DETACH") ||
			g_str_equal(event, "ME DETACH")) {
		gd->attached = FALSE;
		ofono_gprs_detached_notify(gprs);
		return;
	} else if (g_str_has_prefix(event, "PDN ACT")) {
		// Quectels format doesn't have a space before the CID, so
		// we can't use sscanf...
		gd->last_auto_context_id = parse_number(event);
		DBG("last_auto_context_id = %d", gd->last_auto_context_id);

		g_at_chat_send(gd->chat, "AT+CGDCONT?", cgdcont_prefix,
				at_cgdcont_read_cb, gprs, NULL);

		// if (!ql_data.thread1_created) {
		// 	pthread_t tid1;
		// 	pthread_create(&tid1, NULL, ql_thread1_function, gprs);
		// 	ql_data.thread1_created = true;
    	// }

	} else if (g_str_has_prefix(event, "PDN DEACT")) {
		int context_id = parse_number(event);
		/* Indicate that this cid is not activated anymore */
		if (gd->last_auto_context_id == context_id)
			gd->last_auto_context_id = -1;
	}
}

static void cereg_notify(GAtResult *result, gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	int stat = 0;
	GAtResultIter iter;
	const char *event;

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+CEREG:"))
		return;

	if (!g_at_result_iter_next_number(&iter, &stat))
		return;

	if (stat != 1 && stat != 5)
		return;

	// We can't get the CID from this, so have to assume CID 1
	gd->last_auto_context_id = 1;

	g_at_chat_send(gd->chat, "AT+CGDCONT?", cgdcont_prefix,
			at_cgdcont_read_cb, gprs, NULL);
}

static void qnetdevstatus_notify(GAtResult *result, gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	int stat = 0;
	GAtResultIter iter;
	const char *event;

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QNETDEVSTATUS:"))
		return;

	if (!g_at_result_iter_next_number(&iter, &stat))
		return;

	if (!g_at_result_iter_next_number(&iter, &stat))
		return;
	
	if (stat==0){
		quectel_debug("[puck] stat: %d, Enable RmNet device status URC", stat);
	}
	else if (stat==1){
	    quectel_debug("[puck] stat: %d, A RmNet call is ready and MCU can get IP addresses by DHCP or QMI", stat);
	}
	else if (stat==2)
	{
		quectel_debug("[puck] stat: %d, A rmnet call is connected", stat);

		if (!ql_data.thread1_created) {
			pthread_t tid1;
			if(pthread_create(&tid1, NULL, ql_thread1_function, gprs)){
				quectel_debug("[puck] ql_thread1 failed");
				ql_data.thread1_created = false;
				return;
			}
			ql_data.thread1_created = true;
			quectel_debug("[puck] ql_data.thread1_created :%d", ql_data.thread1_created);
    	}
	}
}

static void gprs_initialized(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);

	DBG("");

	g_at_chat_register(gd->chat, "+CEREG:", cereg_notify, FALSE, gprs, NULL);
	g_at_chat_register(gd->chat, "+CGEV:", cgev_notify, FALSE, gprs, NULL);
	g_at_chat_register(gd->chat, "+CGREG:", cgreg_notify, FALSE, gprs, NULL);
	g_at_chat_register(gd->chat, "+QNETDEVSTATUS:", qnetdevstatus_notify, FALSE, gprs, NULL);

	ofono_gprs_register(gprs);
}

static void at_cgreg_test_cb(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	gint range[2];
	GAtResultIter iter;
	int cgreg1 = 0;
	int cgreg2 = 0;
	const char *cmd;

	DBG("");

	if (!ok)
		goto error;

	g_at_result_iter_init(&iter, result);

retry:
	if (!g_at_result_iter_next(&iter, "+CGREG:"))
		goto error;

	if (!g_at_result_iter_open_list(&iter))
		goto retry;

	while (g_at_result_iter_next_range(&iter, &range[0], &range[1])) {
		if (1 >= range[0] && 1 <= range[1])
			cgreg1 = 1;
		if (2 >= range[0] && 2 <= range[1])
			cgreg2 = 1;
	}

	g_at_result_iter_close_list(&iter);

	if (cgreg2)
		cmd = "AT+CGREG=2";
	else if (cgreg1)
		cmd = "AT+CGREG=1";
	else
		goto error;

	g_at_chat_send(gd->chat, cmd, none_prefix, NULL, NULL, NULL);

	g_at_chat_send(gd->chat, "AT+CGEREP=2,1", none_prefix,
		gprs_initialized, gprs, NULL);

	return;

error:
	ofono_info("GPRS not supported on this device");
	ofono_gprs_remove(gprs);
}

static void at_cgdcont_test_cb(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);
	GAtResultIter iter;
	int min, max;
	const char *pdp_type;
	gboolean found = FALSE;

	DBG("");

	if (!ok)
		goto error;

	g_at_result_iter_init(&iter, result);

	while (!found && g_at_result_iter_next(&iter, "+CGDCONT:")) {
		gboolean in_list = FALSE;

		if (!g_at_result_iter_open_list(&iter))
			continue;

		if (g_at_result_iter_next_range(&iter, &min, &max) == FALSE)
			continue;

		if (!g_at_result_iter_skip_next(&iter))
			continue;

		if (g_at_result_iter_open_list(&iter))
			in_list = TRUE;

		if (!g_at_result_iter_next_string(&iter, &pdp_type))
			continue;

		if (in_list && !g_at_result_iter_close_list(&iter))
			continue;

		/* We look for IP PDPs */
		if (g_str_equal(pdp_type, "IP"))
			found = TRUE;
	}

	if (found == FALSE)
		goto error;

	ofono_gprs_set_cid_range(gprs, min, max);

	g_at_chat_send(gd->chat, "AT+CGREG=?", cgreg_prefix,
			at_cgreg_test_cb, gprs, NULL);

	return;

error:
	ofono_info("GPRS not supported on this device");
	ofono_gprs_remove(gprs);
}

static int at_gprs_probe(struct ofono_gprs *gprs,
					unsigned int vendor, void *data)
{
	GAtChat *chat = data;
	struct gprs_data *gd;

	DBG("");

	gd = g_try_new0(struct gprs_data, 1);
	if (gd == NULL)
		return -ENOMEM;

	gd->chat = g_at_chat_clone(chat);
	gd->vendor = vendor;
	gd->last_auto_context_id = -1;

	ofono_gprs_set_data(gprs, gd);

	g_at_chat_send(gd->chat, "AT+CGDCONT=?", cgdcont_prefix,
			at_cgdcont_test_cb, gprs, NULL);

	return 0;
}

static void at_gprs_remove(struct ofono_gprs *gprs)
{
	struct gprs_data *gd = ofono_gprs_get_data(gprs);

	ofono_gprs_set_data(gprs, NULL);

	g_at_chat_unref(gd->chat);
	g_free(gd);
}

static const struct ofono_gprs_driver driver = {
	.name			= "veriquecmodem",
	.probe			= at_gprs_probe,
	.remove			= at_gprs_remove,
	.set_attached		= at_gprs_set_attached,
	.attached_status	= at_gprs_registration_status,
};

void veriquec_gprs_init(void)
{
	DBG("");
	ofono_gprs_driver_register(&driver);
}

void veriquec_gprs_exit(void)
{
	ofono_gprs_driver_unregister(&driver);
}
