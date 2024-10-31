/*
 *
 *  oFono - Open Source Telephony
 *
 *  Copyright (C) 2017 Vincent Cesson. All rights reserved.
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

#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <sys/time.h>
#include <time.h>
#include <math.h>

#include <glib.h>
#include <gatchat.h>
#include <gattty.h>
#include <gdbus.h>
#include <assert.h>

#include "ofono.h"

#define OFONO_API_SUBJECT_TO_CHANGE
#include <ofono/dbus.h>
#include <ofono/plugin.h>
#include <ofono/log.h>
#include <ofono/modem.h>
#include <ofono/devinfo.h>
#include <ofono/netreg.h>
#include <ofono/phonebook.h>
#include <ofono/sim.h>
#include <ofono/sms.h>
#include <ofono/gprs.h>
#include <ofono/gprs-context.h>
#include <ofono/location-reporting.h>
#include <drivers/qmimodem/qmi.h>
#include <asm/ioctls.h>
#include <linux/serial.h>
#include <termios.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <unistd.h>
#include <sys/wait.h>
#include <poll.h>
#include <drivers/atmodem/atutil.h>
#include <drivers/atmodem/vendor.h>
#include <drivers/common/verisure/errorhandling.h>

#define VENDOR_INFO_INTERFACE OFONO_SERVICE ".verisure.VendorInfo"
#define RSSISCAN_INTERFACE OFONO_SERVICE ".verisure.RssiScan"
#define AT_CHANNEL_INTERFACE OFONO_SERVICE ".verisure.AtChannel"
#define DEBUG_LOGGING OFONO_SERVICE ".verisure.DebugLog"
#define SIM_REFRESH_INTERFACE OFONO_SERVICE ".verisure.SimRefresh"
#define JAM_DETECTION_INTERFACE OFONO_SERVICE ".verisure.JamDetection"
#define RPM_MANAGER_INTERFACE OFONO_SERVICE ".verisure.RadioPolicyManager"
#define IMS_MANAGER_INTERFACE OFONO_SERVICE ".verisure.ImsManager"
#define NETWORK_REGISTRATION OFONO_SERVICE  ".NetworkRegistration"
#define VERISURE_ERROR_INTERFACE OFONO_SERVICE ".verisure.Error"
#define IMS_MBN_SELECT_CMD "AT+QMBNCFG=\"Select\","
#define IMS_MBN_DEACTIVATE_CMD "AT+QMBNCFG=\"Deactivate\""

//VoLTE service availability
#define VOLTE_AVAILABLE 2 //2: Available

//IMS registration status
#define IMS_REGISTERED 2 // 2: Registered

//IMS functionality status
#define IMS_ENABLED 1 // 1: enabled

#define MCC_LEN 3
#define MNC_MIN_LEN 2
#define MNC_MAX_LEN 3
#define INVALID_MCC "FFF"
#define INVALID_MNC "FFF"

#define CIEV_LSTA_INDICATOR_VALUE_GSM_IDLE_DRX (0)
#define CIEV_LSTA_INDICATOR_VALUE_GSM_SCAN     (1)
#define CIEV_LSTA_INDICATOR_VALUE_GSM_VOICE    (2)
#define CIEV_LSTA_INDICATOR_VALUE_WCDMA_DRX    (10)
#define CIEV_LSTA_INDICATOR_VALUE_WCDMA_SCAN   (11)
#define CIEV_LSTA_INDICATOR_VALUE_LTE_DRX      (20)
#define CIEV_LSTA_INDICATOR_VALUE_LTE_SCAN     (21)
#define DATE_MAXLEN                            (17) // Length of the string "yy/mm/dd,hh:mm:ss"

//Configuration value to be sent in "AT+QAPRDYIND", to receive "+APIND:QMI READY"
#define CFG_VAL_QMI_READY (8)

static const char *none_prefix[] = { NULL };
static const char *cops_prefix[] = { "+COPS:", NULL };
static const char *qnwinfo_prefix[] = { "+QNWINFO:", NULL };
static const char *crsm_prefix[] = { "+CRSM:", NULL };
static const char *qaprdyind_prefix[] = { "+QAPRDYIND:", NULL };
static const char *qdai_prefix[] = { "+QDAI:", NULL };
static const char *qnvfr_prefix[] = { "+QNVFR:", NULL };
static const char *qlts_prefix[] = { "+QLTS:", NULL };
static const char *qcfg_prefix[] = { "+QCFG:", NULL };
static const char *qpdptrycfg_prefix[] = { "+QPDPTRYCFG:", NULL };
static const char *qpdptrychk_prefix[] = { "+QPDPTRYCHK:", NULL };
static const char *qimscfg_prefix[] = { "+QIMSCFG:", NULL };


static char date_str[DATE_MAXLEN + 1] = "";
static const char *ok_str = "OK";
static const char *err_str = "ERROR";
static char operator_tmp[7];

static int f1_cfg_counter_setting,f2_cfg_counter_setting,f3_cfg_counter_setting,f4_cfg_counter_setting;
static int f1_cfg_time_duration_setting,f2_cfg_time_duration_setting,f3_cfg_time_duration_setting,f4_cfg_time_duration_setting;

static bool print_modem_log = false;
static bool b_apind_qmi_ready_received = false;

struct veriquec_rpm_manager {
	DBusMessage *msg;
	guint notify_id;
};

struct veriquec_modem_info {
	DBusMessage *msg;
	char *path;
};

struct veriquec_rssi_scan {
	DBusMessage *msg;
	DBusMessage *setup_msg;
	DBusMessage *reply_setup;
	uint32_t cid;
	uint32_t lac;
};

struct veriquec_at_channel {
	int channels;
	DBusMessage *msg;
};

typedef struct {
	int current_rssi;
} ciev_gsm_drx_t;

typedef struct {
	int rscp;
	int noise;
	double ecno;
} ciev_wcdma_drx_t;

typedef struct {
	int rsrp;
	double rsrq;
	int rssi;
} ciev_lte_drx_t;

typedef union {
	ciev_gsm_drx_t gsm;
	ciev_wcdma_drx_t wcdma;
	ciev_lte_drx_t lte;
} ciev_rat_drx_t;

typedef struct {
	unsigned int counter;
	ciev_rat_drx_t rat;
} ciev_drx_t;

typedef struct {
	int min;
	int max;
	int mean;
	unsigned int variance_or_grade;
} ciev_rssi_distribution_t;

typedef struct {
	unsigned int reported_channel_count;
	unsigned int scanned_channel_count;
	unsigned int start_arfcn;
	unsigned int end_arfcn;
	ciev_rssi_distribution_t rssi_distribution;
} ciev_scan_t;

typedef union {
	ciev_drx_t drx;
	ciev_scan_t scan;
} ciev_lsta_t;

typedef struct {
	unsigned int indicator_value;
	ciev_lsta_t lsta;
} ciev_t;

struct veriquec_ceer_info {
	guint ceer_app_ciev_notify_id;
	guint ceer_mdm_ciev_notify_id;
	int last_cause_group;
	int last_cause;
	time_t last_action_time;
};
#define CEER_INFO_SLEEP_SECONDS 2

struct veriquec_sim_refresh {
	DBusMessage *msg;
};

struct veriquec_jam_detection {
	DBusMessage *msg;
	const char *path;
	gboolean enabled;
	guint notify_id;
};

typedef struct {
    char plmn_id[7];
    char *mbn_name;
    gboolean mbn_available;
    gboolean volte_support;
    gboolean sms_over_ims_support;
} imsOperatorList_t;

// Populate IMS Operator List //To be removed after Req ID.2 - Operator whitelist implementation
#define MAX_ROW_IMS_OPERATOR_LIST 9
imsOperatorList_t imsOperatorList[] = {
	{"21403" ,"ROW_Generic_3GPP", true, true, false},
	{"21409" ,"ROW_Generic_3GPP", true, true, false},
	{"21421" ,"ROW_Generic_3GPP", true, true, false},
	{"24002" ,"ROW_Generic_3GPP", true, true, false},  //this has been included for testing purpose only
	{"24002" ,"ROW_Generic_3GPP", true, true, false},  //this has been included for testing purpose only (3)
	{"24007" ,"ROW_Generic_3GPP", true, true, false},  //this has been included for testing purpose only (Comviq)
	{"24008" ,"ROW_Generic_3GPP", true, true, false},  //this has been included for testing purpose only (Telenor)
	{"21401" ,"UK_Vodafone_IoT", true, true, false},
	{"21406" ,"UK_Vodafone_IoT", true, true, false},
	{"21437" ,"UK_Vodafone_IoT", true, true, false}
};

typedef enum {
	IMS_REQ_ENABLE,
	IMS_REQ_DISABLE,
	IMS_REQ_INVALID,
} ims_request;

struct veriquec_ims_data {
	DBusMessage *msg;
	ims_request ims_request;
	gboolean ims_enabled;  //true - ims enabled, false - ims not enabled
	gboolean ims_registered;  //true - ims registered, false - ims not registered
    gboolean volte_available;  //true - volte available, false - volte not available
	const char *path;
	const char *operator;
};

typedef enum {
	STATUS_REGISTERED,
	STATUS_DEREGISTERED,
	STATUS_INVALID,
} netreg_status;

typedef struct {
	char  plmn_mcc[MCC_LEN + 1];
	char  plmn_mnc[MNC_MAX_LEN + 1];
	netreg_status status;
} veriquec_netreg_data;

static veriquec_netreg_data __cached_netreg_data;

struct veriquec_data {
	GAtChat *app;
	GAtChat *mdm;
	struct qmi_device *qmid;
	struct ofono_sim *sim;
	gboolean have_sim;
	gboolean interface_registered;
	gboolean qmi_ready;
	gboolean post_sim;
	struct ofono_gprs *gprs;
	struct at_util_sim_state_query *sim_state_query;
	struct veriquec_rpm_manager *rpm_mgr;
	struct veriquec_modem_info *info;
	struct veriquec_rssi_scan *rssi_scan;
	struct veriquec_at_channel *at_channel;
	struct veriquec_sim_refresh *sim_refresh;
	struct veriquec_jam_detection *jam_detection;
	struct veriquec_ceer_info *ceer_info;
	struct verisure_error *error;
	struct veriquec_ims_data *ims_data;
	guint 	 netreg_watch;
	veriquec_netreg_data netreg_data;
};

static void reset_netreg_data(veriquec_netreg_data* data)
{
	DBG("");

	strncpy(data->plmn_mcc, INVALID_MCC, MCC_LEN);
	strncpy(data->plmn_mnc, INVALID_MNC, MNC_MAX_LEN);
	data->status = STATUS_INVALID;
}

static int veriquec_probe(struct ofono_modem *modem)
{
	struct veriquec_data *data;

	data = g_try_new0(struct veriquec_data, 1);
	if (data == NULL)
		return -ENOMEM;

	ofono_modem_set_data(modem, data);

	return 0;
}

static void veriquec_unregister(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("%p", modem);

	g_at_chat_cancel_all(data->app);
	g_at_chat_unregister_all(data->app);

	if (g_dbus_unregister_interface(conn, path, VENDOR_INFO_INTERFACE)) {
		ofono_modem_remove_interface(modem, VENDOR_INFO_INTERFACE);
	}

	if (g_dbus_unregister_interface(conn, path, RSSISCAN_INTERFACE)) {
		ofono_modem_remove_interface(modem, RSSISCAN_INTERFACE);
	}

	if (g_dbus_unregister_interface(conn, path, AT_CHANNEL_INTERFACE)) {
		ofono_modem_remove_interface(modem, AT_CHANNEL_INTERFACE);
	}

	if (g_dbus_unregister_interface(conn, path, DEBUG_LOGGING)) {
		ofono_modem_remove_interface(modem, DEBUG_LOGGING);
	}

	if (g_dbus_unregister_interface(conn, path, SIM_REFRESH_INTERFACE)) {
		ofono_modem_remove_interface(modem, SIM_REFRESH_INTERFACE);
	}

	if (g_dbus_unregister_interface(conn, path, JAM_DETECTION_INTERFACE)) {
		ofono_modem_remove_interface(modem, JAM_DETECTION_INTERFACE);
	}

	if (g_dbus_unregister_interface(conn, path, RPM_MANAGER_INTERFACE)) {
		ofono_modem_remove_interface(modem, RPM_MANAGER_INTERFACE);
	}

	if (g_dbus_unregister_interface(conn, path, IMS_MANAGER_INTERFACE)) {
		ofono_modem_remove_interface(modem, IMS_MANAGER_INTERFACE);
	}

	data->interface_registered = FALSE;
}

static void veriquec_remove(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);

	DBG("%p", modem);

	if ((data != NULL) && data->interface_registered) {
		veriquec_unregister(modem);
	}

	/* Cleanup potential SIM state polling */
	at_util_sim_state_query_free(data->sim_state_query);
	ofono_modem_set_data(modem, NULL);

	if (data)
		g_free(data);
}

static void veriquec_debug_log_to_file(const char *prefix, const char *at_log_string)
{
	FILE *modemlog = NULL;
	char timestamp_buf[32] = {0};
	struct tm *tm_info;
	struct timeval tv;
	int ms;

	gettimeofday(&tv, NULL);

	ms = tv.tv_usec / 1000;

	tm_info = localtime(&tv.tv_sec);

	strftime(timestamp_buf, sizeof(timestamp_buf) - 1, "%b %d %H:%M:%S", tm_info);

	modemlog = fopen("/var/log/veriquec.log", "a");
	if (modemlog == NULL) {
		DBG("Failed to open veriquec modem log file: %s", strerror(errno));
	}
	else {
		fprintf(modemlog, "%s.%03d | %s %s\n", timestamp_buf, ms, prefix, at_log_string);
		fclose(modemlog);
	}
}

static void veriquec_debug(const char *str, void *user_data)
{
	const char *prefix = user_data;

	/* Always log to file */
	veriquec_debug_log_to_file(prefix, str);

	if (print_modem_log) {
		ofono_info("%s%s", prefix, str);
 	}
}

static void veriquec_qmi_debug(const char *str, void *user_data)
{
	const char *prefix = user_data;

	if (getenv("OFONO_QMI_DEBUG"))
		ofono_info("%s%s", prefix, str);
}

static GAtChat *open_device(const char *device, char *device_debug_name)
{
	GAtSyntax *syntax;
	GIOChannel *channel;
	GAtChat *chat;
	GHashTable *options;

	DBG("Opening device %s", device);

	options = g_hash_table_new(g_str_hash, g_str_equal);
	if (options == NULL)
		return NULL;
	/*
	 * The modem does not answer when the "Baud" attibute is missing
	 * The supplied value is not making any change. But the "Baud"
	 * paramenter is needed.
	 */
	g_hash_table_insert(options, "Baud", "115200");

	channel = g_at_tty_open(device, options);
	g_hash_table_destroy(options);
	if (channel == NULL)
		return NULL;


	syntax = g_at_syntax_new_gsm_permissive();
	chat = g_at_chat_new(channel, syntax);
	g_at_syntax_unref(syntax);
	g_io_channel_unref(channel);

	if (chat == NULL)
		return NULL;

	if (getenv("OFONO_AT_DEBUG"))
		g_at_chat_set_debug(chat, veriquec_debug, device_debug_name);

	return chat;
}

static void sim_state_cb(gboolean present, gpointer user_data)
{
	struct ofono_modem *modem = user_data;
	struct veriquec_data *data = ofono_modem_get_data(modem);

	at_util_sim_state_query_free(data->sim_state_query);
	data->sim_state_query = NULL;

	data->have_sim = present;
	ofono_modem_set_powered(modem, TRUE);
}

static void sim_detect_cb(GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;

	DBG("");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QSIMSTAT:"))
		return;

	// Skip enable status
	g_at_result_iter_skip_next(&iter);

	// TODO Can this notification send unknown(2) or not?
	if (!g_at_result_iter_next_number(&iter, &data->have_sim))
		return;

	DBG("Have SIM: %d", data->have_sim);

	ofono_sim_inserted_notify(data->sim, data->have_sim);
}

static void sim_detect_enable_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

	g_at_chat_register(data->mdm, "+QSIMSTAT:", sim_detect_cb, FALSE, data, NULL);
}

static void ims_reg_status_cb(GAtResult *result, gpointer user_data)
{
    DBusConnection *conn = ofono_dbus_get_connection();
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
    gboolean curr_ims_registration_status = false;

	DBG("");

	/* Sample URCs:
		+QIMSREGSTAT: 0  // Not Registered
		+QIMSREGSTAT: 1  // Registering
		+QIMSREGSTAT: 2  // Registered
	*/
	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QIMSREGSTAT:"))
		return;

	gint ims_reg_status;
	if (!g_at_result_iter_next_number(&iter, &ims_reg_status))
		return;

	DBG("IMS reg Status: %d", ims_reg_status);

    curr_ims_registration_status = (IMS_REGISTERED == ims_reg_status) ? 1 : 0;

    if (data->ims_data->ims_registered != curr_ims_registration_status)
    {
        data->ims_data->ims_registered = curr_ims_registration_status;

        // Send property changed
        ofono_dbus_signal_property_changed(conn, data->ims_data->path, IMS_MANAGER_INTERFACE, "ImsRegistered", DBUS_TYPE_BOOLEAN, &curr_ims_registration_status);
    }
}

static void ims_srv_status_cb(GAtResult *result, gpointer user_data)
{
    DBusConnection *conn = ofono_dbus_get_connection();
	struct veriquec_data *data = user_data;
	GAtResultIter iter;

	DBG("");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QIMSSRVSTAT:"))
		return;

	/* Brief: +QIMSSRVSTAT: <sms_service_status>, <volte_service_status>, <ut_service_status>,
		status: 0 - unavailable, 1 - limited service, 2 - available
	   Sample URCs:
		+QIMSSRVSTAT: 0,0,2
		+QIMSSRVSTAT: 0,2,2
		+QIMSSRVSTAT: 2,2,2
	*/

	// Skip sms service status
	g_at_result_iter_skip_next(&iter);

	gint volte_srv_status;
	if (!g_at_result_iter_next_number(&iter, &volte_srv_status))
		return;

	DBG("Received URC volte status code: %d", volte_srv_status);
	gboolean curr_volte_availability_status = (VOLTE_AVAILABLE == volte_srv_status) ? 1 : 0;

	if (data->ims_data->volte_available != curr_volte_availability_status){
		data->ims_data->volte_available = curr_volte_availability_status;

        // Send property changed
        ofono_dbus_signal_property_changed(conn, data->ims_data->path, IMS_MANAGER_INTERFACE, "VolteAvailable", DBUS_TYPE_BOOLEAN, &curr_volte_availability_status);
  }
}

static void ims_reg_srv_status_urc_enable_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

    DBG("");

	if (ok){
		g_at_chat_register(data->mdm, "+QIMSREGSTAT:", ims_reg_status_cb, FALSE, data, NULL);
		g_at_chat_register(data->mdm, "+QIMSSRVSTAT:", ims_srv_status_cb, FALSE, data, NULL);
	}else{
		DBG("FW doesn't support IMS status URCs");
	}
}

static void cfun_enable(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct ofono_modem *modem = user_data;
	struct veriquec_data *data = ofono_modem_get_data(modem);

	if (!ok) {
		g_at_chat_unref(data->app);
		data->app = NULL;

		g_at_chat_unref(data->mdm);
		data->mdm = NULL;

		ofono_modem_set_powered(modem, FALSE);
		return;
	}

	// Get initial SIM state
	data->sim_state_query = at_util_sim_state_query_new(data->app,
						2, 20, sim_state_cb, modem,
						NULL);
}

static void rpm_manager_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_rpm_manager *rpm_mgr = data->rpm_mgr;

	g_at_chat_unregister(data->mdm, data->rpm_mgr->notify_id);

	g_free(rpm_mgr);
}

static void qpdptrychk_urc_cb(GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char *reject_cause;
	int enable,status;

	DBG("QPDPTRYCHK CALLBACK TRIGGERED");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QPDPTRYCHK:")) {
		return;
	}
	if (!g_at_result_iter_next_number(&iter, &enable)) {
		return;
	}
	if (!g_at_result_iter_next_string(&iter, &reject_cause)) {
		return;
	}
	if (!g_at_result_iter_next_number(&iter, &status)) {
		return;
	}

	if (status == 0) {
			DBG("RPM triggered, maximum number of PDP activations reached");
	} else {
		DBG("RPM not triggered");
	}
	DBG("Reject Cause: %s\n", reject_cause);

	if (g_strcmp0(reject_cause, "F1") == 0) {
		DBG("Maximum number of PDP activation retries reached for F1");
	}
	if (g_strcmp0(reject_cause, "F2") == 0) {
		DBG("Maximum number of PDP activation retries reached for F2");
	}
	if (g_strcmp0(reject_cause, "F3") == 0) {
		DBG("Maximum number of PDP activation retries reached for F3");
	}
	if (g_strcmp0(reject_cause, "F4") == 0) {
		DBG("Maximum number of PDP activation retries reached for F4");
	}
}

static DBusMessage *veriquec_rpm_enable(DBusConnection *conn,
										DBusMessage *msg,
										void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;
	DBG("");

	if (data->rpm_mgr->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F1\",1,60,60", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}
	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F2\",1,60,30", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}
	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F3\",1,60,60", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}
	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F4\",1,60,30", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}

	// Register a callback function in case URC is reported
	data->rpm_mgr->notify_id = g_at_chat_register(data->mdm, "+QPDPTRYCHK:", qpdptrychk_urc_cb, FALSE, data, NULL);

	data->rpm_mgr->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->rpm_mgr->msg);

	__ofono_dbus_pending_reply(&data->rpm_mgr->msg, reply);

	return NULL;
}

static DBusMessage *veriquec_rpm_disable(DBusConnection *conn,
										DBusMessage *msg,
										void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;

	DBG("");

	if (data->rpm_mgr->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F1\",0,60,60", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}
	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F2\",0,60,30", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}
	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F3\",0,60,60", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}
	if (!g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F4\",0,60,30", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}

	data->rpm_mgr->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->rpm_mgr->msg);

	__ofono_dbus_pending_reply(&data->rpm_mgr->msg, reply);

	return NULL;
}

static const GDBusMethodTable rpm_manager_methods[] = {
	{ GDBUS_ASYNC_METHOD("Enable", NULL, GDBUS_ARGS({ "", "" }), veriquec_rpm_enable) },
	{ GDBUS_ASYNC_METHOD("Disable", NULL, GDBUS_ARGS({ "", "" }), veriquec_rpm_disable) },

	{}
};

static int veriquec_radio_policy_manager_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	/* Enable radio policy management */
	g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F1\",1,60,60", none_prefix, NULL, data, NULL);
	g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F2\",1,60,30", none_prefix, NULL, data, NULL);
	g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F3\",1,60,60", none_prefix, NULL, data, NULL);
	g_at_chat_send(data->app, "AT+QPDPTRYCFG=\"F4\",1,60,30", none_prefix, NULL, data, NULL);

	/* Create radio policy DBus interface */
	data->rpm_mgr = g_try_new0(struct veriquec_rpm_manager, 1);
	if (data->rpm_mgr == NULL)
		return -EIO;

	if (!g_dbus_register_interface(conn, path, RPM_MANAGER_INTERFACE,
		rpm_manager_methods, NULL, NULL,
		data, rpm_manager_cleanup)) {
		ofono_error("Could not register %s interface under %s", RPM_MANAGER_INTERFACE, path);
		g_free(data->rpm_mgr);
		return -EIO;
	}

	ofono_modem_add_interface(modem, RPM_MANAGER_INTERFACE);

	return 0;
}

static void veriquec_qgmr_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char *hw_rev_str = "EC25";
	const char *fw_rev_str;
	DBusMessage *reply;
	DBusMessageIter dbus_iter;
	DBusMessageIter dbus_dict;

	if (!ok)
		goto error;

	g_at_result_iter_init(&iter, result);
	g_at_result_iter_next(&iter, NULL);

	if ((fw_rev_str = g_at_result_iter_raw_line(&iter)) == NULL)
		goto error;

	reply = dbus_message_new_method_return(data->info->msg);

	dbus_message_iter_init_append(reply, &dbus_iter);

	dbus_message_iter_open_container(&dbus_iter, DBUS_TYPE_ARRAY,
			OFONO_PROPERTIES_ARRAY_SIGNATURE,
			&dbus_dict);

	DBG("fw_rev_str: %s\n", fw_rev_str);

	ofono_dbus_dict_append(&dbus_dict, "FW Version",
			DBUS_TYPE_STRING, &fw_rev_str);

	ofono_dbus_dict_append(&dbus_dict, "HW Version",
			DBUS_TYPE_STRING, &hw_rev_str);

	dbus_message_iter_close_container(&dbus_iter, &dbus_dict);

	__ofono_dbus_pending_reply(&data->info->msg, reply);

	return;

error:
	__ofono_dbus_pending_reply(&data->info->msg,
			__ofono_error_failed(data->info->msg));
}

static void modem_info_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_modem_info *info = data->info;

	g_free(info);
}

static DBusMessage *modem_info_get_properties(DBusConnection *conn,
							DBusMessage *msg,
							void *user_data)
{
	struct veriquec_data *data = user_data;

	DBG("");

	if (data->info->msg != NULL)
		return __ofono_error_busy(msg);

    /*
    Modem correctly sends the fw version (major version + minor version + sub version),
    only after the qmi_ready indication.

    If we do not have already received qmi_ready, do not query the fw version now.
    Rather query it later, after we receive qmi_ready and report it.
  */
    if (b_apind_qmi_ready_received)
    {
        if (!g_at_chat_send(data->app, "AT+QGMR?", NULL, veriquec_qgmr_cb,
            data, NULL))
          return __ofono_error_failed(msg);
    }

	data->info->msg = dbus_message_ref(msg);

	return NULL;
}

static const GDBusMethodTable modem_info_methods[] = {
	{ GDBUS_ASYNC_METHOD("GetProperties",
			NULL, GDBUS_ARGS({ "Properties", "a{sv}" }),
			modem_info_get_properties) },
	{}
};

static int veriquec_modem_info_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	data->info = g_try_new0(struct veriquec_modem_info, 1);
	if (data->info == NULL)
		return -EIO;

	if (!g_dbus_register_interface(conn, path, VENDOR_INFO_INTERFACE,
					modem_info_methods, NULL, NULL,
					data, modem_info_cleanup)) {
		ofono_error("Could not register %s interface under %s",
					VENDOR_INFO_INTERFACE, path);
		g_free(data->info);
		return -EIO;
	}

	ofono_modem_add_interface(modem, VENDOR_INFO_INTERFACE);
	return 0;
}

static void rssi_scan_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_rssi_scan *rssi_scan = data->rssi_scan;

	g_free(rssi_scan);
}

static void rssi_scan_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	DBusMessage *reply;
	DBusMessageIter dbus_iter;
	DBusMessageIter dbus_dict;

	DBG("");

	if (!ok)
		goto error;

	g_at_result_iter_init(&iter, result);

	int rssi = 1, rscp = 2, rsrp = 4, tech = -1;
	double rsrq = 5.1, ecno = 3;
	const char *tech_str;

	if (!g_at_result_iter_next(&iter, "+QCSQ:"))
		goto error;

	if (!g_at_result_iter_next_string(&iter, &tech_str))
		goto error;

	if (g_strcmp0(tech_str, "GSM") == 0)
		tech = 0;
	else if (g_strcmp0(tech_str, "WCDMA") == 0)
		tech = 2;
	else if (g_strcmp0(tech_str, "LTE") == 0)
		tech = 3;

	// All techs have some RSSI value
	if (tech != -1) {
		const char *str;

		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			goto error;

		rssi = g_ascii_strtoll(str, NULL, 10);
		DBG("rssi: %d", rssi);

		if (rssi > 0)
		{
			// This value is a positive dBm value, so we need to change the sign
			rssi *= -1;
			DBG("rssi (after sign change): %d", rssi);
		}
	}

	if (tech == 2) {
		// +QCSQ: "WCDMA",69,-72,-4
		const char *str;

		// AT parser can't handle negative numbers...
		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			goto error;
		rscp = g_ascii_strtoll(str, NULL, 10);

		// AT parser can't handle negative numbers...
		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			goto error;
		ecno = g_ascii_strtoll(str, NULL, 10);
	} else if (tech == 3) {
		// +QCSQ: "LTE",80,-109,177,-9
		const char *str;

		// AT parser can't handle negative numbers...
		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			goto error;
		rsrp = g_ascii_strtoll(str, NULL, 10);

		// We don't use the SINR value
		if (!g_at_result_iter_skip_next(&iter))
			goto error;

		// AT parser can't handle negative numbers...
		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			goto error;
		rsrq = g_ascii_strtoll(str, NULL, 10);
	}

	reply = dbus_message_new_method_return(data->rssi_scan->msg);
	dbus_message_iter_init_append(reply, &dbus_iter);

	dbus_message_iter_open_container(&dbus_iter, DBUS_TYPE_ARRAY,
	                                 OFONO_PROPERTIES_ARRAY_SIGNATURE,
	                                 &dbus_dict);

	ofono_dbus_dict_append(&dbus_dict, "rat", DBUS_TYPE_INT32, &tech);

	if (tech == 0) {
		ofono_dbus_dict_append(&dbus_dict, "rssi", DBUS_TYPE_INT32, &rssi);
	} else if (tech == 2) {
		ofono_dbus_dict_append(&dbus_dict, "rscp", DBUS_TYPE_INT32, &rscp);
		ofono_dbus_dict_append(&dbus_dict, "ecno", DBUS_TYPE_DOUBLE, &ecno);

	} else if (tech == 3) {
		ofono_dbus_dict_append(&dbus_dict, "rsrp", DBUS_TYPE_INT32, &rsrp);
		ofono_dbus_dict_append(&dbus_dict, "rsrq", DBUS_TYPE_DOUBLE, &rsrq);
	}

	if (tech != -1) {
		ofono_dbus_dict_append(&dbus_dict, "lac", DBUS_TYPE_INT32, &data->rssi_scan->lac);
		ofono_dbus_dict_append(&dbus_dict, "cell", DBUS_TYPE_INT32, &data->rssi_scan->cid);
	}

	dbus_message_iter_close_container(&dbus_iter, &dbus_dict);
	__ofono_dbus_pending_reply(&data->rssi_scan->msg, reply);
	return;

error:
	DBG("Failed to scan for signal quality");
	__ofono_dbus_pending_reply(&data->rssi_scan->msg, __ofono_error_failed(data->rssi_scan->msg));
}

static void rssi_scan_read_cid_lac_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char *str;
	bool rat_4G = false;

	DBG("");

	if (!ok)
		goto error;

	g_at_result_iter_init(&iter, result);

	// CGREG is used for 3G, CEREG is used for 4G
	// Sometimes the information is replicated i both cmds, but not always
	// So first try to pares out the information from CGREG
	if (!g_at_result_iter_next(&iter, "+CGREG:")) {
		g_at_result_iter_init(&iter, result); // Cmd is not CGREG, check if it is CEREG
		if (!g_at_result_iter_next(&iter, "+CEREG:")) {
			goto error; // Cmd is neither CGREG nor CEREG
		} else {
			rat_4G = true; // Cmd is CEREG ie we are on 4G
		}
	}

	// Skip mode and status
	if (!g_at_result_iter_skip_next(&iter))
		goto error;
	if (!g_at_result_iter_skip_next(&iter))
		goto error;

	if (!g_at_result_iter_next_string(&iter, &str)) {
		if (!rat_4G) {
			DBG("Could not read CID/LAC wiwith CGREG, try with with CEREG instead");
			g_at_chat_send(data->app, "AT+CEREG?", NULL, rssi_scan_read_cid_lac_cb, data, NULL);
			return;
		} else {
			goto error; // Already tried on 4G (CEREG)
		}
	}
	data->rssi_scan->lac = g_ascii_strtoll(str, NULL, 16);

	if (!g_at_result_iter_next_string(&iter, &str))
		goto error;
	data->rssi_scan->cid = g_ascii_strtoll(str, NULL, 16);

	// Now read the actual scan data
	g_at_chat_send(data->app, "AT+QCSQ", NULL, rssi_scan_cb, data, NULL);

	return;

error:
	DBG("Could not read CID/LAC");
	__ofono_dbus_pending_reply(&data->rssi_scan->msg, __ofono_error_failed(data->rssi_scan->msg));
}

static void rssi_scan_setup_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

	DBG("");

	if (!ok)
		goto error;

	__ofono_dbus_pending_reply(&data->rssi_scan->setup_msg, data->rssi_scan->reply_setup);

	return;

error:
	DBG("Failed to setup for signal quality scan");
	__ofono_dbus_pending_reply(&data->rssi_scan->setup_msg,
	                           __ofono_error_failed(data->rssi_scan->setup_msg));
	return;
}


static DBusMessage *rssi_scan(DBusConnection *conn,
                              DBusMessage *msg,
                              void *user_data)
{
	struct veriquec_data *data = user_data;
	DBG("");

	data->rssi_scan->msg = dbus_message_ref(msg);

	// Start with AT+CGREG? to get CID and LAC information
	g_at_chat_send(data->app, "AT+CGREG?", NULL, rssi_scan_read_cid_lac_cb, data, NULL);

	return NULL;
}

static DBusMessage *rssi_scan_setup(DBusConnection *conn,
                                    DBusMessage *msg,
                                    void *user_data)
{
	struct veriquec_data *data = user_data;
	char buf[256];
	int rat;

	DBG("");

	if (!dbus_message_get_args(msg, NULL, DBUS_TYPE_INT32, &rat, DBUS_TYPE_INVALID))
		return __ofono_error_invalid_args(msg);

	data->rssi_scan->setup_msg = dbus_message_ref(msg);

	if(rat == 7) {
		DBG("Activate all RATs");
		g_at_chat_send(data->app, "at+qcfg=\"cops_no_mode_change\",0", NULL, NULL, NULL, NULL);
		strcpy(buf,"AT+QCFG=\"nwscanmode\", 0");
	}else if (rat == 0 || rat == 2 || rat == 3) {
		// Have to convert 0 to 1, as the format differs from Gemalto
		DBG("Activate RAT: %d", rat);
		g_at_chat_send(data->app, "at+qcfg=\"cops_no_mode_change\",1", NULL, NULL, NULL, NULL);
		sprintf(buf,"AT+QCFG=\"nwscanmode\", %d", rat == 0 ? 1 : rat);
	} else {
		goto error;
	}

	data->rssi_scan->reply_setup = dbus_message_new_method_return(data->rssi_scan->setup_msg);
	g_at_chat_send(data->app, buf, NULL, rssi_scan_setup_cb, data, NULL);

	return NULL;

	error:
		DBG("Invalid value on requested rat %d", rat);
		__ofono_dbus_pending_reply(&data->rssi_scan->setup_msg,
		                           __ofono_error_failed(data->rssi_scan->setup_msg));
		return NULL;

}

static const GDBusMethodTable rssiscan_methods[] = {
		{ GDBUS_ASYNC_METHOD("Setup", GDBUS_ARGS({"rat","i"}), NULL, rssi_scan_setup) },
		{ GDBUS_ASYNC_METHOD("Scan", NULL, GDBUS_ARGS({"result","a{sv}"}), rssi_scan) },
		{}
};

static int veriquec_rssi_scan_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	data->rssi_scan = g_try_new0(struct veriquec_rssi_scan, 1);
	if (data->rssi_scan == NULL)
		return -EIO;

	if (!g_dbus_register_interface(conn, path, RSSISCAN_INTERFACE,
	                               rssiscan_methods, NULL, NULL,
	                               data, rssi_scan_cleanup)) {
		ofono_error("Could not register %s interface under %s", RSSISCAN_INTERFACE, path);
		g_free(data->rssi_scan);
		return -EIO;
	}

	ofono_modem_add_interface(modem, RSSISCAN_INTERFACE);
	return 0;
}

static void at_channel_check_mdm_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

	if (ok) {
		DBusMessage *reply;

		reply = dbus_message_new_method_return(data->at_channel->msg);

		__ofono_dbus_pending_reply(&data->at_channel->msg, reply);
	} else {
		DBG("Failed to get ok on at channel mdm");

		__ofono_dbus_pending_reply(&data->at_channel->msg, __ofono_error_failed(data->at_channel->msg));
	}
}

static void at_channel_check_app_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

	if (ok) {
		if (data->at_channel->channels > 1) {
			if (g_at_chat_send(data->mdm, "AT", NULL, at_channel_check_mdm_cb, data, NULL) == 0) {
				DBG("Failed to send at channel check mdm");
				__ofono_dbus_pending_reply(&data->at_channel->msg, __ofono_error_failed(data->at_channel->msg));
			}
		} else {
			DBusMessage *reply;

			reply = dbus_message_new_method_return(data->at_channel->msg);

			__ofono_dbus_pending_reply(&data->at_channel->msg, reply);
		}
	} else {
		DBG("Failed to get ok on at channel app");

		__ofono_dbus_pending_reply(&data->at_channel->msg, __ofono_error_failed(data->at_channel->msg));
	}
}

static DBusMessage *at_channel_check(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	int channels;

	if (data->at_channel->msg != NULL) {
		DBG("Ongoing AT check");
		return __ofono_error_busy(msg);
	}

	if (!dbus_message_get_args(msg, NULL, DBUS_TYPE_INT32, &channels, DBUS_TYPE_INVALID)) {
		DBG("Could not read dbus arguments");
		return __ofono_error_invalid_args(msg);
	}

	if ((channels >= 0) && (channels <= 3)) {
		data->at_channel->channels = channels;
	} else {
		DBG("Invalid channels = %d", channels);
		return __ofono_error_invalid_args(msg);
	}

	if (data->at_channel->channels > 0) {
		data->at_channel->msg = dbus_message_ref(msg);

		if ((data->at_channel->channels & 0x01) == 0x01) {
			if (g_at_chat_send(data->app, "AT", NULL, at_channel_check_app_cb, data, NULL) == 0) {
				DBG("Failed to send at channel check app");
				data->at_channel->msg = NULL;
				return __ofono_error_failed(msg);
			}
		} else {
			if (g_at_chat_send(data->mdm, "AT", NULL, at_channel_check_mdm_cb, data, NULL) == 0) {
				DBG("Failed to send at channel check mdm");
				data->at_channel->msg = NULL;
				return __ofono_error_failed(msg);
			}
		}
	} else {
		DBusMessage *reply;

		reply = dbus_message_new_method_return(msg);

		return reply;
	}

	return NULL;
}

static void at_channel_cmd_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = (struct veriquec_data *)user_data;
	DBusMessage *reply = NULL;
	const char *content = NULL;
	GAtResultIter iter;
	DBusMessageIter dbus_iter;
	bool result_data = false;

	DBG("Send AT cmd %s", ok ? "ok":"failed");
	reply = dbus_message_new_method_return(data->at_channel->msg);
	dbus_message_iter_init_append(reply, &dbus_iter);

	if (!ok) {
		dbus_message_iter_append_basic(&dbus_iter, DBUS_TYPE_STRING, &err_str);
		goto send;
	}

	g_at_result_iter_init(&iter, result);
	while (true) {
		if (!g_at_result_iter_next(&iter, NULL)) {
			if (!result_data) {
				dbus_message_iter_append_basic(&dbus_iter, DBUS_TYPE_STRING, &ok_str);
			}
			goto send;
		} else {
			result_data = true;
			content = g_at_result_iter_raw_line(&iter);
			dbus_message_iter_append_basic(&dbus_iter, DBUS_TYPE_STRING, &content);
		}
	}

send:
	__ofono_dbus_pending_reply(&data->at_channel->msg, reply);
}

static DBusMessage* at_channel_cmd(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = (struct veriquec_data *)user_data;
	const char *raw_data = NULL;
	DBusMessageIter iter;

	DBG("");

	if (data->at_channel->msg != NULL) {
		return __ofono_error_busy(msg);
	}
	data->at_channel->msg = dbus_message_ref(msg);

	if (!dbus_message_iter_init(msg, &iter)) {
		return __ofono_error_invalid_args(msg);
	}

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING) {
		return __ofono_error_invalid_args(msg);
	}

	dbus_message_iter_get_basic(&iter, &raw_data);
	if (!g_at_chat_send(data->app, raw_data, NULL, at_channel_cmd_cb, data, NULL))
	{
		__ofono_error_failed(data->at_channel->msg);
	}

	return NULL;
}

static void at_channel_get_date_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = (struct veriquec_data *) user_data;
	GAtResultIter iter;
	const char *reply_content = (const char *) date_str;
	DBusMessage *reply = NULL;
	DBusMessageIter dbus_iter;
	int len;

	DBG("");

	if (!ok) {
		goto send;
	}

	g_at_result_iter_init(&iter, result);

	// Result format: +QLTS:<time>,<dst>
	if (!g_at_result_iter_next(&iter, "+QLTS:")) {
		DBG("Expected '+QLTS:' failed");
		goto send;
	}

	// We are only interrested in <time> (because date is a part of <time>)
	if (!g_at_result_iter_next_string(&iter, &reply_content)) {
		DBG("Failed reading <time> from +QLTS-response");
	} else {
		// Reply string format should be "yy/mm/dd,hh:mm:ss" -> 17 chars
		len = strlen(reply_content);
		if (len >= DATE_MAXLEN + 2) { // Two extra digits for year
			// Remove additional (time zone) info
			// Change four digit year to two digit year
			len = DATE_MAXLEN;
			memcpy(date_str, &reply_content[2], len);
			reply_content = (const char *) date_str;
		}
	}

send:
	reply = dbus_message_new_method_return(data->at_channel->msg);
	dbus_message_iter_init_append(reply, &dbus_iter);
	dbus_message_iter_append_basic(&dbus_iter, DBUS_TYPE_STRING, &reply_content);
	__ofono_dbus_pending_reply(&data->at_channel->msg, reply);
}

static DBusMessage *at_channel_get_date(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = (struct veriquec_data *) user_data;

	DBG("");

	if (data->at_channel->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	data->at_channel->msg = dbus_message_ref(msg);

	if (g_at_chat_send(data->app, "AT+QLTS=2", qlts_prefix, at_channel_get_date_cb, data, NULL) == 0) {
		DBG("Failed to send at channel get date");
		__ofono_error_failed(data->at_channel->msg);
	}

	return NULL;
}

static DBusMessage *at_channel_CFUN1(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = (struct veriquec_data *) user_data;
	DBusMessage *reply;
	DBG("");

	if (data->at_channel->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!g_at_chat_send(data->app, "AT+CFUN=1,1", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}

	data->at_channel->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->at_channel->msg);

	__ofono_dbus_pending_reply(&data->at_channel->msg, reply);

	return NULL;
}

static DBusMessage *at_channel_CFUN0(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = (struct veriquec_data *) user_data;
	DBusMessage *reply;
	DBG("");

	if (data->at_channel->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!g_at_chat_send(data->app, "AT+CFUN=0", none_prefix, NULL, data, NULL)) {
		return __ofono_error_failed(msg);
	}

	data->at_channel->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->at_channel->msg);

	__ofono_dbus_pending_reply(&data->at_channel->msg, reply);

	return NULL;
}

static void at_channel_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_at_channel *at_channel = data->at_channel;

	g_free(at_channel);
}

static const GDBusMethodTable at_channel_methods[] = {
	{ GDBUS_ASYNC_METHOD("Check", GDBUS_ARGS({"channels","i"}), NULL, at_channel_check) },
	{ GDBUS_ASYNC_METHOD("SendAtCmd", GDBUS_ARGS( {"cmd", "s"}), GDBUS_ARGS( {"resp", "s"}), at_channel_cmd) },
	{ GDBUS_ASYNC_METHOD("GetDate", NULL, GDBUS_ARGS({"date","s"}), at_channel_get_date) },
	{ GDBUS_ASYNC_METHOD("ModemFuncFull", NULL, GDBUS_ARGS({ "", "" }), at_channel_CFUN1) },
	{ GDBUS_ASYNC_METHOD("ModemFuncMin",  NULL, GDBUS_ARGS({ "", "" }), at_channel_CFUN0) },
	{}
};

static int veriquec_at_channel_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	data->at_channel = g_try_new0(struct veriquec_at_channel, 1);
	if (data->at_channel == NULL) {
		return -EIO;
	}

	if (!g_dbus_register_interface(conn, path, AT_CHANNEL_INTERFACE,
	                               at_channel_methods, NULL, NULL, data, at_channel_cleanup)) {
		ofono_error("Could not register %s interface under %s", AT_CHANNEL_INTERFACE, path);
		g_free(data->at_channel);
		return -EIO;
	}

	ofono_modem_add_interface(modem, AT_CHANNEL_INTERFACE);
	return 0;
}

static void cops_sim_refresh_end_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *veriquec_data = (struct veriquec_data *) user_data;
	DBusMessage *reply;

	if (!ok) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		return;
	}

	DBG("Sim refresh done!\n");
	__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg, dbus_message_new_method_return(veriquec_data->sim_refresh->msg));
}

static void sim_refresh_hplmnwact_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *veriquec_data = (struct veriquec_data *) user_data;

	if (!ok) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		return;
	}

	if (!g_at_chat_send(veriquec_data->app, "AT+COPS=0", cops_prefix, cops_sim_refresh_end_cb,
	                    veriquec_data, NULL)) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
	}
}

static void sim_refresh_locigprs_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *veriquec_data = (struct veriquec_data *) user_data;

	if (!ok) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		return;
	}

	if (!g_at_chat_send(
	    veriquec_data->app,
	    "AT+CRSM=214,28531,0,0,14,\"FFFFFFFFFFFFFFFFFFFFFFFFFFFF\"", crsm_prefix,
	    sim_refresh_hplmnwact_cb, veriquec_data, NULL)) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		g_at_chat_send(veriquec_data->app, "AT+COPS=0", cops_prefix, NULL,
		               veriquec_data, NULL);
	}
}

static void sim_refresh_fplmn_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *veriquec_data = (struct veriquec_data *) user_data;

	if (!ok) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		return;
	}

	if (!g_at_chat_send(veriquec_data->app,
	                    "AT+CRSM=214,28542,0,0,11, \"FFFFFFFFFFFFFFFFFFFFFF\"",
	                    crsm_prefix, sim_refresh_locigprs_cb, veriquec_data,
	                    NULL)) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		g_at_chat_send(veriquec_data->app, "AT+COPS=0", cops_prefix, NULL,
		               veriquec_data, NULL);
	}
}

static void cops_sim_refresh_setup_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *veriquec_data = (struct veriquec_data *) user_data;

	if (!ok) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		return;
	}

	if (!g_at_chat_send(veriquec_data->app,
	                    "AT+CRSM=214,28539,0,0,12,\"FFFFFFFFFFFFFFFFFFFFFFFF\"",
	                    crsm_prefix, sim_refresh_fplmn_cb, veriquec_data,
	                    NULL)) {
		__ofono_dbus_pending_reply(&veriquec_data->sim_refresh->msg,
					__ofono_error_failed(veriquec_data->sim_refresh->msg));
		g_at_chat_send(veriquec_data->app, "AT+COPS=0", cops_prefix, NULL,
		               veriquec_data, NULL);
	}
}

static DBusMessage *sim_refresh(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;

	DBG("");

	if (data->sim_refresh->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	DBG("Do sim refresh!");

	data->sim_refresh->msg = dbus_message_ref(msg);

	if (!g_at_chat_send(data->app, "AT+COPS=2", cops_prefix, cops_sim_refresh_setup_cb, data, NULL)) {
		data->sim_refresh->msg = NULL;
		return __ofono_error_failed(msg);
	}
	return NULL;
}

static void sim_refresh_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_sim_refresh *sim_refresh = data->sim_refresh;
	g_free(sim_refresh);
}

static const GDBusMethodTable sim_refresh_methods[] = {
		{GDBUS_ASYNC_METHOD("Refresh", NULL, GDBUS_ARGS( {"", ""}), sim_refresh) },
		{ }
};

static int veriquec_sim_refresh_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	data->sim_refresh = g_try_new0(struct veriquec_sim_refresh, 1);
	if (data->sim_refresh == NULL) {
		return -EIO;
	}

	if (!g_dbus_register_interface(conn, path, SIM_REFRESH_INTERFACE,
	                               sim_refresh_methods, NULL, NULL, data,
	                               sim_refresh_cleanup)) {
		ofono_error("Could not register %s interface under %s",
		SIM_REFRESH_INTERFACE,
		            path);
		return -EIO;
	}

	ofono_modem_add_interface(modem, SIM_REFRESH_INTERFACE);
	return 0;
}

static void jam_notify_cb(GAtResult *result, gpointer user_data)
{
	DBusConnection *conn = ofono_dbus_get_connection();
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char* ind_str;
	dbus_bool_t jammed = FALSE;

	DBG("");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QJDR:")) {
		return;
	}

	if (!g_at_result_iter_next_unquoted_string(&iter, &ind_str)) {
		return;
	}

	if (g_strcmp0(ind_str, "JAMMED") == 0) {
		jammed = TRUE;
	} else if ((g_strcmp0(ind_str, "NOJAMMING") != 0) && (g_strcmp0(ind_str, "0") != 0)) {
		return;
	}

	// Send property changed
	ofono_dbus_signal_property_changed(conn, data->jam_detection->path, JAM_DETECTION_INTERFACE, "Jammed", DBUS_TYPE_BOOLEAN, &jammed);
}

static DBusMessage *jam_detection_enable(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;

	DBG("");

	if (data == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!data->jam_detection->enabled) {
		data->jam_detection->enabled = TRUE;

		data->jam_detection->notify_id = g_at_chat_register(data->mdm, "+QJDR:", jam_notify_cb, FALSE, data, NULL);

		// Enable jamming detection
		if (!g_at_chat_send(data->app, "AT+QJDR=1", none_prefix, NULL, data, NULL)) {
			return __ofono_error_failed(msg);
		}

		// Enable URC
		if (!g_at_chat_send(data->app, "AT+QJDCFG=\"urc\",1", none_prefix, NULL, data, NULL)) {
			return __ofono_error_failed(msg);
		}
	}

	data->jam_detection->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->jam_detection->msg);

	__ofono_dbus_pending_reply(&data->jam_detection->msg, reply);

	return NULL;
}

static DBusMessage *jam_detection_disable(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;

	DBG("");

	if (data == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (data->jam_detection->enabled) {
		data->jam_detection->enabled = FALSE;

		g_at_chat_unregister(data->app, data->jam_detection->notify_id);

		// Disable jamming detection
		if (!g_at_chat_send(data->app, "AT+QJDR=0", none_prefix, NULL, data, NULL)) {
			return __ofono_error_failed(msg);
		}

		// Disable URC
		if (!g_at_chat_send(data->app, "AT+QJDCFG=\"urc\",0", none_prefix, NULL, data, NULL)) {
			return __ofono_error_failed(msg);
		}

	}

	data->jam_detection->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->jam_detection->msg);

	__ofono_dbus_pending_reply(&data->jam_detection->msg, reply);

	return NULL;
}

// "Empty" function, ie no action is done
// Kept only for legacy reasons
static DBusMessage *jam_detection_clear(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;

	DBG("");

	if (data == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	data->jam_detection->msg = dbus_message_ref(msg);

	reply = dbus_message_new_method_return(data->jam_detection->msg);

	__ofono_dbus_pending_reply(&data->jam_detection->msg, reply);

	return NULL;
}

static void veriquec_qjdcfg_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	DBusMessage *reply;
	DBusMessageIter dbus_iter;
	DBusMessageIter dbus_dict;
	const char *ind_str;
	const char *val_str;
	int ind_val;

	DBG("");

	if (!ok)
		goto error;

	reply = dbus_message_new_method_return(data->jam_detection->msg);

	dbus_message_iter_init_append(reply, &dbus_iter);

	dbus_message_iter_open_container(&dbus_iter, DBUS_TYPE_ARRAY,
			OFONO_PROPERTIES_ARRAY_SIGNATURE,
			&dbus_dict);

	g_at_result_iter_init(&iter, result);

	while (g_at_result_iter_next(&iter, "+QJDCFG:")) {
		if (!g_at_result_iter_next_string(&iter, &ind_str)) {
			goto error;
		}

		// AT parser can't handle negative numbers...
		if (!g_at_result_iter_next_unquoted_string(&iter, &val_str))
			goto error;
		ind_val = g_ascii_strtoll(val_str, NULL, 10);

		ofono_dbus_dict_append(&dbus_dict, ind_str, DBUS_TYPE_INT32, &ind_val);
	}

	dbus_message_iter_close_container(&dbus_iter, &dbus_dict);
	__ofono_dbus_pending_reply(&data->jam_detection->msg, reply);
	return;

error:
	__ofono_dbus_pending_reply(&data->jam_detection->msg,
			__ofono_error_failed(data->jam_detection->msg));
}

static DBusMessage *jam_detection_configuration_get(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;

	DBG("");

	if (data == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!g_at_chat_send(data->app, "AT+QJDCFG?", NULL, veriquec_qjdcfg_cb,
			data, NULL))
		return __ofono_error_failed(msg);

	data->jam_detection->msg = dbus_message_ref(msg);

	return NULL;
}

static DBusMessage *jam_detection_configuration_set(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessageIter array;
	DBusMessageIter dict;
	DBusMessageIter entry;
	int ind_val = 0;
	char cmd[256];

	DBG("");

	if (data == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection == NULL) {
		return __ofono_error_failed(msg);
	}

	if (!dbus_message_iter_init(msg, &array)) {
		return __ofono_error_failed(msg);
	}

	if (dbus_message_iter_get_arg_type(&array) != DBUS_TYPE_ARRAY) {
		return __ofono_error_failed(msg);
	}

	dbus_message_iter_recurse(&array, &dict);

	while (dbus_message_iter_get_arg_type(&dict) == DBUS_TYPE_DICT_ENTRY) {
		DBusMessageIter iter;
		const char *key;
		int type;

		dbus_message_iter_recurse(&dict, &entry);

		dbus_message_iter_get_basic(&entry, &key);

		dbus_message_iter_next(&entry);
		dbus_message_iter_recurse(&entry, &iter);

		type = dbus_message_iter_get_arg_type(&iter);
		if (type == DBUS_TYPE_INT32) {
			dbus_message_iter_get_basic(&iter, &ind_val);
			sprintf(cmd,"AT+QJDCFG=\"%s\",%d", key, ind_val);
			// Just disable the parameter sending for now.
			// Gsmsrv now have settings only valid in CU1
			// We don't have any need settings for CU2 at the moment
			//g_at_chat_send(data->app, cmd, none_prefix, NULL, NULL, NULL);
		}

		dbus_message_iter_next(&dict);
	}

	return dbus_message_new_method_return(msg);
}

static void veriquec_qjdr_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	DBusMessage *reply;
	DBusMessageIter dbus_iter;
	DBusMessageIter dbus_dict;
	const char* ind_str;
	dbus_bool_t jammed = FALSE;


	DBG("");

	if (!ok)
		goto error;

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QJDR:")) {
		goto error;
	}

	if (!g_at_result_iter_next_unquoted_string(&iter, &ind_str)) {
		goto error;
	}

	if (g_strcmp0(ind_str, "JAMMED") == 0) {
		jammed = TRUE;
	} else if ((g_strcmp0(ind_str, "NOJAMMING") != 0) && (g_strcmp0(ind_str, "0") != 0)) {
		goto error;
	}

	reply = dbus_message_new_method_return(data->jam_detection->msg);
	dbus_message_iter_init_append(reply, &dbus_iter);
	dbus_message_iter_open_container(&dbus_iter, DBUS_TYPE_ARRAY,
			OFONO_PROPERTIES_ARRAY_SIGNATURE,
			&dbus_dict);

	ofono_dbus_dict_append(&dbus_dict, "Jammed", DBUS_TYPE_BOOLEAN, &jammed);

	dbus_message_iter_close_container(&dbus_iter, &dbus_dict);
	__ofono_dbus_pending_reply(&data->jam_detection->msg, reply);
	return;

error:
	__ofono_dbus_pending_reply(&data->jam_detection->msg,
			__ofono_error_failed(data->jam_detection->msg));
}

static DBusMessage *jam_detection_get_properties(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;

	DBG("");

	if (data == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection == NULL) {
		return __ofono_error_failed(msg);
	}

	if (data->jam_detection->msg != NULL) {
		return __ofono_error_busy(msg);
	}

	if (!g_at_chat_send(data->app, "AT+QJDR?", NULL, veriquec_qjdr_cb,
			data, NULL))
		return __ofono_error_failed(msg);

	data->jam_detection->msg = dbus_message_ref(msg);

	return NULL;
}

static void jam_detection_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_jam_detection *jam_detection = data->jam_detection;

	g_free(jam_detection);
}

static const GDBusMethodTable jam_detection_methods[] = {
	{ GDBUS_ASYNC_METHOD("GetProperties", NULL, GDBUS_ARGS({ "properties", "a{sv}" }), jam_detection_get_properties) },
	{ GDBUS_ASYNC_METHOD("Enable", NULL, GDBUS_ARGS({ "", "" }), jam_detection_enable) },
	{ GDBUS_ASYNC_METHOD("Disable", NULL, GDBUS_ARGS({ "", "" }), jam_detection_disable) },
	{ GDBUS_ASYNC_METHOD("Clear", NULL, GDBUS_ARGS({ "", "" }), jam_detection_clear) },
	{ GDBUS_ASYNC_METHOD("GetConfiguration", NULL, GDBUS_ARGS({ "configuration", "a{sv}" }), jam_detection_configuration_get) },
	{ GDBUS_METHOD("SetConfiguration", GDBUS_ARGS({ "configuration", "a{sv}" }), NULL, jam_detection_configuration_set) },
	{}
};

static const GDBusSignalTable jam_detection_signals[] = {
	{ GDBUS_SIGNAL("PropertyChanged", GDBUS_ARGS({ "name", "s" }, { "value", "v" })) },
	{}
};

int veriquec_jam_detection_register(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	data->jam_detection = g_try_new0(struct veriquec_jam_detection, 1);
	if (data->jam_detection == NULL) {
		return -EIO;
	}

	data->jam_detection->enabled = FALSE;
	data->jam_detection->path = path;

	if (!g_dbus_register_interface(conn, path, JAM_DETECTION_INTERFACE, jam_detection_methods, jam_detection_signals, NULL, data, jam_detection_cleanup)) {
		ofono_error("Could not register %s interface under %s", JAM_DETECTION_INTERFACE, path);
		g_free(data->jam_detection);
		return -EIO;
	}

	ofono_modem_add_interface(modem, JAM_DETECTION_INTERFACE);
	return 0;
}

static void at_cmd_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

	DBG("ok: %d", ok);

	/*
	    Modem IMS status at this point:
		  ------------------------------------------------------------
		  |	 Scenario   |     MBN      |   +QCFG=ims  |  ims_enabled |
		  |             |              |   execution  |              |
		  ------------------------------------------------------------
		  | EnableIms	|   Activated  |      Ok      |     true     |
		  | EnableIms	|   Activated  |    Not Ok    |     false    |
		  | DisableIms	|  Deactivated |      Ok      |     false    |
		  | DisableIms	|  Deactivated |    Not Ok    |     false    |
		  ------------------------------------------------------------
	*/
	data->ims_data->ims_enabled = false; //Setting default to false as per above table.

	if(ok){
		if (data->ims_data->ims_request == IMS_REQ_ENABLE) {
			data->ims_data->ims_enabled = true;
		}
		__ofono_dbus_pending_reply(&data->ims_data->msg,
			dbus_message_new_method_return(data->ims_data->msg));
	}
	else{
		__ofono_dbus_pending_reply(&data->ims_data->msg,
			__ofono_error_failed(data->ims_data->msg));
	}
}

static void qmbncfg_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	const char *qcfg_cmd = (data->ims_data->ims_request == IMS_REQ_ENABLE) ?
								"AT+QCFG=\"ims\",1" : "AT+QCFG=\"ims\",2";

    DBG("");

	if(!ok || !g_at_chat_send(data->app,
							  qcfg_cmd,
							  none_prefix,
							  at_cmd_cb,
							  data,
							  NULL))
	{
		DBG("%s", (data->ims_data->ims_request == IMS_REQ_ENABLE) ?
					"Failed to enable IMS" : "Failed to disable IMS");
		__ofono_dbus_pending_reply(&data->ims_data->msg,
			__ofono_error_failed(data->ims_data->msg));
	}
}

static void send_ims_properties(const struct veriquec_data* data,
  bool ims_enabled_status, bool ims_registered_status, bool volte_available_status)
{
	DBusMessage *reply;
	DBusMessageIter dbus_iter;
	DBusMessageIter dbus_dict;
    ofono_bool_t ims_enabled = (ims_enabled_status ? 1 : 0);
    ofono_bool_t ims_registered = (ims_registered_status ? 1 : 0);
	ofono_bool_t volte_available = (volte_available_status ? 1 : 0);

    DBG("");

	reply = dbus_message_new_method_return(data->ims_data->msg);

	dbus_message_iter_init_append(reply, &dbus_iter);

	dbus_message_iter_open_container(&dbus_iter, DBUS_TYPE_ARRAY,
									 OFONO_PROPERTIES_ARRAY_SIGNATURE,
									 &dbus_dict);

	ofono_dbus_dict_append(&dbus_dict, "ImsEnabled",
			DBUS_TYPE_BOOLEAN, &ims_enabled);

	ofono_dbus_dict_append(&dbus_dict, "ImsRegistered",
			DBUS_TYPE_BOOLEAN, &ims_registered);

	ofono_dbus_dict_append(&dbus_dict, "VolteAvailable",
			DBUS_TYPE_BOOLEAN, &volte_available);

	dbus_message_iter_close_container(&dbus_iter, &dbus_dict);

	__ofono_dbus_pending_reply(&data->ims_data->msg, reply);
}

/**
 * @brief  Returns mbn name for the given operator
 *
 * @param  [IN]  mcc: operator mcc
 * 	       [IN]  mnc: operator mnc
 *
 * @return mbn_name: Valid string if matching mbn found, NULL otherwise.
 * 					 Caller function must free the mbn_name string.
 */
static char* check_operator_mbn(const char* mcc, const char* mnc)
{
	DBG("mcc: %s, mnc: %s", (mcc ? mcc : "null"),  (mnc ? mnc : "null"));

	if ((mcc == NULL) || (mnc == NULL)){
		DBG("mcc/mnc cannot be NULL");
		return NULL;
	}

	char *mbn_name = NULL;
	char operator[MCC_LEN + MNC_MAX_LEN + 1] = {0};
	strncpy(operator, mcc, MCC_LEN);
	strcat(operator, mnc);

	for (int i = 0; i < MAX_ROW_IMS_OPERATOR_LIST; i++)
	{
		if ((g_strcmp0(imsOperatorList[i].plmn_id, operator) == 0) &&
			imsOperatorList[i].mbn_available &&
			imsOperatorList[i].volte_support &&
			(strlen(imsOperatorList[i].mbn_name) != 0))
		{
			int mbn_len = strlen(imsOperatorList[i].mbn_name);
			mbn_name = g_try_new0(char, mbn_len + 1);
			if (mbn_name) {
				strncpy(mbn_name, imsOperatorList[i].mbn_name, mbn_len);
			}
		}
	}

	DBG("mbn_name: %s", mbn_name ? mbn_name : "null");
	return mbn_name;
}

static void qcfg_ims_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char* qcfg_ims_str = NULL;
	const char* ims_conf_str = NULL;

    DBG("");

	g_at_result_iter_init(&iter, result);

	if (g_at_result_iter_next(&iter, "+QCFG:") &&
		g_at_result_iter_next_string(&iter, &qcfg_ims_str) &&
		(g_strcmp0(qcfg_ims_str, "ims") == 0) &&
		g_at_result_iter_next_unquoted_string(&iter, &ims_conf_str)) {

		int ims_conf = g_ascii_strtoll(ims_conf_str, NULL, 10);

		DBG("Received value: ims_conf: %d", ims_conf);
        data->ims_data->ims_enabled = (IMS_ENABLED == ims_conf);
	}
	else {
		DBG("AT+QCFG=\"ims\" query failed; setting ims_enable to false");
        data->ims_data->ims_enabled = false;
	}

	int curr_ims_enable_status = data->ims_data->ims_enabled ? 1 : 0;
	ofono_dbus_signal_property_changed(ofono_dbus_get_connection(), data->ims_data->path,
		IMS_MANAGER_INTERFACE, "ImsEnabled", DBUS_TYPE_BOOLEAN, &curr_ims_enable_status);
}

static void qmbncfg_list_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	bool qcfg_ims_chk_ongoing = false;
	const char *str = NULL;
	char* mbn_name = NULL;

#define INVALID_VAL -1
	int index = INVALID_VAL;
	int selected = INVALID_VAL;
	int activated = INVALID_VAL;

    DBG("");

	g_at_result_iter_init(&iter, result);

	while (ok &&
		   g_at_result_iter_next(&iter, "+QMBNCFG:") &&
		   g_at_result_iter_next_string(&iter, &str) &&
		   (g_strcmp0(str, "List") == 0)) {

		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			break;
		index = g_ascii_strtoll(str, NULL, 10);

		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			break;
		selected = g_ascii_strtoll(str, NULL, 10);

		if (!g_at_result_iter_next_unquoted_string(&iter, &str))
			break;
		activated = g_ascii_strtoll(str, NULL, 10);

		if (!g_at_result_iter_next_string(&iter, &str))
			break;

		DBG("[%s]: index: %d, selected?: %d activated?: %d", str, index, selected, activated);

		if (activated == 1) {
			mbn_name = check_operator_mbn(data->netreg_data.plmn_mcc, data->netreg_data.plmn_mnc);

			if (g_strcmp0(str, mbn_name) == 0) {
				if(g_at_chat_send(data->app, "AT+QCFG=\"ims\"", NULL,
								qcfg_ims_cb, data, NULL)) {
					qcfg_ims_chk_ongoing = true;
				}
			}
			else {
				/*TODO: Scenario where activated MBN is not compatiblie with current operator
				        Implement notifying Gsmsrv to trigger EnableIms/DisableIms
				*/
			}

			free(mbn_name);
			break;
		}
	}

	if (!qcfg_ims_chk_ongoing) {
		data->ims_data->ims_enabled = false;
		int curr_ims_enable_status = 0;
		ofono_dbus_signal_property_changed(ofono_dbus_get_connection(), data->ims_data->path,
			IMS_MANAGER_INTERFACE, "ImsEnabled", DBUS_TYPE_BOOLEAN, &curr_ims_enable_status);
	}
}

static void evaluate_ims_status(struct veriquec_data* data)
{

	DBG("");

	if (!g_at_chat_send(data->app, "AT+QMBNCFG=\"List\"", NULL,
						qmbncfg_list_cb, data, NULL)){
		DBG("Querying MBN list failed");
	}
}

/**
 * @brief Function to update complete network registration data
 *        i.e. current operator (mcc/mnc) & registration status
 */
static void update_netreg_data(struct veriquec_data* data)
{
//	DBG("");

	if ((g_strcmp0(__cached_netreg_data.plmn_mcc, INVALID_MCC) != 0) &&
	    (g_strcmp0(__cached_netreg_data.plmn_mnc, INVALID_MNC) != 0) &&
		__cached_netreg_data.status != STATUS_INVALID)
	{	//reg status, mcc & mnc are received

		if ((g_strcmp0(__cached_netreg_data.plmn_mcc, data->netreg_data.plmn_mcc) != 0) ||
			(g_strcmp0(__cached_netreg_data.plmn_mnc, data->netreg_data.plmn_mnc) != 0) ||
			__cached_netreg_data.status != data->netreg_data.status)
		{
			strncpy(data->netreg_data.plmn_mcc, __cached_netreg_data.plmn_mcc, sizeof(__cached_netreg_data.plmn_mcc));
			strncpy(data->netreg_data.plmn_mnc, __cached_netreg_data.plmn_mnc, sizeof(__cached_netreg_data.plmn_mnc));
			data->netreg_data.status = __cached_netreg_data.status;
			DBG("Netreg data changed [reg_status, plmn_id]: [%d, %s%s]",
			    data->netreg_data.status, data->netreg_data.plmn_mcc, data->netreg_data.plmn_mnc);

			if (data->netreg_data.status == STATUS_REGISTERED) {
				evaluate_ims_status(data);
			}
		}

		reset_netreg_data(&__cached_netreg_data);
	}
}

/**
 * @brief org.ofono.NetworkRegistration PropertyChanged handler function
 */
static gboolean netreg_changed(DBusConnection *conn,
					DBusMessage *msg, void *user_data)
{
//	DBG("");

	struct veriquec_data* data = user_data;
	DBusMessageIter iter;
	DBusMessageIter var;
	const char *property;

	if (!dbus_message_iter_init(msg, &iter))
		return TRUE;

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING)
		return TRUE;

	dbus_message_iter_get_basic(&iter, &property);
	dbus_message_iter_next(&iter);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_VARIANT)
		return TRUE;
	dbus_message_iter_recurse(&iter, &var);

	if (!g_strcmp0("Status", property))
	{
		const char *value;

		if (dbus_message_iter_get_arg_type(&var) != DBUS_TYPE_STRING) {
			return TRUE;
		}
		dbus_message_iter_get_basic(&var, &value);

		__cached_netreg_data.status =
			(!g_strcmp0("registered", value) || !g_strcmp0("roaming", value)) ?
				STATUS_REGISTERED : STATUS_DEREGISTERED;
		//DBG("Updated __cached_netreg_data.status: %d", __cached_netreg_data.status);
	}
	else if (g_strcmp0("MobileCountryCode", property) == 0)
	{
		const char *value;

		if (dbus_message_iter_get_arg_type(&var) != DBUS_TYPE_STRING) {
			return TRUE;
		}
		dbus_message_iter_get_basic(&var, &value);

		if (strlen(value) == MCC_LEN) {
			memset(__cached_netreg_data.plmn_mcc, 0, MCC_LEN);
			strncpy(__cached_netreg_data.plmn_mcc, value, MCC_LEN);
			//DBG("Updated __cached_netreg_data.plmn_mcc: %s", __cached_netreg_data.plmn_mcc);
		} else {
			DBG("Invalid MCC");
		}
	}
	else if (g_strcmp0("MobileNetworkCode", property) == 0)
	{
		uint8_t mnc_len;
		const char *value;

		if (dbus_message_iter_get_arg_type(&var) != DBUS_TYPE_STRING) {
			return TRUE;
		}
		dbus_message_iter_get_basic(&var, &value);

		mnc_len  = strlen(value);
		if ((mnc_len == MNC_MIN_LEN) || (mnc_len == MNC_MAX_LEN)) {
			memset(__cached_netreg_data.plmn_mnc, 0, MNC_MAX_LEN);
			strncpy(__cached_netreg_data.plmn_mnc, value, mnc_len);
			//DBG("Updated __cached_netreg_data.plmn_mnc: %s", __cached_netreg_data.plmn_mnc);
		} else {
			DBG("Invalid MNC");
		}
	}

	update_netreg_data(data);
	return TRUE;
}

/**
 * @brief 	Configure ims support in modem
 *
 * @param 	enable : true - enables ims support, false - disables ims support
 * @param 	mbn    : valid mbn name string to enable ims support. This parameter
 *                   is not used for disable ims case.
 * @param 	data   : veriquec_data
 * @return           true if there are no error conditions, false otherwise
 */
static bool set_ims_support(bool enable, const char* mbn, struct veriquec_data* data)
{
	char* cmd_name = NULL;
	bool ret = true;

    DBG("set ims support: %d [mbn: %s]", enable, mbn);

	if (enable && !mbn) {
		return false;
	}

	if (enable) {
		cmd_name = g_try_new0(char, (strlen(mbn) +
									 strlen(IMS_MBN_SELECT_CMD) +
									 2/*for quotes around MBN name*/ +
									 1));
		if (cmd_name) {
			strcpy(cmd_name, IMS_MBN_SELECT_CMD);
			strcat(cmd_name,"\"");
			strcat(cmd_name, mbn);
			strcat(cmd_name,"\"");
		}
	} else {
		cmd_name = g_try_new0(char, strlen(IMS_MBN_DEACTIVATE_CMD) + 1);
		if (cmd_name) {
			strcpy(cmd_name, IMS_MBN_DEACTIVATE_CMD);
		}
	}

	DBG("AT Cmd: %s", cmd_name);
	if((cmd_name == NULL) ||
	   !g_at_chat_send(data->app, cmd_name, NULL, qmbncfg_cb, data, NULL)) {
		ret = false;
	}

	free(cmd_name);
	cmd_name = NULL;

    return ret;
}

/**
 * @brief org.ofono.verisure.ImsManager.EnableIms method handler function
 */
static DBusMessage* enable_ims(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	DBusMessage* error = NULL;
	DBusMessageIter dbus_iter;
    struct veriquec_data *data = user_data;

	char* mbn_name = NULL;
	char* err_msg = NULL;

	DBG("");
    data->ims_data->ims_request = IMS_REQ_ENABLE;

	if (data->netreg_data.status != STATUS_REGISTERED)
	{
		error = g_dbus_create_error(msg, VERISURE_ERROR_INTERFACE ".Failed",
					"Operation failed");
	}
	else
	{
		mbn_name = check_operator_mbn(data->netreg_data.plmn_mcc, data->netreg_data.plmn_mnc);
		if (mbn_name == NULL)
		{
			error = g_dbus_create_error(msg, VERISURE_ERROR_INTERFACE ".UnapprovedOperator",
			            "Operator is not Whitelisted for IMS services");
		}
		else if (!set_ims_support(true, mbn_name, data))
		{
			error = g_dbus_create_error(msg, VERISURE_ERROR_INTERFACE ".Failed",
			            "Operation failed");
		}
		else
		{
			data->ims_data->msg = dbus_message_ref(msg);
		}

		free(mbn_name);
	}

	if (error != NULL) {
		return error;
	}

	return NULL;
}

/**
 * @brief org.ofono.verisure.ImsManager.DisableIms method handler function
 */
static DBusMessage* disable_ims(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
    DBusMessage *reply;
    struct veriquec_data *data = user_data;

    DBG("");
    data->ims_data->ims_request = IMS_REQ_DISABLE;

	if (!set_ims_support(false, NULL, data))
	{
		return __ofono_error_failed(msg);
	}

    data->ims_data->msg = dbus_message_ref(msg);
    return NULL;
}

/**
 * @brief org.ofono.verisure.ImsManager.GetProperties method handler function
 */
static DBusMessage* get_properties_handler(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;
	DBusMessageIter dbus_iter;
	DBusMessageIter dbus_dict;

    DBG("");

	dbus_message_ref(msg);

    ofono_bool_t ims_enabled = (data->ims_data->ims_enabled ? 1 : 0);
    ofono_bool_t ims_registered = (data->ims_data->ims_registered ? 1 : 0);
	ofono_bool_t volte_available = (data->ims_data->volte_available ? 1 : 0);

	reply = dbus_message_new_method_return(msg);

	dbus_message_iter_init_append(reply, &dbus_iter);

	dbus_message_iter_open_container(&dbus_iter, DBUS_TYPE_ARRAY,
									 OFONO_PROPERTIES_ARRAY_SIGNATURE,
									 &dbus_dict);

	ofono_dbus_dict_append(&dbus_dict, "ImsEnabled",
			DBUS_TYPE_BOOLEAN, &ims_enabled);

	ofono_dbus_dict_append(&dbus_dict, "ImsRegistered",
			DBUS_TYPE_BOOLEAN, &ims_registered);

	ofono_dbus_dict_append(&dbus_dict, "VolteAvailable",
			DBUS_TYPE_BOOLEAN, &volte_available);

	dbus_message_iter_close_container(&dbus_iter, &dbus_dict);

	__ofono_dbus_pending_reply(&msg, reply);

	return NULL;
}

static const GDBusMethodTable ims_methods[] = {
	{ GDBUS_ASYNC_METHOD("EnableIms", NULL, GDBUS_ARGS({ "result", "s" }), enable_ims) },
	{ GDBUS_ASYNC_METHOD("DisableIms", NULL, GDBUS_ARGS({ "", "" }), disable_ims) },
	{ GDBUS_ASYNC_METHOD("GetProperties", NULL, GDBUS_ARGS({ "Properties", "a{sv}" }), get_properties_handler) },
	{}
};

static const GDBusSignalTable ims_signals[] = {
	{ GDBUS_SIGNAL("PropertyChanged", GDBUS_ARGS({ "name", "s" }, { "value", "v" })) },
	{}
};

static void ims_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct veriquec_ims_data *ims_data = data->ims_data;

	g_free(ims_data);
}

int veriquec_ims_manager_register(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	data->ims_data = g_try_new0(struct veriquec_ims_data, 1);
	if (data->ims_data == NULL) {
		return -EIO;
	}

	data->ims_data->path = path;
    data->ims_data->ims_request = IMS_REQ_INVALID;
	data->ims_data->ims_enabled = false;
	data->ims_data->ims_registered = false;
    data->ims_data->volte_available = false;

	if (!g_dbus_register_interface(conn, path, IMS_MANAGER_INTERFACE, ims_methods, ims_signals, NULL, data, ims_cleanup)) {
		ofono_error("Could not register %s interface under %s", IMS_MANAGER_INTERFACE, path);
		g_free(data->ims_data);
		return -EIO;
	}

	ofono_modem_add_interface(modem, IMS_MANAGER_INTERFACE);

	return 0;
}

static DBusMessage *modem_log_onoff(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = user_data;
	DBusMessage *reply;
	const char *member = dbus_message_get_member(msg);

	if (member == NULL) {
		DBG("Got NULL for member name for DebugLog method");
		return __ofono_error_failed(msg);
	}
	else if (strcmp(member, "ModemLogOn") == 0) {
		g_at_chat_send(data->app, "AT+QCFG=\"aprstlevel\", 0", NULL, NULL, NULL, NULL); // Upon modem crash, halt modem so that it is possible to take dump with QLog
		g_at_chat_send(data->app, "AT+QCFG=\"modemrstlevel\", 0", NULL, NULL, NULL, NULL);
		print_modem_log = true;
	}
	else if (strcmp(member, "ModemLogOff") == 0) {
		g_at_chat_send(data->app, "AT+QCFG=\"aprstlevel\", 1", NULL, NULL, NULL, NULL); // Upon modem crash, don't halt the modem. Just restart the modem
		g_at_chat_send(data->app, "AT+QCFG=\"modemrstlevel\", 1", NULL, NULL, NULL, NULL);
		print_modem_log = false;
	}
	else {
		DBG("Got unexpected member name for DebugLog method: %s", member);
		return __ofono_error_failed(msg);
	}

	reply = dbus_message_new_method_return(msg);

	if (reply == NULL) {
		DBG("Could not create dbus reply for DebugLog method: %s", member);
		reply = __ofono_error_failed(msg);
	}

	return reply;
}

static const GDBusMethodTable debug_level_methods[] = {
	{ GDBUS_METHOD("ModemLogOn", NULL, NULL, modem_log_onoff) },
	{ GDBUS_METHOD("ModemLogOff", NULL, NULL, modem_log_onoff) },
	{}
};

static int veriquec_debuglog_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	DBusConnection *conn = ofono_dbus_get_connection();
	const char *path = ofono_modem_get_path(modem);

	DBG("");

	/* Letting the default be to log modem communication, until there's a signal to turn
	   it on/off from the backend */
	print_modem_log = false;

	if (!g_dbus_register_interface(conn, path, DEBUG_LOGGING, debug_level_methods, NULL, NULL, data, NULL)) {
		ofono_error("Could not register %s interface under %s", DEBUG_LOGGING, path);
		return -EIO;
	}

	ofono_modem_add_interface(modem, DEBUG_LOGGING);
	return 0;
}

/* This function is called when the setting of FPLMN is done. */
static void set_crsm_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;

	DBG("Setting CRSM: OK: %d", ok);

	__ofono_dbus_pending_reply(&data->error->msg, data->error->reply);
}

static DBusMessage* set_fplmn_list(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = (struct veriquec_data *)user_data;
	DBusMessageIter iter;
	const char *fplmn;
	char buf[256];
	DBG("");
	if (!dbus_message_iter_init(msg, &iter))
		return __ofono_error_invalid_args(msg);

	if (dbus_message_iter_get_arg_type(&iter) != DBUS_TYPE_STRING)
		return __ofono_error_invalid_args(msg);

	dbus_message_iter_get_basic(&iter, &fplmn);

	data->error->msg = dbus_message_ref(msg);
	data->error->reply = dbus_message_new_method_return(data->error->msg);
	sprintf(buf,"AT+CRSM=214,28539,0,0,12,\"%s\"",fplmn);
	if (!g_at_chat_send(data->app, buf,	crsm_prefix, set_crsm_cb, data, NULL))
	{
		__ofono_error_failed(data->error->msg);
	}

	return NULL;
}
static void get_crsm_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = (struct veriquec_data *)user_data;
	const char *content;
	GAtResultIter iter;
	DBusMessageIter dbus_iter;

	DBG("Get fplmn list %s", ok ? "ok":"failed");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+CRSM:")) {
		return;
	}
;
	if (!g_at_result_iter_skip_next(&iter)) {
		DBG("Failed to skip integer 1 from CRSM message");
		__ofono_error_failed(data->error->msg);
		return;
	}

	if (!g_at_result_iter_skip_next(&iter)) {
		DBG("Failed to skip integer 2 from CRSM message");
		__ofono_error_failed(data->error->msg);
		return;
	}

	if (!g_at_result_iter_next_string(&iter, &content)) {
		DBG("Failed to parse string from CRSM message");
		content = NULL;
		__ofono_error_failed(data->error->msg);

		return;
	}
	dbus_message_iter_init_append(data->error->reply, &dbus_iter);

	dbus_message_iter_append_basic(&dbus_iter, DBUS_TYPE_STRING, &content);

	__ofono_dbus_pending_reply(&data->error->msg, data->error->reply);
}

static DBusMessage* get_fplmn_list(DBusConnection *conn, DBusMessage *msg, void *user_data)
{
	struct veriquec_data *data = (struct veriquec_data *)user_data;

	DBG("");

	if (data->error->msg != NULL) {
		return __ofono_error_busy(msg);
	}
	data->error->msg = dbus_message_ref(msg);
	data->error->reply = dbus_message_new_method_return(data->error->msg);

	if (!g_at_chat_send(data->app, "AT+CRSM=176,28539,0,0,12",	crsm_prefix, get_crsm_cb, data, NULL))
	{
		__ofono_error_failed(data->error->msg);
	}

	return NULL;
}

static const GDBusMethodTable veriquec_error_handling_methods[] = {
    { GDBUS_ASYNC_METHOD("SetFPLMNList", GDBUS_ARGS( {"list", "s"}), NULL, set_fplmn_list) },
    { GDBUS_ASYNC_METHOD("GetFPLMNList", NULL, GDBUS_ARGS( {"list", "s"}), get_fplmn_list) },
    { }
};

static const GDBusSignalTable veriquec_error_handling_signals[] = {
  { GDBUS_SIGNAL("CeerError", GDBUS_ARGS({ "operator", "s" }, { "reason", "i" }, { "cause", "i" })) },
  {}
};

struct get_operator_request
{
	struct veriquec_data *data;
	void (*cb)(struct verisure_error *error, const char *operator);
};


static void cops_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct get_operator_request *request = user_data;
	DBG("Get operator: OK: %d", ok);
	if (ok)
	{
		const char *operator = NULL;
		int mode;
		GAtResultIter iter;

		g_at_result_iter_init(&iter, result);
		if (!g_at_result_iter_next(&iter, "+COPS:"))
		{
			DBG("Failed to read operator\n");
			request->cb(request->data->error, NULL);
			return;
		}

		memset(request->data->error->operator, 0, 7);

		g_at_result_iter_next_number(&iter, &mode);
		if (mode == 2)
		{
			DBG("No operator\n");
			request->cb(request->data->error, NULL);
		}
		else
		{
			g_at_result_iter_skip_next(&iter);
			g_at_result_iter_next_string(&iter, &operator);
			g_at_result_iter_skip_next(&iter);

			request->cb(request->data->error, operator);
		}
	}
	else
	{
		DBG("Not ok");
		request->cb(request->data->error, NULL);
	}

	free(request);
}

static void qnwinfo_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct get_operator_request *request = user_data;
	static unsigned char operator_len;

	DBG("Get operator: OK: %d", ok);
	if (ok)
	{
		const char *operator = NULL;
		int mode;
		GAtResultIter iter;

		g_at_result_iter_init(&iter, result);
		if (!g_at_result_iter_next(&iter, "+QNWINFO:"))
		{
			DBG("Failed to read operator\n");
			request->cb(request->data->error, NULL);
			return;
		}

		memset(request->data->error->operator, 0, 7);
		operator_len = 0;

		g_at_result_iter_skip_next(&iter);
		g_at_result_iter_next_string(&iter, &operator);
		g_at_result_iter_skip_next(&iter);
		g_at_result_iter_skip_next(&iter);

		if(operator != NULL)
		{
			operator_len = strlen(operator);
			if(operator_len < 5)
			{
				memset(operator_tmp, 0, 7);
				memset(operator_tmp, '0', (5 - operator_len));
				strcat(operator_tmp, operator);
				operator = &operator_tmp[0];
			}
		}
		request->cb(request->data->error, operator);
	}
	else
	{
		DBG("Not ok");
		request->cb(request->data->error, NULL);
	}

	free(request);
}

static void cops_fmt_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct get_operator_request *request = user_data;
	DBG("");
	if(!ok)
	{
		DBG("Failed to set operator format\n");
		request->cb(request->data->error, NULL);
		free(request);
		return;
	}
	g_at_chat_send(request->data->mdm, "AT+COPS?", cops_prefix, cops_cb, request, NULL);
}

static void get_operator(void *user_data, void (*cb)(struct verisure_error *error, const char *operator))
{
	struct veriquec_data *data = user_data;
	DBG("");
	struct get_operator_request *request = malloc(sizeof(struct get_operator_request));

	if (request == NULL)
	{
		DBG("Failed to allocate memory for request\n");
		cb(data->error, NULL);
		return;
	}
	request->data = data;
	request->cb = cb;
	g_at_chat_send(data->mdm, "AT+QNWINFO", qnwinfo_prefix, qnwinfo_cb, request, NULL);
}

static void veriquec_error_handling_cleanup(void *user_data)
{
	struct veriquec_data *data = user_data;
	struct verisure_error *error_handling = data->error;

	g_free(error_handling);
}

static void sm_error_notify(GAtResult *result, gpointer user_data, bool app_channel)
{
	struct veriquec_data *data = user_data;
	const char *indicator_str;
	GAtResultIter iter;
	int cause;
	struct reject_signal reject_signal;
	g_at_result_iter_init(&iter, result);

	DBG("");

	if (!g_at_result_iter_next(&iter, "+SM ERROR: ")) {
		return;
	}


	if (!g_at_result_iter_next_number(&iter, &cause)) {
		DBG("Failed to parse cause group integer");
		return;
	}

	reject_signal.domain = REJECT_CAUSE_DOMAIN_PS;
	reject_signal.cause = cause;

	errorhandling_handle_error(reject_signal,data->error, data);

		// Request more info, for ofono logging purposes only
	GAtChat *channel = app_channel ? data->app : data->mdm;
	g_at_chat_send(channel, "AT+CEER", none_prefix, NULL, NULL, NULL);
}

static void mm_error_notify(GAtResult *result, gpointer user_data, bool app_channel)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int cause;
	struct reject_signal reject_signal;
	g_at_result_iter_init(&iter, result);

	DBG("");

	if (!g_at_result_iter_next(&iter, "+MM ERROR: ")) {
		return;
	}


	if (!g_at_result_iter_next_number(&iter, &cause)) {
		DBG("Failed to parse cause group integer from CIEV:ceer message");
		return;
	}

	reject_signal.domain = REJECT_CAUSE_DOMAIN_CS;
	reject_signal.cause = cause;

	errorhandling_handle_error(reject_signal,data->error, data);

		// Request more info, for ofono logging purposes only
	GAtChat *channel = app_channel ? data->app : data->mdm;
	g_at_chat_send(channel, "AT+CEER", none_prefix, NULL, NULL, NULL);
}

static void emm_error_notify(GAtResult *result, gpointer user_data, bool app_channel)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int cause;
	struct reject_signal reject_signal;
	g_at_result_iter_init(&iter, result);

	DBG("");

	if (!g_at_result_iter_next(&iter, "+EMM ERROR: ")) {
		return;
	}


	if (!g_at_result_iter_next_number(&iter, &cause)) {
		DBG("Failed to parse cause group integer from CIEV:ceer message");
		return;
	}

	reject_signal.domain = REJECT_CAUSE_DOMAIN_PS;
	reject_signal.cause = cause;

	errorhandling_handle_error(reject_signal,data->error, data);

		// Request more info, for ofono logging purposes only
	GAtChat *channel = app_channel ? data->app : data->mdm;
	g_at_chat_send(channel, "AT+CEER", none_prefix, NULL, NULL, NULL);
}

static void gmm_error_notify(GAtResult *result, gpointer user_data, bool app_channel)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int cause;
	struct reject_signal reject_signal;
	g_at_result_iter_init(&iter, result);

	DBG("");

	if (!g_at_result_iter_next(&iter, "+GMM ERROR: ")) {
		return;
	}


	if (!g_at_result_iter_next_number(&iter, &cause)) {
		DBG("Failed to parse cause group integer from CIEV:ceer message");
		return;
	}

	reject_signal.domain = REJECT_CAUSE_DOMAIN_CS;
	reject_signal.cause = cause;

	errorhandling_handle_error(reject_signal,data->error, data);

		// Request more info, for ofono logging purposes only
	GAtChat *channel = app_channel ? data->app : data->mdm;
	g_at_chat_send(channel, "AT+CEER", none_prefix, NULL, NULL, NULL);
}

static void qpdptrychk_handle(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char *str;
	int num1,num2;

	DBG("");

	if (!ok) {
		DBG("Failed to parse QPDPTRYCHK response");
		return;
	}

	g_at_result_iter_init(&iter, result);
	for (int i = 0; i < 4; i++) {
		if (!g_at_result_iter_next(&iter, "+QPDPTRYCHK:")) {
			return;
		}
		if (!g_at_result_iter_next_string(&iter, &str)) {
			return;
		}
		if (!g_at_result_iter_next_number(&iter, &num1)) {
			return;
		}
		if (!g_at_result_iter_next_number(&iter, &num2)) {
			return;
		}

		if (g_strcmp0(str, "F1") == 0) {
			if (num2 == f1_cfg_counter_setting) {
				DBG("Starting RPM mode cause F1. Duration: %d minutes", f1_cfg_time_duration_setting);
			}
		}
		if (g_strcmp0(str, "F2") == 0) {
			if (num2 == f2_cfg_counter_setting) {
				DBG("Starting RPM mode cause F2. Duration: %d minutes", f2_cfg_time_duration_setting);
			}
		}
		if (g_strcmp0(str, "F3") == 0) {
			if (num2 == f3_cfg_counter_setting) {
				DBG("Starting RPM mode cause F3. Duration: %d minutes", f3_cfg_time_duration_setting);
			}
		}
		if (g_strcmp0(str, "F4") == 0) {
			if (num2 == f4_cfg_counter_setting) {
				DBG("Starting RPM mode cause F4. Duration: %d minutes", f4_cfg_time_duration_setting);
			}
		}
	}
}

static void qpdptrycfg_handle(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char *str;
	int num1,num2,num3;

	DBG("");

	if (!ok) {
		DBG("Failed to parse QPDPTRYCFG response");
		return;
	}

	g_at_result_iter_init(&iter, result);
	for (int i = 0; i < 4; i++) {
		if (!g_at_result_iter_next(&iter, "+QPDPTRYCFG:")) {
			return;
		}
		if (!g_at_result_iter_next_string(&iter, &str)) {
			return;
		}
		if (!g_at_result_iter_next_number(&iter, &num1)) {
			return;
		}
		if (!g_at_result_iter_next_number(&iter, &num2)) {
			return;
		}
		if (!g_at_result_iter_next_number(&iter, &num3)) {
			return;
		}

		if (g_strcmp0(str, "F1") == 0) {
			f1_cfg_counter_setting = num3;
			f1_cfg_time_duration_setting = num2;
		}
		if (g_strcmp0(str, "F2") == 0) {
			f2_cfg_counter_setting = num3;
			f2_cfg_time_duration_setting = num2;
		}
		if (g_strcmp0(str, "F3") == 0) {
			f3_cfg_counter_setting = num3;
			f3_cfg_time_duration_setting = num2;
		}
		if (g_strcmp0(str, "F4") == 0) {
			f4_cfg_counter_setting = num3;
			f4_cfg_time_duration_setting = num2;
		}
	}
}

static void esm_error_notify(GAtResult *result, gpointer user_data, bool app_channel)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int domain;
	int cause;
	struct reject_signal reject_signal;
	g_at_result_iter_init(&iter, result);

	DBG("");

	if (!g_at_result_iter_next(&iter, "+ESM ERROR: ")) {
		return;
	}


	if (!g_at_result_iter_next_number(&iter, &domain)) {
		DBG("Failed to parse domain integer from CIEV:ceer message");
		return;
	}

	if (!g_at_result_iter_next_number(&iter, &cause)) {
		DBG("Failed to parse cause integer from CIEV:ceer message");
		return;
	}

	if (cause == 0) {
		DBG("Cause value 0 is not valid and can be disregarded");
		return;
	}

	reject_signal.domain = REJECT_CAUSE_DOMAIN_PS;
	reject_signal.cause = cause;

	errorhandling_handle_error(reject_signal,data->error, data);

		// Request more info, for ofono logging purposes only
	GAtChat *channel = app_channel ? data->app : data->mdm;
	g_at_chat_send(channel, "AT+CEER", none_prefix, NULL, NULL, NULL);

	if(cause == REJECT_CAUSE_OPERATOR_DETERMINED_BARRING ||
	   cause == REJECT_CAUSE_MISSING_OR_UNKNOWN_APN ||
	   cause == REJECT_CAUSE_UNKNOWN_PDN_TYPE ||
	   cause == REJECT_CAUSE_USER_AUTHENTICATION_OR_AUTHORIZATION_FAILED ||
	   cause == REJECT_CAUSE_REQUEST_REJECTED_BY_SERVING_GW_OR_PDN_GW ||
	   cause == REJECT_CAUSE_SERVICE_OPTION_NOT_SUPPORTED ||
	   cause == REJECT_CAUSE_REQUESTED_SERVICE_OPTION_NOT_SUBSCRIBED) {
		DBG("F2 reject cause detected. Cause: %d", cause);
		g_at_chat_send(channel, "AT+QPDPTRYCFG?", qpdptrycfg_prefix, qpdptrycfg_handle, NULL, NULL);
		g_at_chat_send(channel, "AT+QPDPTRYCHK?", qpdptrychk_prefix, qpdptrychk_handle, NULL, NULL);
	}

	if(cause == REJECT_CAUSE_NOT_AUTHORIZED_FOR_THIS_CSG ||
	   cause == REJECT_CAUSE_NON_EPS_AUTHENTICATION_UNACCEPTABLE ||
	   cause == REJECT_CAUSE_REQUEST_REJECTED_UNSPECIFIED ||
	   cause == REJECT_CAUSE_SERVICE_OPTION_TEMPORARILY_OUT_OF_ORDER ||
	   cause == REJECT_CAUSE_REQUESTED_SERVICE_OPTION_NOT_AUTHORIZED_IN_THIS_PLMN ||
	   cause == REJECT_CAUSE_NETWORK_FAILURE ||
	   cause == REJECT_CAUSE_PROTOCOL_ERROR_UNSPECIFIED) {
		DBG("F3 reject cause detected. Cause: %d", cause);
		g_at_chat_send(channel, "AT+QPDPTRYCFG?", qpdptrycfg_prefix, qpdptrycfg_handle, NULL, NULL);
		g_at_chat_send(channel, "AT+QPDPTRYCHK?", qpdptrychk_prefix, qpdptrychk_handle, NULL, NULL);
	}
}

static void emm_error_notify_app_cb(GAtResult *result, gpointer user_data) {
	emm_error_notify(result, user_data, true);
}

static void emm_error_notify_mdm_cb(GAtResult *result, gpointer user_data) {
	emm_error_notify(result, user_data, false);
}

static void gmm_error_notify_app_cb(GAtResult *result, gpointer user_data) {
	gmm_error_notify(result, user_data, true);
}

static void gmm_error_notify_mdm_cb(GAtResult *result, gpointer user_data) {
	gmm_error_notify(result, user_data, false);
}

static void esm_error_notify_app_cb(GAtResult *result, gpointer user_data) {
	esm_error_notify(result, user_data, true);
}

static void esm_error_notify_mdm_cb(GAtResult *result, gpointer user_data) {
	esm_error_notify(result, user_data, false);
}

static void mm_error_notify_app_cb(GAtResult *result, gpointer user_data) {
	mm_error_notify(result, user_data, false);
}

static void mm_error_notify_mdm_cb(GAtResult *result, gpointer user_data) {
	mm_error_notify(result, user_data, false);
}

static void sm_error_notify_app_cb(GAtResult *result, gpointer user_data) {
	sm_error_notify(result, user_data, false);
}

static void sm_error_notify_mdm_cb(GAtResult *result, gpointer user_data) {
	sm_error_notify(result, user_data, false);
}

static int veriquec_error_handling_enable(struct ofono_modem *modem)
{
  struct veriquec_data *data = ofono_modem_get_data(modem);
  DBusConnection *conn = ofono_dbus_get_connection();
  const char *path = ofono_modem_get_path(modem);

  DBG("");

  data->error = g_try_new0(struct verisure_error, 1);
  if (data->error == NULL) {
    return -EIO;
  }

  if (!g_dbus_register_interface(conn, path, ERROR_HANDLING_INTERFACE,
                                 veriquec_error_handling_methods, veriquec_error_handling_signals, NULL, data,
                                 veriquec_error_handling_cleanup)) {
    ofono_error("Could not register %s interface under %s",
                ERROR_HANDLING_INTERFACE,
                path);


    return -EIO;
  }

  ofono_modem_add_interface(modem, ERROR_HANDLING_INTERFACE);

	errorhandling_init(data->error, modem);
	data->error->get_operator = get_operator;

	g_at_chat_register(data->app, "+EMM ERROR:", emm_error_notify_app_cb, FALSE, data, NULL);
	g_at_chat_register(data->mdm, "+EMM ERROR:", emm_error_notify_mdm_cb, FALSE, data, NULL);
	g_at_chat_register(data->app, "+GMM ERROR:", gmm_error_notify_app_cb, FALSE, data, NULL);
	g_at_chat_register(data->mdm, "+GMM ERROR:", gmm_error_notify_mdm_cb, FALSE, data, NULL);
	g_at_chat_register(data->app, "+ESM ERROR:", esm_error_notify_app_cb, FALSE, data, NULL);
	g_at_chat_register(data->mdm, "+ESM ERROR:", esm_error_notify_mdm_cb, FALSE, data, NULL);
	g_at_chat_register(data->app, "+MM ERROR:", mm_error_notify_app_cb, FALSE, data, NULL);
	g_at_chat_register(data->mdm, "+MM ERROR:", mm_error_notify_mdm_cb, FALSE, data, NULL);
	g_at_chat_register(data->app, "+SM ERROR:", sm_error_notify_app_cb, FALSE, data, NULL);
	g_at_chat_register(data->mdm, "+SM ERROR:", sm_error_notify_mdm_cb, FALSE, data, NULL);

  return 0;
}

static void qmi_enable_cb(void *user_data)
{
	struct ofono_modem *modem = user_data;
	struct veriquec_data *data = ofono_modem_get_data(modem);
	struct ofono_gprs_context *gc = NULL;
	//We should never reach this if we do not have a qmi interface
	//we should do a system exit in veriquec_enable()
	DBG("");
	data->qmi_ready = true;
	qmi_device_set_expected_data_format(data->qmid, QMI_DEVICE_EXPECTED_DATA_FORMAT_RAW_IP);

	if (data->post_sim) {
		// We have valid sim card
		// an now the QMI daemon is also ready
		// so now we can create a data connection
		gc = ofono_gprs_context_create(modem, OFONO_VENDOR_QUECTEL_EC2X,
																	"qmimodem", data->qmid);

		if (data->gprs  && gc) {
			ofono_gprs_add_context(data->gprs, gc);
		}
	}

}

static int qmi_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	const char *device;
	int fd;
	struct serial_struct old, new;
	int DTR_flag = TIOCM_DTR;

	DBG("modem struct: %p", modem);

	device = ofono_modem_get_string(modem, "Device");
	if (!device)
		return -EINVAL;

	fd = open(device, O_RDWR | O_NONBLOCK | O_CLOEXEC);
	if (fd < 0)
		return -EINVAL;

	ioctl(fd, TIOCGSERIAL, &old);
	new = old;
	new.closing_wait = ASYNC_CLOSING_WAIT_NONE;
	ioctl(fd, TIOCSSERIAL, &new);
	ioctl(fd, TIOCMBIS, &DTR_flag);

	data->qmid = qmi_device_new(fd);
	if (!data->qmid) {
		close(fd);
		return -EINVAL;
	}

	qmi_device_set_close_on_unref(data->qmid, true);
	qmi_device_set_debug(data->qmid, veriquec_qmi_debug, "QMI: ");
	qmi_device_discover(data->qmid, qmi_enable_cb, modem, NULL);
	return 0;
}
static void apind_notify(GAtResult *result, gpointer user_data)
{
	struct ofono_modem *modem = user_data;
	GAtResultIter iter;
	const char *event;

	DBG("");

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+APIND:"))
		return;

	if (!g_at_result_iter_next_unquoted_string(&iter, &event))
		return;

	if (g_str_equal(event, "QMI READY")) {
		// This is only received once per power up of the modem
		// So for example at a flight mode toggle, we woun't get this signal
		struct veriquec_data *data = NULL;

        DBG("QMI ready setup");
        b_apind_qmi_ready_received = true;

		qmi_enable(modem);

        data = ofono_modem_get_data(modem);
        g_at_chat_send(data->app, "AT+QGMR?", NULL, veriquec_qgmr_cb, data, NULL);
	}
}

static void at_qdai_check(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int ind;
	int wanted_config[] = {3, 0, 1, 4, 0, 0, 1, 1};
	bool update = FALSE;

	DBG("");

	if (!ok)
		return;

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QDAI:"))
		return;

	for (int i = 0; i < (sizeof(wanted_config) / sizeof(int)); i++) {
		if (!g_at_result_iter_next_number(&iter, &ind)) {
			return;
		}
		if (ind != wanted_config[i]) {
			update = TRUE;
			break;
		}
	}

	if (update) {
		g_at_chat_send(data->mdm, "AT+QDAI=3,0,1,4,0,0,1,1", none_prefix, NULL, NULL, NULL);
		g_at_chat_send(data->mdm, "AT+QAPRDYIND=8", NULL, NULL, NULL, NULL); // Since this cmd only works sporadically,
																																				 // we add this here to be on the safer side

		// Unfortunately we need to reboot for this to take effect
		g_at_chat_send(data->mdm, "AT+CFUN=1,1", NULL, NULL, NULL, NULL);
	}
}

static void at_fplmn_backoff_time(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	const char *str;
	bool update = TRUE;

	DBG("");

	/* If ERROR is returned, the parameter is missing and needs to be set.
	   Then present, check that it has the correct value */
	if (ok) {
		g_at_result_iter_init(&iter, result);
		if (g_at_result_iter_next(&iter, "+QNVFR:")) {
			if (g_at_result_iter_next_unquoted_string(&iter, &str)) {
				if (g_strcmp0(str, "FFFFFFFF") == 0) {
					update = FALSE;
				}
			}
		}
	}

	if (update) {
		// Renable timer T3402, this needs to be done due to a bug i modem fw
		g_at_chat_send(data->app, "AT+QNVFW=\"/nv/item_files/modem/nas/lte_nas_temp_fplmn_backoff_time\",FFFFFFFF",
		               none_prefix, NULL, NULL, NULL);

		// Unfortunately we need to reboot for this to take effect
		g_at_chat_send(data->app, "AT+CFUN=1,1", none_prefix, NULL, NULL, NULL);
	}
}

static void at_qaprdyind_check(gboolean ok, GAtResult *result,
				gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int ind;

	DBG("");

	if (!ok)
		return;

	g_at_result_iter_init(&iter, result);

	if (!g_at_result_iter_next(&iter, "+QAPRDYIND:"))
		return;

	if (!g_at_result_iter_next_number(&iter, &ind))
		return;

    DBG("data->have_sim: %d, ind: %d", data->have_sim, ind);

	// Is it enabled?
	if (ind != CFG_VAL_QMI_READY) {
		// Otherwise enable it
		g_at_chat_send(data->mdm, "AT+QAPRDYIND=8", NULL, NULL, NULL, NULL);

		// Unfortunately we need to reboot for this to take effect
		g_at_chat_send(data->mdm, "AT+CFUN=1,1", NULL, NULL, NULL, NULL);
	}
}

static void dbgctl_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct veriquec_data *data = user_data;
	GAtResultIter iter;
	int debug_mode = 1;

	if (!ok) {
		return;
	}

	g_at_result_iter_init(&iter, result);
	if (!g_at_result_iter_next(&iter, "+QCFG:")) {
		return;
	}

	if (!g_at_result_iter_skip_next(&iter)) { // dbgctl
		return;
	}

	g_at_result_iter_next_number(&iter, &debug_mode);

	if (debug_mode == 1) {
		g_at_chat_send(data->mdm, "AT+QCFG=\"dbgctl\", 0", NULL, NULL, NULL, NULL);
	}
}

static int veriquec_enable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	const char *app, *mdm, *net, *qmi;

	DBG("%p", modem);

	app = ofono_modem_get_string(modem, "Aux");
	mdm = ofono_modem_get_string(modem, "Modem");
	qmi = ofono_modem_get_string(modem, "Device");

	if (app == NULL || mdm == NULL) {
		return -EINVAL;
	}

	/* Open devices */
	data->app = open_device(app, "App");
	if (data->app == NULL)
		return -EINVAL;

	/* The modem can take a while to wake up if just powered on. */
	g_at_chat_set_wakeup_command(data->app, "AT\r", 1000, 11000);

	// We want to use the other device to send SMS in case the first port is
	// busy at the time...
	data->mdm = open_device(mdm, "Mdm");

	if (data->mdm == NULL) {
		g_at_chat_unref(data->app);
		data->app = NULL;
		return -EINVAL;
	}

	if (!qmi) {
		//No qmi interface no point in continuing
		return -EINVAL;
	}

	data->qmi_ready = false;
	data->post_sim = false;
	reset_netreg_data(&data->netreg_data);
	reset_netreg_data(&__cached_netreg_data);


	g_at_chat_send(data->mdm, "ATE0", none_prefix,
					NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "AT&C0", none_prefix,
					NULL, NULL, NULL);

	g_at_chat_send(data->app, "ATE0", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->app, "AT+CMEE=1", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->app, "AT&C0", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "ATE0", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "AT+CMEE=1", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "AT&C0", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "AT+QCFG=\"dbgctl\"", qcfg_prefix, dbgctl_cb, data, NULL);

	// Power save
	g_at_chat_send(data->app, "AT+QSCLK=1", none_prefix, NULL, NULL, NULL);

	// Quectel specific configuration
	g_at_chat_send(data->mdm, "AT+QCFG=\"gprsattach\",1", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "AT+QCFG=\"urc_cause_support\",59", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->mdm, "AT+QURCCFG=\"urcport\",\"usbat\"", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->app, "AT+QCFG=\"cops_no_mode_change\",0", none_prefix, NULL, NULL, NULL);
	g_at_chat_send(data->app, "AT+QCFG=\"nwscanmode\", 0", none_prefix, NULL, NULL, NULL);

	// These settings will give a timeout = 10 seconds for SMS resending
	g_at_chat_send(data->mdm, "AT+QNVW=3532,0,\"05\"", none_prefix, NULL, NULL, NULL); // retry_period = 5 second
	g_at_chat_send(data->mdm, "AT+QNVW=3533,0,\"00\"", none_prefix, NULL, NULL, NULL); // retry_interval = 0 second

	g_at_chat_send(data->app, "AT+CFUN=4", none_prefix,
						cfun_enable, modem, NULL);

	g_at_chat_register(data->mdm, "+APIND:", apind_notify, FALSE, modem, NULL);

	veriquec_error_handling_enable(modem);
	return -EINPROGRESS;
}

static void veriquec_qpowd_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct ofono_modem *modem = user_data;
	struct veriquec_data *data = ofono_modem_get_data(modem);

	DBG("");

	g_at_chat_unref(data->mdm);
	data->mdm = NULL;
	g_at_chat_unref(data->app);
	data->app = NULL;

	if (ok)
		ofono_modem_set_powered(modem, FALSE);
}

static int veriquec_disable(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);

	DBG("%p", modem);

	g_dbus_remove_watch(ofono_dbus_get_connection(), data->netreg_watch);
	data->netreg_watch = 0;

	//veriquec_ceer_info_disable(modem);
	veriquec_unregister(modem);

	/* Shutdown the modem */
	g_at_chat_send(data->app, "AT+QPOWD=1", none_prefix, veriquec_qpowd_cb, modem, NULL);

	return -EINPROGRESS;
}

static void set_online_cb(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct cb_data *cbd = user_data;
	ofono_modem_online_cb_t cb = cbd->cb;
	struct ofono_error error;

	decode_at_error(&error, g_at_result_final_response(result));

	cb(&error, cbd->data);
}

static void veriquec_set_online(struct ofono_modem *modem, ofono_bool_t online,
		ofono_modem_online_cb_t cb, void *user_data)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	struct cb_data *cbd = cb_data_new(cb, user_data);
	char const *command = online ? "AT+CFUN=1" : "AT+CFUN=4";

	DBG("modem %p %s", modem, online ? "online" : "offline");

	if (g_at_chat_send(data->app, command, none_prefix,
					set_online_cb, cbd, g_free))
	{
		if(online) {
			g_at_chat_send(data->app, "AT+CSMS=1", none_prefix, NULL, NULL, NULL);
		}
		return;
	}

	CALLBACK_WITH_FAILURE(cb, cbd->data);

	g_free(cbd);
}

static void veriquec_pre_sim(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	struct ofono_sim *sim;

	DBG("%p", modem);

	ofono_devinfo_create(modem, 0, "atmodem", data->mdm);
	sim = ofono_sim_create(modem, OFONO_VENDOR_QUECTEL_EC2X,
							"atmodem", data->mdm);

	if (sim) {
		data->sim = sim;

		ofono_sim_inserted_notify(sim, data->have_sim);
		// Enable SIM detection URC
		g_at_chat_send(data->app, "AT+QSIMDET=1,1", none_prefix, NULL, NULL, NULL);
		g_at_chat_send(data->mdm, "AT+QSIMSTAT=1", none_prefix,
			sim_detect_enable_cb, data, NULL);
	}

	//Disable auto-activate MBN file
	g_at_chat_send(data->app, "AT+QMBNCFG=\"AutoSel\",0", none_prefix, NULL, NULL, NULL);

	//sms over IMS not allowed
	g_at_chat_send(data->app, "AT+QNVFR=\"/nv/item_files/modem/mmode/sms_domain_pref\",00", none_prefix, NULL, NULL, NULL);

	// Put UARTS in suspend mode, so that they can wake up in the test rigg
	// TODO Find similar functionality
	//g_at_chat_send(data->app, "AT^SPOW=2,1000,3", none_prefix, NULL, NULL, NULL);

	// Ofono might crash if these interfaces are called to early, so add them here
	veriquec_radio_policy_manager_enable(modem);
	veriquec_modem_info_enable(modem);
	veriquec_rssi_scan_enable(modem);
	veriquec_at_channel_enable(modem);
	veriquec_sim_refresh_enable(modem);
	veriquec_jam_detection_register(modem);
	// TODO Find similar functionality
	//veriquec_ceer_info_enable(modem);
	veriquec_debuglog_enable(modem);
	veriquec_ims_manager_register(modem);

	data->interface_registered = TRUE;

	g_at_chat_send(data->mdm, "AT+QAPRDYIND?", qaprdyind_prefix,
		at_qaprdyind_check, data, NULL);

	DBusConnection *conn = ofono_dbus_get_connection();
	data->netreg_watch = g_dbus_add_signal_watch(conn, OFONO_SERVICE,
								ofono_modem_get_path(modem), NETWORK_REGISTRATION,
								"PropertyChanged", netreg_changed, data, NULL);
}

static void veriquec_post_sim(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);

	DBG("%p", modem);

	data->post_sim = true;
	ofono_netreg_create(modem, OFONO_VENDOR_QUECTEL_EC2X,	"atmodem", data->mdm);
	ofono_sms_create(modem, OFONO_VENDOR_QUECTEL_EC2X, "atmodem", data->mdm);
	ofono_voicecall_create(modem, OFONO_VENDOR_QUECTEL_EC2X, "atmodem", data->mdm);
	ofono_netmon_create(modem, OFONO_VENDOR_QUECTEL_EC2X, "atmodem", data->mdm);
	data->gprs = ofono_gprs_create(modem, OFONO_VENDOR_QUECTEL_EC2X, "veriquecmodem", data->mdm);
	ofono_lte_create(modem, 0, "veriquecmodem", data->mdm);

	// Clear all PDN events (sometimes we can get old ones otherwise)
	g_at_chat_send(data->app, "AT+CGEREP=2,0", none_prefix, NULL, NULL, NULL);

	g_at_chat_send(data->mdm, "AT+QAPRDYIND?", qaprdyind_prefix,
		at_qaprdyind_check, data, NULL);

	//Enable URC reporting of - "IMS registration" and "IMS service" status
	g_at_chat_send(data->mdm, "AT+QIMSCFG=\"ims_status\",1,1", qimscfg_prefix,
		ims_reg_srv_status_urc_enable_cb, data, NULL);
}

static void veriquec_post_online(struct ofono_modem *modem)
{
	struct veriquec_data *data = ofono_modem_get_data(modem);
	struct ofono_gprs_context *gc = NULL;

	DBG("%p", modem);

	// Needs to be done late in the setup, otherwise this command will fail
	g_at_chat_send(data->mdm, "At+QDAI?", qdai_prefix, at_qdai_check, data, NULL);

	g_at_chat_send(data->app, "AT+QNVFR=\"/nv/item_files/modem/nas/lte_nas_temp_fplmn_backoff_time\"", qnvfr_prefix, at_fplmn_backoff_time, data, NULL);

	if (data->qmi_ready) {
		// The QMI daemon is ready and therefore go ahead and make the data connection
		gc = ofono_gprs_context_create(modem, OFONO_VENDOR_QUECTEL_EC2X, "qmimodem", data->qmid);
		if (data->gprs && gc) {
			ofono_gprs_add_context(data->gprs, gc);
		}
	}
}

static struct ofono_modem_driver veriquec_driver = {
	.name		= "veriquec",
	.probe		= veriquec_probe,
	.remove		= veriquec_remove,
	.enable		= veriquec_enable,
	.disable	= veriquec_disable,
	.set_online	= veriquec_set_online,
	.pre_sim	= veriquec_pre_sim,
	.post_sim	= veriquec_post_sim,
	.post_online	= veriquec_post_online,
};

static int veriquec_init(void)
{
	DBG("");
	return ofono_modem_driver_register(&veriquec_driver);
}

static void veriquec_exit(void)
{
	ofono_modem_driver_unregister(&veriquec_driver);
}

OFONO_PLUGIN_DEFINE(veriquec, "Quectel modem plugin", VERSION,
		OFONO_PLUGIN_PRIORITY_DEFAULT, veriquec_init, veriquec_exit)
