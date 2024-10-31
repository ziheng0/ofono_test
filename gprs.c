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

static void gprs_initialized(gboolean ok, GAtResult *result, gpointer user_data)
{
	struct ofono_gprs *gprs = user_data;
	struct gprs_data *gd = ofono_gprs_get_data(gprs);

	DBG("");

	g_at_chat_register(gd->chat, "+CEREG:", cereg_notify, FALSE, gprs, NULL);
	g_at_chat_register(gd->chat, "+CGEV:", cgev_notify, FALSE, gprs, NULL);
	g_at_chat_register(gd->chat, "+CGREG:", cgreg_notify, FALSE, gprs, NULL);

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
