/*
 * usb_ctrl.c - USB control pipe device specific code for Gnuk
 *
 * Copyright (C) 2010, 2011, 2012, 2013, 2015, 2016, 2017, 2018,
 *               2022
 *               Free Software Initiative of Japan
 * Author: NIIBE Yutaka <gniibe@fsij.org>
 *
 * This file is a part of Gnuk, a GnuPG USB Token implementation.
 *
 * Gnuk is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Gnuk is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
 * License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 */

/* Packet size of USB Bulk transfer for full speed */
#define GNUK_MAX_PACKET_SIZE 64

#include <stdint.h>
#include <string.h>
#include <chopstx.h>

#include "config.h"

#include "usb_lld.h"
#include "usb_conf.h"
#include "gnuk.h"
#include "neug.h"

uint32_t bDeviceState = USB_DEVICE_STATE_UNCONNECTED;

static void
gnuk_setup_endpoints_for_interface (struct usb_dev *dev,
				    uint16_t interface, int stop)
{
#if !defined(GNU_LINUX_EMULATION)
  (void)dev;
#endif

  if (interface == CCID_INTERFACE)
    {
      if (!stop)
	{
#ifdef GNU_LINUX_EMULATION
	  usb_lld_setup_endp (dev, ENDP1, 1, 1);
	  usb_lld_setup_endp (dev, ENDP2, 0, 1);
#else
	  usb_lld_setup_endpoint (ENDP1, EP_BULK, 0, ENDP1_RXADDR,
				  ENDP1_TXADDR, GNUK_MAX_PACKET_SIZE);
	  usb_lld_setup_endpoint (ENDP2, EP_INTERRUPT, 0, 0, ENDP2_TXADDR, 0);
#endif
	}
      else
	{
	  usb_lld_stall_rx (ENDP1);
	  usb_lld_stall_tx (ENDP1);
	  usb_lld_stall_tx (ENDP2);
	}
    }
}

void
usb_device_reset (struct usb_dev *dev)
{
  usb_lld_reset (dev, USB_INITIAL_FEATURE);

  /* Initialize Endpoint 0 */
#ifdef GNU_LINUX_EMULATION
  usb_lld_setup_endp (dev, ENDP0, 1, 1);
#else
  usb_lld_setup_endpoint (ENDP0, EP_CONTROL, 0, ENDP0_RXADDR, ENDP0_TXADDR,
			  64);
#endif

  bDeviceState = USB_DEVICE_STATE_DEFAULT;
}

#define USB_CCID_REQ_ABORT			0x01
#define USB_CCID_REQ_GET_CLOCK_FREQUENCIES	0x02
#define USB_CCID_REQ_GET_DATA_RATES		0x03

static const uint8_t freq_table[] = { 0xa0, 0x0f, 0, 0, }; /* dwDefaultClock */
static const uint8_t data_rate_table[] = { 0x80, 0x25, 0, 0, }; /* dwDataRate */

#ifdef FLASH_UPGRADE_SUPPORT
static const uint8_t *const mem_info[] = { _regnual_start,  __heap_end__, };
#endif

#define USB_FSIJ_GNUK_MEMINFO     0
#define USB_FSIJ_GNUK_DOWNLOAD    1
#define USB_FSIJ_GNUK_EXEC        2
#define USB_FSIJ_GNUK_CARD_CHANGE 3

#ifdef FLASH_UPGRADE_SUPPORT
/* After calling this function, CRC module remain enabled.  */
static int
download_check_crc32 (struct usb_dev *dev, const uint32_t *end_p)
{
  uint32_t crc32 = *end_p;
  const uint32_t *p;

  crc32_rv_reset ();

  for (p = (const uint32_t *)&_regnual_start; p < end_p; p++)
    crc32_rv_step (rbit (*p));

  if ((rbit (crc32_rv_get ()) ^ crc32) == 0xffffffff)
    return usb_lld_ctrl_ack (dev);

  return -1;
}
#endif

int
usb_setup (struct usb_dev *dev)
{
  struct device_req *arg = &dev->dev_req;
  uint8_t type_rcp = arg->type & (REQUEST_TYPE|RECIPIENT);

  if (type_rcp == (VENDOR_REQUEST | DEVICE_RECIPIENT))
    {
      if (USB_SETUP_GET (arg->type))
	{
#ifdef FLASH_UPGRADE_SUPPORT
	  if (arg->request == USB_FSIJ_GNUK_MEMINFO)
	    return usb_lld_ctrl_send (dev, mem_info, sizeof (mem_info));
#else
	  return -1;
#endif
	}
      else /* SETUP_SET */
	{
#ifdef FLASH_UPGRADE_SUPPORT
	  uint8_t *addr = sram_address ((arg->value * 0x100) + arg->index);
#endif

	  if (arg->request == USB_FSIJ_GNUK_DOWNLOAD)
	    {
#ifdef FLASH_UPGRADE_SUPPORT
	      if (ccid_get_ccid_state () != CCID_STATE_EXITED)
		return -1;

	      if (addr < _regnual_start || addr + arg->len > __heap_end__)
		return -1;

	      if (arg->index + arg->len < 256)
		memset (addr + arg->index + arg->len, 0,
			256 - (arg->index + arg->len));

	      return usb_lld_ctrl_recv (dev, addr, arg->len);
#else
	      return -1;
#endif
	    }
	  else if (arg->request == USB_FSIJ_GNUK_EXEC && arg->len == 0)
	    {
#ifdef FLASH_UPGRADE_SUPPORT
	      if (ccid_get_ccid_state () != CCID_STATE_EXITED)
		return -1;

	      if (((uintptr_t)addr & 0x03))
		return -1;

	      return download_check_crc32 (dev, (uint32_t *)addr);
#else
	      return -1;
#endif
	    }
	  else if (arg->request == USB_FSIJ_GNUK_CARD_CHANGE && arg->len == 0)
	    {
	      if (arg->value != 0 && arg->value != 1 && arg->value != 2)
		return -1;

	      ccid_card_change_signal (arg->value);
	      return usb_lld_ctrl_ack (dev);
	    }
	}
    }
  else if (type_rcp == (CLASS_REQUEST | INTERFACE_RECIPIENT))
    {
      if (arg->index == CCID_INTERFACE)
	{
	  if (USB_SETUP_GET (arg->type))
	    {
	      if (arg->request == USB_CCID_REQ_GET_CLOCK_FREQUENCIES)
		return usb_lld_ctrl_send (dev, freq_table, sizeof (freq_table));
	      else if (arg->request == USB_CCID_REQ_GET_DATA_RATES)
		return usb_lld_ctrl_send (dev, data_rate_table,
					  sizeof (data_rate_table));
	    }
	  else
	    {
	      if (arg->request == USB_CCID_REQ_ABORT)
		/* wValue: bSeq, bSlot */
		/* Abortion is not supported in Gnuk */
		return -1;
	    }
	}
    }

  return -1;
}


void
usb_ctrl_write_finish (struct usb_dev *dev)
{
  struct device_req *arg = &dev->dev_req;
  uint8_t type_rcp = arg->type & (REQUEST_TYPE|RECIPIENT);

  if (type_rcp == (VENDOR_REQUEST | DEVICE_RECIPIENT))
    {
      if (USB_SETUP_SET (arg->type) && arg->request == USB_FSIJ_GNUK_EXEC)
	{
	  if (ccid_get_ccid_state () != CCID_STATE_EXITED)
	    return;

	  bDeviceState = USB_DEVICE_STATE_UNCONNECTED;
	  usb_lld_prepare_shutdown (); /* No further USB communication */
	  led_blink (LED_GNUK_EXEC);	/* Notify the main.  */
	}
    }
}


int
usb_set_configuration (struct usb_dev *dev)
{
  int i;
  uint8_t current_conf;

  current_conf = usb_lld_current_configuration (dev);
  if (current_conf == 0)
    {
      if (dev->dev_req.value != 1)
	return -1;

      usb_lld_set_configuration (dev, 1);
      for (i = 0; i < NUM_INTERFACES; i++)
	gnuk_setup_endpoints_for_interface (dev, i, 0);
      bDeviceState = USB_DEVICE_STATE_CONFIGURED;
    }
  else if (current_conf != dev->dev_req.value)
    {
      if (dev->dev_req.value != 0)
	return -1;

      usb_lld_set_configuration (dev, 0);
      for (i = 0; i < NUM_INTERFACES; i++)
	gnuk_setup_endpoints_for_interface (dev, i, 1);
      bDeviceState = USB_DEVICE_STATE_ADDRESSED;
    }

  /* Do nothing when current_conf == value */
  return usb_lld_ctrl_ack (dev);
}


int
usb_set_interface (struct usb_dev *dev)
{
  uint16_t interface = dev->dev_req.index;
  uint16_t alt = dev->dev_req.value;

  if (interface >= NUM_INTERFACES)
    return -1;

  if (alt != 0)
    return -1;
  else
    {
      gnuk_setup_endpoints_for_interface (dev, interface, 0);
      return usb_lld_ctrl_ack (dev);
    }
}


int
usb_get_interface (struct usb_dev *dev)
{
  const uint8_t zero = 0;
  uint16_t interface = dev->dev_req.index;

  if (interface >= NUM_INTERFACES)
    return -1;

  return usb_lld_ctrl_send (dev, &zero, 1);
}

int
usb_get_status_interface (struct usb_dev *dev)
{
  const uint16_t status_info = 0;
  uint16_t interface = dev->dev_req.index;

  if (interface >= NUM_INTERFACES)
    return -1;

  return usb_lld_ctrl_send (dev, &status_info, 2);
}
