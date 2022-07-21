/* USB buffer memory definition and number of string descriptors */

#ifndef __USB_CONF_H
#define __USB_CONF_H

#define CCID_NUM_INTERFACES 1
#define CCID_INTERFACE 0
#define NUM_INTERFACES CCID_NUM_INTERFACES

#if defined(USB_SELF_POWERED)
#define USB_INITIAL_FEATURE 0xC0   /* bmAttributes: self powered */
#else
#define USB_INITIAL_FEATURE 0x80   /* bmAttributes: bus powered */
#endif

/* Control pipe */
/* EP0: 64-byte, 64-byte  */
#define ENDP0_RXADDR        (0x40)
#define ENDP0_TXADDR        (0x80)

/* CCID/ICCD BULK_IN, BULK_OUT */
/* EP1: 64-byte, 64-byte */
#define ENDP1_TXADDR        (0xc0)
#define ENDP1_RXADDR        (0x100)
/* EP2: INTR_IN: 4-byte */
#define ENDP2_TXADDR        (0x140)

/* 0x144 */
#endif /* __USB_CONF_H */
