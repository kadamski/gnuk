#include "ch.h"
#include "hal.h"
#include "board.h"
#include "usb_lld.h"

static const uint8_t *
unique_device_id (void)
{
  /* STM32F103 has 96-bit unique device identifier */
  const uint8_t *addr = (const uint8_t *)0x1ffff7e8;

  return addr;
}

static void
usb_cable_config (int enable)
{
#if defined(SET_USB_CONDITION)
  if (SET_USB_CONDITION (enable))
    palSetPad (IOPORT_USB, GPIO_USB);
  else
    palClearPad (IOPORT_USB, GPIO_USB);
#else
  (void)enable;
#endif
}

static void
set_led (int on)
{
  if (SET_LED_CONDITION (on))
    palSetPad (IOPORT_LED, GPIO_LED);
  else
    palClearPad (IOPORT_LED, GPIO_LED);
}


#define FLASH_KEY1               0x45670123UL
#define FLASH_KEY2               0xCDEF89ABUL

static void
flash_unlock (void)
{
  FLASH->KEYR = FLASH_KEY1;
  FLASH->KEYR = FLASH_KEY2;
}


static int
flash_wait_for_last_operation (uint32_t timeout)
{
  int status;

  do
    {
      status = FLASH->SR;
      if (--timeout == 0)
	break;
    }
  while ((status & FLASH_SR_BSY) != 0);

  return status & (FLASH_SR_BSY|FLASH_SR_PGERR|FLASH_SR_WRPRTERR);
}

#define FLASH_PROGRAM_TIMEOUT 0x00010000
#define FLASH_ERASE_TIMEOUT   0x01000000

static int
flash_program_halfword (uint32_t addr, uint16_t data)
{
  int status;

  status = flash_wait_for_last_operation (FLASH_PROGRAM_TIMEOUT);

  port_disable ();
  if (status == 0)
    {
      FLASH->CR |= FLASH_CR_PG;

      *(volatile uint16_t *)addr = data;

      status = flash_wait_for_last_operation (FLASH_PROGRAM_TIMEOUT);
      FLASH->CR &= ~FLASH_CR_PG;
    }
  port_enable ();

  return status;
}

static int
flash_erase_page (uint32_t addr)
{
  int status;

  status = flash_wait_for_last_operation (FLASH_ERASE_TIMEOUT);

  port_disable ();
  if (status == 0)
    {
      FLASH->CR |= FLASH_CR_PER;
      FLASH->AR = addr; 
      FLASH->CR |= FLASH_CR_STRT;

      status = flash_wait_for_last_operation (FLASH_ERASE_TIMEOUT);
      FLASH->CR &= ~FLASH_CR_PER;
    }
  port_enable ();

  return status;
}

static int
flash_check_blank (const uint8_t *p_start, size_t size)
{
  const uint8_t *p;

  for (p = p_start; p < p_start + size; p++)
    if (*p != 0xff)
      return 0;

  return 1;
}

static int
flash_write (uint32_t dst_addr, const uint8_t *src, size_t len)
{
  int status;

  while (len)
    {
      uint16_t hw = *src++;

      hw |= (*src++ << 8);
      status = flash_program_halfword (dst_addr, hw);
      if (status != 0)
	return 0;		/* error return */

      dst_addr += 2;
      len -= 2;
    }

  return 1;
}

#define OPTION_BYTES_ADDR 0x1ffff800

static int
flash_protect (void)
{
  int status;
  uint32_t option_bytes_value;

  status = flash_wait_for_last_operation (FLASH_ERASE_TIMEOUT);

  port_disable ();
  if (status == 0)
    {
      FLASH->OPTKEYR = FLASH_KEY1;
      FLASH->OPTKEYR = FLASH_KEY2;

      FLASH->CR |= FLASH_CR_OPTER;
      FLASH->CR |= FLASH_CR_STRT;

      status = flash_wait_for_last_operation (FLASH_ERASE_TIMEOUT);
      FLASH->CR &= ~FLASH_CR_OPTER;
    }
  port_enable ();

  if (status != 0)
    return 0;

  option_bytes_value = *(uint32_t *)OPTION_BYTES_ADDR;
  return (option_bytes_value & 0xff) == 0xff ? 1 : 0;
}

#define FLASH_MASS_ERASE_TIMEOUT   0xF0000000

extern uint8_t __flash_start__, __flash_end__;
extern uint8_t _regnual_start;

static void __attribute__((naked))
flash_mass_erase_and_exec (void)
{
  void (**func )(void) = (void (**)(void))(&_regnual_start + 4);
  uint32_t addr = (uint32_t)&__flash_start__;
  uint32_t end = (uint32_t)&__flash_end__;
  int r;

  while (addr < end)
    {
      r = flash_erase_page (addr);
      if (r != 0)
	break;

      addr += FLASH_PAGE_SIZE;
    }

  if (addr >= end)
    (**func) ();

  for (;;);
}

static void
nvic_enable_vector (uint32_t n, uint32_t prio)
{
  unsigned int sh = (n & 3) << 3;

  NVIC_IPR (n >> 2) = (NVIC_IPR(n >> 2) & ~(0xFF << sh)) | (prio << sh);
  NVIC_ICPR (n >> 5) = 1 << (n & 0x1F);
  NVIC_ISER (n >> 5) = 1 << (n & 0x1F);
}

static void
usb_lld_sys_init (void)
{
  RCC->APB1ENR |= RCC_APB1ENR_USBEN;
  nvic_enable_vector (USB_LP_CAN1_RX0_IRQn,
		      CORTEX_PRIORITY_MASK (STM32_USB_IRQ_PRIORITY));
  /*
   * Note that we also have other IRQ(s):
   * 	USB_HP_CAN1_TX_IRQn (for double-buffered or isochronous)
   * 	USBWakeUp_IRQn (suspend/resume)
   */
  RCC->APB1RSTR = RCC_APB1RSTR_USBRST;
  RCC->APB1RSTR = 0;

  usb_cable_config (1);
}

static void
usb_lld_sys_shutdown (void)
{
  RCC->APB1ENR &= ~RCC_APB1ENR_USBEN;
  usb_cable_config (0);
}

#define SYSRESETREQ 0x04
static void
nvic_system_reset (void)
{
  SCB->AIRCR = (0x05FA0000 | (SCB->AIRCR & 0x70) | SYSRESETREQ);
  asm volatile ("dsb");
}

static void __attribute__ ((naked))
reset (void)
{
  asm volatile ("cpsid	i\n\t"		/* Mask all interrupts            */
		"ldr	r0, =_text\n\t"
		"ldr	r1, [r0], #4\n\t"
		"msr	MSP, r1\n\t"	/* Main (exception handler) stack */
		"ldr	r1, [r0]\n\t"	/* Reset handler                  */
		"bx	r1\n"
		: /* no output */ : /* no input */ : "memory");
}

typedef void (*handler)(void);
extern uint8_t __ram_end__;

handler vector[] __attribute__ ((section(".vectors"))) = {
  (handler)&__ram_end__,
  reset,
  (handler)unique_device_id,
  (handler)set_led,
  flash_unlock,
  (handler)flash_program_halfword,
  (handler)flash_erase_page,
  (handler)flash_check_blank,
  (handler)flash_write,
  (handler)flash_protect,
  (handler)flash_mass_erase_and_exec,
  usb_lld_sys_init,
  usb_lld_sys_shutdown,
  nvic_system_reset,
};
