/* Host stand-in for orbit-os kernel/include/arch.h: system-register accesses and barriers
 * have no effect on the page tables, so they are no-ops here (reads return 0). */
#ifndef ORBIT_ARCH_H
#define ORBIT_ARCH_H
#include <stdint.h>
#define read_sysreg(r) ((uint64_t)0)
#define write_sysreg(r, v) ((void)(v))
static inline void isb(void) {}
static inline void dsb_sy(void) {}
static inline void dsb_ish(void) {}
static inline uint64_t irq_save(void) { return 0; }
static inline void irq_restore(uint64_t f) { (void)f; }
#endif
