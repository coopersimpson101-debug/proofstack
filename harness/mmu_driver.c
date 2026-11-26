/* Host driver for orbit-os kernel/mm/mmu.c.
 *
 * build.py compiles this file with the orbit-os kernel/arch/aarch64/mmu.c #included verbatim
 * (linked with the portable kernel/lib/a64pt.c it calls) except for its three inline-asm statements (TLB/I-cache maintenance and the AT S1E1R probe), which cannot be
 * assembled for the host and do not touch the page tables. System-register accessors come
 * from harness/stubs/arch.h; linker-script symbols and `plat` are set at run time.
 *
 * The page tables live in mmu.c's own static pool and are walked here in software exactly as
 * the stage-1 4 KiB-granule walk does (L0..L3, table/block/page descriptors).
 *
 * Commands (hex numbers), one per line:
 *   reset                         empty pool, fresh L0 table as "lo" root
 *   map VA PA SIZE PROT           map_range(lo, VA, PA, SIZE, PROT)
 *   layout KS UTS UTE TE RE USS USE END RAMB RAMS DEVB DEVS DTB DTBS
 *                                 set linker symbols + plat, then run mmu_init()
 *   dump ROOT LO HI               ROOT = lo|hi; print runs of mapped 4 KiB pages in [LO, HI):
 *                                 "VA PA NPAGES ATTRS" (contiguous VA->PA, same attributes)
 *   query ROOT VA                 "VA PA ATTRS" or "VA fault" for one address
 *   tables                        number of page tables used
 *   prot NAME                     print the PROT_* constant NAME (KDATA, KTEXT, ...)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t hs_sym[8];
struct platform;

#include "mmu_stripped.c"

struct platform plat;

void panic(const char *fmt, ...)
{
    printf("PANIC %s\n", fmt);
    fflush(stdout);
    exit(3);
}

void *k_memset(void *dst, int c, size_t n) { return memset(dst, c, n); }
void *kmalloc(size_t n) { return malloc(n); }
void kfree(void *p) { free(p); }
void kprintf(const char *fmt, ...) { (void)fmt; }

#define DESC_ATTRS (~PTE_ADDR_MASK & ~3ULL)
#define DRV_4K 0x1000ULL
#define DRV_2M 0x200000ULL

/* returns 1 and sets pa and attrs if va is mapped through root */
static int walk(const uint64_t *root, uint64_t va, uint64_t *pa, uint64_t *attrs)
{
    const uint64_t *t = root;
    for (int level = 0; level < 4; level++) {
        unsigned shift = 39 - 9 * level;
        uint64_t d = t[(va >> shift) & 511];
        if (!(d & PTE_VALID))
            return 0;
        if (level == 3) {
            if (!(d & PTE_TABLE))
                return 0; /* reserved encoding at L3 */
            *pa = (d & PTE_ADDR_MASK) | (va & 0xfff);
            *attrs = d & DESC_ATTRS;
            return 1;
        }
        if (!(d & PTE_TABLE)) {
            if (level != 2)
                return 0; /* this code never makes L0/L1 blocks */
            *pa = (d & PTE_ADDR_MASK & ~(DRV_2M - 1)) | (va & (DRV_2M - 1));
            *attrs = d & DESC_ATTRS;
            return 1;
        }
        t = (const uint64_t *)(uintptr_t)(d & PTE_ADDR_MASK);
    }
    return 0;
}

static void dump(const uint64_t *root, uint64_t lo, uint64_t hi)
{
    uint64_t rva = 0, rpa = 0, rn = 0, rat = 0;
    for (uint64_t va = lo; va < hi; va += DRV_4K) {
        uint64_t pa, at;
        if (walk(root, va, &pa, &at)) {
            if (rn && va == rva + rn * DRV_4K && pa == rpa + rn * DRV_4K && at == rat) {
                rn++;
                continue;
            }
            if (rn)
                printf("%llx %llx %llx %llx\n", (unsigned long long)rva, (unsigned long long)rpa,
                       (unsigned long long)rn, (unsigned long long)rat);
            rva = va, rpa = pa, rn = 1, rat = at;
        }
        if (va + DRV_4K < va)
            break;
    }
    if (rn)
        printf("%llx %llx %llx %llx\n", (unsigned long long)rva, (unsigned long long)rpa,
               (unsigned long long)rn, (unsigned long long)rat);
    puts("end");
}

int main(void)
{
    char line[512];
    while (fgets(line, sizeof line, stdin)) {
        unsigned long long a[14];
        char name[16];
        if (strncmp(line, "reset", 5) == 0) {
            pt_used = 0;
            l0_lo = alloc_table();
            l0_hi = alloc_table();
            puts("ok");
        } else if (sscanf(line, "map %llx %llx %llx %llx", &a[0], &a[1], &a[2], &a[3]) == 4) {
            map_range(l0_lo, a[0], a[1], a[2], a[3]);
            puts("ok");
        } else if (sscanf(line, "layout %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx %llx",
                          &a[0], &a[1], &a[2], &a[3], &a[4], &a[5], &a[6], &a[7], &a[8], &a[9],
                          &a[10], &a[11], &a[12], &a[13]) == 14) {
            for (int k = 0; k < 8; k++)
                hs_sym[k] = a[k];
            memset(&plat, 0, sizeof plat);
            plat.ram_base = a[8];
            plat.ram_size = a[9];
            plat.dev_base = a[10];
            plat.dev_size = a[11];
            plat.dtb = (const void *)(uintptr_t)a[12];
            plat.dtb_size = (uint32_t)a[13];
            pt_used = 0;
            mmu_init();
            puts("ok");
        } else if (sscanf(line, "dump lo %llx %llx", &a[0], &a[1]) == 2) {
            dump(l0_lo, a[0], a[1]);
        } else if (sscanf(line, "dump hi %llx %llx", &a[0], &a[1]) == 2) {
            dump(l0_hi, a[0], a[1]);
        } else if (sscanf(line, "query %15s %llx", name, &a[0]) == 2) {
            uint64_t pa, at;
            const uint64_t *root = strcmp(name, "hi") == 0 ? l0_hi : l0_lo;
            if (walk(root, a[0], &pa, &at))
                printf("%llx %llx %llx\n", a[0], (unsigned long long)pa, (unsigned long long)at);
            else
                printf("%llx fault\n", a[0]);
        } else if (strncmp(line, "tables", 6) == 0) {
            printf("%lu\n", (unsigned long)pt_used);
        } else if (sscanf(line, "prot %15s", name) == 1) {
            uint64_t v = !strcmp(name, "KDATA") ? PROT_KDATA : !strcmp(name, "KTEXT") ? PROT_KTEXT
                       : !strcmp(name, "KRO") ? PROT_KRO : !strcmp(name, "UTEXT") ? PROT_UTEXT
                       : !strcmp(name, "UDATA") ? PROT_UDATA : !strcmp(name, "DEVICE") ? PROT_DEVICE : 0;
            printf("%llx\n", (unsigned long long)v);
        } else {
            fprintf(stderr, "bad command: %s", line);
            return 2;
        }
        fflush(stdout);
    }
    return 0;
}
