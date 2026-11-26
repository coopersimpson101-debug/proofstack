/* Host driver for orbit-os kernel/mm/buddy.c (compiled unmodified, with zig cc).
 *
 * Reads one command per line on stdin and prints one result line per command:
 *   init N        -> "ok"                      buddy_init over N pages
 *   add I N       -> "ok"                      buddy_add_range(base + I*4K, N pages)
 *   alloc O       -> "<page index>" | "-1"     buddy_alloc(order O)
 *   free I        -> "0" | "-1"                buddy_free(base + I*4K)
 *   state         -> "<free_pages> <nfree[0]> ... <nfree[10]> <buddy_check>"
 * The Lean model (`orbitmodel buddy`) speaks the same protocol, so a Python driver can feed
 * both the same random sequence and compare every line. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "buddy.h"

#define MAXPAGES 4096

static struct buddy b;
static uint8_t meta[MAXPAGES];
static uintptr_t base;

int main(void)
{
    char line[128];
    char *raw = malloc((MAXPAGES + 1) * PAGE_SIZE);
    if (!raw)
        return 2;
    base = ((uintptr_t)raw + PAGE_SIZE - 1) & ~(uintptr_t)(PAGE_SIZE - 1);
    while (fgets(line, sizeof line, stdin)) {
        unsigned long a = 0, c = 0;
        if (sscanf(line, "init %lu", &a) == 1) {
            if (a > MAXPAGES)
                a = MAXPAGES;
            buddy_init(&b, base, a, meta);
            puts("ok");
        } else if (sscanf(line, "add %lu %lu", &a, &c) == 2) {
            buddy_add_range(&b, base + a * PAGE_SIZE, c);
            puts("ok");
        } else if (sscanf(line, "alloc %lu", &a) == 1) {
            void *p = buddy_alloc(&b, (unsigned)a);
            if (p)
                printf("%lu\n", (unsigned long)(((uintptr_t)p - base) / PAGE_SIZE));
            else
                puts("-1");
        } else if (sscanf(line, "free %lu", &a) == 1) {
            printf("%d\n", buddy_free(&b, (void *)(base + a * PAGE_SIZE)));
        } else if (strncmp(line, "state", 5) == 0) {
            printf("%lu", (unsigned long)buddy_free_pages(&b));
            for (int o = 0; o < BUDDY_ORDERS; o++)
                printf(" %lu", (unsigned long)b.nfree[o]);
            printf(" %d\n", buddy_check(&b));
        } else {
            fprintf(stderr, "bad command: %s", line);
            return 2;
        }
        fflush(stdout);
    }
    return 0;
}
