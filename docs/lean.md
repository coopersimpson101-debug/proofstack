# Lean proofs for orbit-os: what is proved, what is tested

Lean 4.35.0, no Mathlib, no `sorry` / `admit` / `native_decide`; `results/lean_axioms.txt` lists
the axioms the headline theorems depend on (only Lean's standard `propext`, `Classical.choice`,
`Quot.sound`). The code under verification is orbit-os
`1a8385b07ccd95ecef07be80a916c75073fb171e` (merged into orbit-os main for its v0.2.0 release, which fixes the
two bugs below): `kernel/mm/buddy.c`, `kernel/lib/a64pt.c` (the page-table builder, moved out of
`kernel/arch/aarch64/mmu.c` by that commit) and `mmu_init` in `mmu.c`. The bugs were found on
`main` at `ba8bac1`; the original algorithms stay in the model as `addRangeV1` / `mapRangeV1`, with
the theorems that exhibit the bugs.

## Buddy allocator (`lean/OrbitProofs/Buddy.lean`)

**Model.** Page indices relative to `b->base`. The C free lists `free[0..10]` are one list of
blocks appended at the end, so `free[o]` is `free.filter (·.ord = o)` in the same order and
`buddy_alloc` takes the first block of the smallest non-empty order, exactly like
`b->free[o].next`. `meta[i] == FREE|o` is "`⟨i,o⟩` is in the free list", `meta[i] & ALLOC` is "a
block with index `i` is allocated", the buddy is computed arithmetically (equal to `i ^ (1<<o)` for
aligned `i`), and `free_pages` / `managed_pages` are explicit counters.

**Invariant `Inv`.** Every free or allocated block is naturally aligned, of order `< 11` and inside
the span; all blocks are pairwise disjoint; `freePages` is the sum of free block sizes; no free
block has its buddy free at the same order (complete coalescing); and
`managed = freePages + allocated pages`.

| theorem | statement (informally) |
|---|---|
| `init_inv` | `buddy_init` establishes `Inv` |
| `addRange_inv` | `buddy_add_range` of **any** range preserves `Inv` (incl. `managed` accounting): pages already in a free or allocated block are skipped. No hypothesis; the original algorithm needed a non-overlap hypothesis (`addRangeV1_inv`) |
| `candidate_disj`, `shrink_spec` | the fixed loop's candidate block (start not inside a block, no block head inside it) is disjoint from every block |
| `alloc_inv` | `buddy_alloc` preserves `Inv` (split loop: upper halves become free blocks) |
| `free_inv` | `buddy_free` preserves `Inv` (coalescing loop) |
| `alloc_some`, `alloc_aligned` | a returned block of order `o` starts at a multiple of `2^o`, lies inside the span and is recorded as allocated |
| `no_overlap` | under `Inv` two different allocated blocks share no page (nor does an allocated and a free block) |
| `free_reject` | freeing an index that heads no allocated block (double / wild free) returns -1 and changes nothing |
| `alloc_free_roundtrip` | `free(alloc(s, o))` succeeds and restores the free lists (up to order within a list), the allocation set and both counters |
| `bug_state_free`, `bug_breaks_invariant`, `bug_double_allocation` | the overlapping-add bug on `addRangeV1`, below |
| `fixed_state_free`, `fixed_no_double_allocation` | the same sequence on the fixed `addRange`: 4 free pages, one order-2 block, no second allocation |

### Bug found: overlapping `buddy_add_range` double-manages pages (fixed in orbit-os `1a8385b` (merged into orbit-os main for its v0.2.0 release))

`buddy_add_range`'s comment says overlapping adds are skipped ("already managed"), but the check
only looks at the metadata byte of each candidate block's *head* page. A range that starts inside a
free block passes, so its pages are inserted a second time. After `add(0, 4)` and `add(1, 1)` on a
4-page span there are 5 free pages, `buddy_check()` still returns 0, and `alloc(0)` → page 1 and
`alloc(2)` → pages 0–3 are two live allocations sharing page 1. The Lean theorems state exactly this
for the model (`addRangeV1`); at orbit-os `ba8bac1` the differential test showed the C code does
the same, and random overlapping adds made the C driver crash on its corrupted intrusive lists.
`mm_init` only adds the disjoint holes between sorted reserved ranges, so the kernel does not hit
this today — it was a latent API bug.

**Fix** (orbit-os `1a8385b` (merged into orbit-os main for its v0.2.0 release)): `buddy_add_range` skips a page that lies inside a managed block
(found from the naturally aligned candidate head at each order), and shrinks a candidate block
while some block head lies inside it. A candidate that starts in no block and contains no block
head overlaps no block, which is what lets `addRange_inv` drop its hypothesis. Regression tests:
orbit-os `tests/test_buddy.c` (the 4-page counterexample and 200 random overlapping rounds checked
against a page bitmap) and proofstack `test_overlapping_add_range_fixed` /
`test_overlapping_add_sequences_agree` (C and Lean agree line by line on overlapping sessions).

## Page tables (`lean/OrbitProofs/Mmu.lean`)

**Model.** Tables are a tree of total functions `index → entry`; a fresh zeroed table is
`fun _ => .inv`. Descriptors are abstract (`page pa prot`, `block pa prot`, `tab t`). `step` is
one iteration of `map_range`'s loop (2 MiB block where the L2 slot is empty and va, pa and the rest
of the range allow it; skip a slot already covered by a block; otherwise an L3 page unless one is
already there), `mapLoop` is the loop, `mapRange` includes the `ALIGN_DOWN` / `ALIGN_UP` of the
arguments, and `walk` is the stage-1 translation.

| theorem | statement (informally) |
|---|---|
| `same_page`, `same_block` | below 2^48, two addresses use the same L0–L3 (L0–L2) slots iff they are in the same 4 KiB page (2 MiB block) |
| `step_spec` | one loop step maps exactly the not-yet-mapped part of `[va, va+adv) ∩ [va, end)`, advances by ≥ 4 KiB, changes nothing else |
| `mapLoop_spec`, `mapRange_spec` | **map_range correctness**: for page-aligned arguments, every previously unmapped page of `[va, va+size)` translates to `pa + (x − va)` with attributes `prot`; every other translation is unchanged (first mapping wins) |
| `mapRange_spec_unaligned`, `mapRange_covers`, `unaligned_fixed` | for arbitrary (unaligned) arguments the fixed `map_range` maps exactly `[ALIGN_DOWN(va), ALIGN_UP(va+size))`: every byte of the range is translated |
| `mapRangeV1_spec_unaligned`, `unaligned_bug` | the original code mapped `[ALIGN_DOWN(va), ALIGN_DOWN(va)+ALIGN_UP(size))`, which can miss the last touched page |
| `mapAll_spec` | a sequence of `map_range` calls on any table = first region containing the address |
| `ttbr0_separation` | for any well-ordered kernel image layout, `mmu_init`'s identity map translates every mapped address to itself, and an address is EL0-accessible **iff** it lies in the user-text or user-stack section: kernel text/rodata/data, the rest of RAM, the DTB and MMIO are never EL0-accessible |
| `mapRange_kva`, `walk_shift` | the TTBR1 higher-half alias (`0xffff_0000_0000_0000 + pa`) behaves like the same mapping at `pa` |
| `ttbr1_el1_only`, `wx_all`, `el0_flags` | no TTBR1 page is EL0-accessible; every attribute set the kernel uses is W^X at EL1 and EL0 |

### Bug found (latent): unaligned ranges lose their last page (fixed in orbit-os `1a8385b` (merged into orbit-os main for its v0.2.0 release))

`map_range` aligns `va` down but computes the end as `ALIGN_DOWN(va) + ALIGN_UP(size)`, so
`map_range(0x1800, size 0x1000)` maps only the page at 0x1000 although the range also covers
0x2000–0x27ff. `mmu_init` passes the DTB's address and size unaligned; on the boards supported
today the DTB lies inside RAM, which is mapped too, so nothing faults. With the DTB outside the
mapped RAM at an unaligned address, the real `mmu_init` leaves the blob's last page unmapped
(shown at orbit-os `ba8bac1` by the bounded check of the real `mmu_init`).

**Fix** (orbit-os `1a8385b` (merged into orbit-os main for its v0.2.0 release)): `end = ALIGN_UP(va + size, 4K)` is computed before `va` is aligned;
the builder moved to the portable `kernel/lib/a64pt.c` with its own host test
(`tests/test_a64pt.c`). The rv64 port's `sv39_map` already computed the end this way.
Regression tests here: `test_unaligned_range_fixed` and
`test_unaligned_dtb_outside_ram_is_fully_mapped`.

## What ties the models to the C code (tested, not proved)

* **Differential tests.** `harness/` compiles orbit-os's `buddy.c` and `a64pt.c` unmodified and `mmu.c`
  with only its three inline-asm statements removed (TLB / I-cache maintenance and the `AT S1E1R` probe) using
  `zig cc` for the host. The Lean executable `orbitmodel` runs the very definitions the theorems are
  about. Both read the same random command sequences and must print identical results: every
  allocation address, free return code, `free_pages` and all eleven `nfree[o]` after every
  operation; and for page tables, translation queries at every boundary of every mapped range (first
  and last byte, ±1 page, enclosing 2 MiB blocks) plus random addresses, decoded from the raw C
  descriptors by a software walk, and the same for `mmu_init` on the qemu-virt and Pi 5 image
  layouts (with RAM reduced to 32 MiB — the model executable evaluates the closure-based tables
  naively and is too slow for a 4 GiB linear map).
* **Bounded exhaustive check of the real `mmu_init`.** For the qemu-virt and Raspberry Pi 5
  layouts and 25 random layouts, every 4 KiB page of the low 4 GiB, of the MMIO window and of both
  TTBR1 alias windows is translated from the C tables and compared with the intended mapping;
  identity, EL0 separation and W^X are asserted on the C attributes directly.
* **Not modelled:** the raw 64-bit descriptor encoding and the C table pool (`pt_pool`, 48 tables;
  the bounded check asserts it is never exhausted), cache/TLB maintenance, concurrency
  (`page_alloc` disables IRQs; there is one CPU), and the hardware walker itself (the Arm
  architecture is taken as specified).
