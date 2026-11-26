/-!
# orbit-os stage-1 page tables: model and proofs

A model of `map_range` (`a64pt_map` in `kernel/lib/a64pt.c` since orbit-os `1a8385b`) and
`mmu_init` (`kernel/arch/aarch64/mmu.c`) of orbit-os (4 KiB granule, 48-bit VA,
four levels L0..L3, 2 MiB block descriptors at L2 where alignment allows, never overwriting a
valid entry).

Page tables are modelled as a tree of total functions (`index → entry`), so a freshly
allocated, zeroed table is `fun _ => .inv`. Descriptors are abstract (`page pa prot`,
`block pa prot`, `tab t`); the raw 64-bit encoding `pa | prot | VALID [| TABLE]` and the C
table pool are *not* modelled here — they are checked by running the real C code
(`harness/mmu_driver.c`): a software walker decodes the raw descriptors exactly like the
hardware walk and the result is compared with this model (`tests/test_mmu_diff.py`) and, for
whole address windows, with the intended mapping (`tests/test_mmu_bounded.py`).
-/
namespace Mmu

def SZ4K : Nat := 4096
def SZ2M : Nat := 2097152
def VA48 : Nat := 281474976710656  -- 2^48

def i0 (va : Nat) : Nat := va / 549755813888 % 512
def i1 (va : Nat) : Nat := va / 1073741824 % 512
def i2 (va : Nat) : Nat := va / 2097152 % 512
def i3 (va : Nat) : Nat := va / 4096 % 512

inductive L3e | inv | page (pa prot : Nat)

/-- `!(desc & PTE_VALID)` -/
def L3e.isInv : L3e → Bool
  | .inv => true
  | .page _ _ => false
inductive L2e | inv | block (pa prot : Nat) | tab (t : Nat → L3e)
inductive L1e | inv | tab (t : Nat → L2e)
inductive L0e | inv | tab (t : Nat → L1e)

abbrev PT := Nat → L0e

def empty : PT := fun _ => .inv

/-- freshly allocated, zeroed tables (`alloc_table()` + `k_memset(t, 0, 4096)`) -/
def emptyL1 : Nat → L1e := fun _ => .inv
def emptyL2 : Nat → L2e := fun _ => .inv
def emptyL3 : Nat → L3e := fun _ => .inv

-- `@[noinline]`: keeps `put2` a partial application, so compiled lookups share the new tables
@[noinline] def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

def walk3 (e : L3e) (x : Nat) : Option (Nat × Nat) :=
  match e with
  | .inv => none
  | .page pa p => some (pa + x % SZ4K, p)

def walk2 (e : L2e) (x : Nat) : Option (Nat × Nat) :=
  match e with
  | .inv => none
  | .block pa p => some (pa + x % SZ2M, p)
  | .tab t3 => walk3 (t3 (i3 x)) x

def walk1 (e : L1e) (x : Nat) : Option (Nat × Nat) :=
  match e with
  | .inv => none
  | .tab t2 => walk2 (t2 (i2 x)) x

/-- the stage-1 translation of `x` (output address, attributes), `none` = translation fault -/
def walk (t : PT) (x : Nat) : Option (Nat × Nat) :=
  match t (i0 x) with
  | .inv => none
  | .tab t1 => walk1 (t1 (i1 x)) x

def l1of (t : PT) (va : Nat) : Nat → L1e :=
  match t (i0 va) with
  | .tab t1 => t1
  | .inv => emptyL1

def l2of (t1 : Nat → L1e) (va : Nat) : Nat → L2e :=
  match t1 (i1 va) with
  | .tab t2 => t2
  | .inv => emptyL2

/-- descend to va's L2 slot (allocating zeroed L0/L1 tables as the C loop does) and store `e` -/
def put2 (t : PT) (va : Nat) (e : L2e) : PT :=
  let t1 := l1of t va
  let t2 := l2of t1 va
  upd t (i0 va) (.tab (upd t1 (i1 va) (.tab (upd t2 (i2 va) e))))

/-- one iteration of the `while (va < end)` loop in `map_range`; returns the advance -/
def step (t : PT) (va pa endv prot : Nat) : PT × Nat :=
  match l2of (l1of t va) va (i2 va) with
  | .block _ _ => (t, SZ2M - va % SZ2M)                       -- already covered by a block
  | .inv =>
    if va % SZ2M = 0 ∧ pa % SZ2M = 0 ∧ SZ2M ≤ endv - va then
      (put2 t va (.block pa prot), SZ2M)                       -- block descriptor
    else (put2 t va (.tab (upd emptyL3 (i3 va) (.page pa prot))), SZ4K)
  | .tab t3 =>
    if (t3 (i3 va)).isInv then (put2 t va (.tab (upd t3 (i3 va) (.page pa prot))), SZ4K)
    else (t, SZ4K)                                            -- never overwrite

def mapLoop : Nat → PT → Nat → Nat → Nat → Nat → PT
  | 0, t, _, _, _, _ => t
  | fuel + 1, t, va, pa, endv, prot =>
    if va < endv then
      let r := step t va pa endv prot
      mapLoop fuel r.1 (va + r.2) (pa + r.2) endv prot
    else t

/-- the original `map_range` (orbit-os ≤ `49ede1e`): end = ALIGN_DOWN(va) + ALIGN_UP(size);
kept as the record of the unaligned-range bug -/
def mapRangeV1 (t : PT) (va pa size prot : Nat) : PT :=
  let va' := va / SZ4K * SZ4K
  let pa' := pa / SZ4K * SZ4K
  let endv := va' + (size + SZ4K - 1) / SZ4K * SZ4K
  mapLoop ((endv - va') / SZ4K + 1) t va' pa' endv prot

/-- `map_range(l0, va, pa, size, prot)` = `a64pt_map` of orbit-os `1a8385b`:
end = ALIGN_UP(va + size), computed before va is rounded down -/
def mapRange (t : PT) (va pa size prot : Nat) : PT :=
  let va' := va / SZ4K * SZ4K
  let pa' := pa / SZ4K * SZ4K
  let endv := (va + size + SZ4K - 1) / SZ4K * SZ4K
  mapLoop ((endv - va') / SZ4K + 1) t va' pa' endv prot

/-! ## Index arithmetic -/

theorem same_page {x va : Nat} (hx : x < VA48) (hv : va < VA48) :
    (i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va ∧ i3 x = i3 va) ↔ x / SZ4K = va / SZ4K := by
  unfold i0 i1 i2 i3 SZ4K; unfold VA48 at hx hv; omega

theorem same_block {x va : Nat} (hx : x < VA48) (hv : va < VA48) :
    (i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va) ↔ x / SZ2M = va / SZ2M := by
  unfold i0 i1 i2 SZ2M; unfold VA48 at hx hv; omega

/-! ## What `put2` changes -/

theorem walk_put2 (t : PT) (va : Nat) (e : L2e) (x : Nat) :
    walk (put2 t va e) x =
      if i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va then walk2 e x else walk t x := by
  unfold put2 walk l1of l2of
  by_cases h0 : i0 x = i0 va
  · rw [h0]
    by_cases h1 : i1 x = i1 va
    · by_cases h2 : i2 x = i2 va
      · rw [if_pos ⟨rfl, h1, h2⟩]; simp [upd, walk1, h1, h2]
      · rw [if_neg (fun h => h2 h.2.2)]
        simp only [upd, if_true, walk1, h1, h2, if_false]
        cases t (i0 va) with
        | inv => rfl
        | tab t1 =>
          simp only
          cases t1 (i1 va) with
          | inv => rfl
          | tab t2 => rfl
    · rw [if_neg (fun h => h1 h.2.1)]
      simp only [upd, if_true, walk1, h1, if_false]
      cases t (i0 va) with
      | inv => rfl
      | tab t1 => rfl
  · rw [if_neg (fun h => h0 h.1)]
    simp [upd, h0]

theorem walk_path (t : PT) (va x : Nat) (h : i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va) :
    walk t x = walk2 (l2of (l1of t va) va (i2 va)) x := by
  obtain ⟨h0, h1, h2⟩ := h
  unfold walk l2of l1of
  rw [h0]
  cases t (i0 va) with
  | inv => rfl
  | tab t1 =>
    simp only [walk1, h1]
    cases t1 (i1 va) with
    | inv => rfl
    | tab t2 => simp [h2]

/-- installing a page in va's L3 table `T3` (the existing one or a fresh one) -/
theorem walk_put_page (t : PT) (va pa prot : Nat) (T3 : Nat → L3e) (hv : va < VA48)
    (hT : ∀ x, i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va → walk t x = walk3 (T3 (i3 x)) x)
    (x : Nat) (hx : x < VA48) :
    walk (put2 t va (.tab (upd T3 (i3 va) (.page pa prot)))) x =
      if x / SZ4K = va / SZ4K then some (pa + x % SZ4K, prot) else walk t x := by
  rw [walk_put2]
  by_cases hb : i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va
  · rw [if_pos hb]
    simp only [walk2]
    by_cases hp : i3 x = i3 va
    · rw [if_pos ((same_page hx hv).mp ⟨hb.1, hb.2.1, hb.2.2, hp⟩)]
      simp [walk3, upd, hp]
    · have : ¬ x / SZ4K = va / SZ4K := fun h => hp ((same_page hx hv).mpr h).2.2.2
      rw [if_neg this, hT x hb]
      simp [upd, hp]
  · have : ¬ x / SZ4K = va / SZ4K := fun h => by
      have := (same_page hx hv).mpr h; exact hb ⟨this.1, this.2.1, this.2.2.1⟩
    rw [if_neg hb, if_neg this]

theorem walk_put_block (t : PT) (va pa prot : Nat) (hv : va < VA48) (x : Nat) (hx : x < VA48) :
    walk (put2 t va (.block pa prot)) x =
      if x / SZ2M = va / SZ2M then some (pa + x % SZ2M, prot) else walk t x := by
  rw [walk_put2]
  by_cases hb : i0 x = i0 va ∧ i1 x = i1 va ∧ i2 x = i2 va
  · rw [if_pos hb, if_pos ((same_block hx hv).mp hb)]; rfl
  · rw [if_neg hb, if_neg (fun h => hb ((same_block hx hv).mpr h))]

/-! ## One loop iteration -/

theorem conv4K (va pa endv x p : Nat) (w : Option (Nat × Nat)) (hva : va % SZ4K = 0)
    (hend : va + SZ4K ≤ endv) (hn : x / SZ4K = va / SZ4K → w = none) :
    (if va ≤ x ∧ x < va + SZ4K ∧ x < endv ∧ w = none then some (pa + (x - va), p) else w) =
      (if x / SZ4K = va / SZ4K then some (pa + x % SZ4K, p) else w) := by
  by_cases hq : x / SZ4K = va / SZ4K
  · have c : va ≤ x ∧ x < va + SZ4K ∧ x < endv ∧ w = none := by
      unfold SZ4K at *; exact ⟨by omega, by omega, by omega, hn hq⟩
    rw [if_pos c, if_pos hq]; unfold SZ4K at *; congr 2; omega
  · have c : ¬ (va ≤ x ∧ x < va + SZ4K ∧ x < endv ∧ w = none) := by
      intro h; apply hq; unfold SZ4K at *; omega
    rw [if_neg c, if_neg hq]

theorem conv2M (va pa endv x p : Nat) (w : Option (Nat × Nat)) (hva : va % SZ2M = 0)
    (hend : va + SZ2M ≤ endv) (hn : x / SZ2M = va / SZ2M → w = none) :
    (if va ≤ x ∧ x < va + SZ2M ∧ x < endv ∧ w = none then some (pa + (x - va), p) else w) =
      (if x / SZ2M = va / SZ2M then some (pa + x % SZ2M, p) else w) := by
  by_cases hq : x / SZ2M = va / SZ2M
  · have c : va ≤ x ∧ x < va + SZ2M ∧ x < endv ∧ w = none := by
      unfold SZ2M at *; exact ⟨by omega, by omega, by omega, hn hq⟩
    rw [if_pos c, if_pos hq]; unfold SZ2M at *; congr 2; omega
  · have c : ¬ (va ≤ x ∧ x < va + SZ2M ∧ x < endv ∧ w = none) := by
      intro h; apply hq; unfold SZ2M at *; omega
    rw [if_neg c, if_neg hq]

theorem conv_keep (va pa endv x p adv : Nat) (w : Option (Nat × Nat))
    (hn : va ≤ x → x < va + adv → w ≠ none) :
    (if va ≤ x ∧ x < va + adv ∧ x < endv ∧ w = none then some (pa + (x - va), p) else w) = w := by
  rw [if_neg]; intro h; exact hn h.1 h.2.1 h.2.2.2

/-- A step maps the not-yet-mapped part of `[va, va + adv) ∩ [va, endv)` and nothing else. -/
theorem step_spec (t : PT) (va pa endv prot : Nat) (hva : va % SZ4K = 0) (hpa : pa % SZ4K = 0)
    (hend : endv % SZ4K = 0) (hlt : va < endv) (hev : endv ≤ VA48) :
    SZ4K ≤ (step t va pa endv prot).2 ∧ (step t va pa endv prot).2 % SZ4K = 0 ∧
    ∀ x, x < VA48 → walk (step t va pa endv prot).1 x =
      if va ≤ x ∧ x < va + (step t va pa endv prot).2 ∧ x < endv ∧ walk t x = none
      then some (pa + (x - va), prot) else walk t x := by
  have hv48 : va < VA48 := by omega
  have h4k : va + SZ4K ≤ endv := by unfold SZ4K at *; omega
  unfold step
  split
  · next bpa bp hslot =>
    refine ⟨by unfold SZ4K SZ2M at *; omega, by unfold SZ4K SZ2M at *; omega, ?_⟩
    intro x hx
    rw [conv_keep]
    intro h1 h2
    have hb := (same_block hx hv48).mpr (by unfold SZ2M at *; omega)
    rw [walk_path t va x hb, hslot]; simp [walk2]
  · next hslot =>
    split
    · next hc =>
      refine ⟨by unfold SZ4K SZ2M; omega, by unfold SZ4K SZ2M; omega, ?_⟩
      intro x hx
      rw [walk_put_block t va pa prot hv48 x hx, conv2M va pa endv x prot _ hc.1 (by omega)]
      intro hq
      rw [walk_path t va x ((same_block hx hv48).mpr hq), hslot]; rfl
    · refine ⟨by unfold SZ4K; omega, by unfold SZ4K; omega, ?_⟩
      intro x hx
      rw [walk_put_page t va pa prot emptyL3 hv48 (fun x hb => by
        rw [walk_path t va x hb, hslot]; rfl) x hx, conv4K va pa endv x prot _ hva h4k]
      intro hq
      have := (same_page hx hv48).mpr hq
      rw [walk_path t va x ⟨this.1, this.2.1, this.2.2.1⟩, hslot]; rfl
  · next t3 hslot =>
    by_cases hinv : (t3 (i3 va)).isInv = true
    · have hp3 : t3 (i3 va) = .inv := by revert hinv; cases t3 (i3 va) <;> simp [L3e.isInv]
      simp only [hinv, if_true]
      refine ⟨by unfold SZ4K; omega, by unfold SZ4K; omega, ?_⟩
      intro x hx
      rw [walk_put_page t va pa prot t3 hv48 (fun x hb => by
        rw [walk_path t va x hb, hslot]; rfl) x hx, conv4K va pa endv x prot _ hva h4k]
      intro hq
      have := (same_page hx hv48).mpr hq
      rw [walk_path t va x ⟨this.1, this.2.1, this.2.2.1⟩, hslot]
      simp [walk2, walk3, this.2.2.2, hp3]
    · simp only [hinv, if_false, Bool.false_eq_true]
      obtain ⟨ppa, pp, hp3⟩ : ∃ a b, t3 (i3 va) = .page a b := by
        revert hinv; cases t3 (i3 va) <;> simp [L3e.isInv]
      refine ⟨by unfold SZ4K; omega, by unfold SZ4K; omega, ?_⟩
      intro x hx
      rw [conv_keep]
      intro h1 h2
      have := (same_page hx hv48).mpr (by unfold SZ4K at *; omega)
      rw [walk_path t va x ⟨this.1, this.2.1, this.2.2.1⟩, hslot]
      simp [walk2, walk3, this.2.2.2, hp3]

/-! ## The whole loop -/

theorem mapLoop_spec : ∀ (fuel : Nat) (t : PT) (va pa endv prot : Nat),
    va % SZ4K = 0 → pa % SZ4K = 0 → endv % SZ4K = 0 → endv ≤ VA48 →
    (endv - va) / SZ4K + 1 ≤ fuel →
    ∀ x, x < VA48 → walk (mapLoop fuel t va pa endv prot) x =
      if va ≤ x ∧ x < endv ∧ walk t x = none then some (pa + (x - va), prot) else walk t x
  | 0, _, _, _, _, _, _, _, _, _, hf => absurd hf (Nat.not_succ_le_zero _)
  | fuel + 1, t, va, pa, endv, prot, hva, hpa, hend, hev, hf => by
    intro x hx
    simp only [mapLoop]
    by_cases hlt : va < endv
    · rw [if_pos hlt]
      obtain ⟨hadv, hmod, hspec⟩ := step_spec t va pa endv prot hva hpa hend hlt hev
      generalize (step t va pa endv prot).1 = t' at hspec ⊢
      generalize (step t va pa endv prot).2 = adv at hadv hmod hspec ⊢
      rw [mapLoop_spec fuel t' (va + adv) (pa + adv) endv prot (by unfold SZ4K at *; omega)
        (by unfold SZ4K at *; omega) hend hev (by unfold SZ4K at *; omega) x hx, hspec x hx]
      by_cases h1 : va + adv ≤ x
      · have hC : ¬ (va ≤ x ∧ x < va + adv ∧ x < endv ∧ walk t x = none) := by omega
        rw [if_neg hC]
        by_cases hc : va ≤ x ∧ x < endv ∧ walk t x = none
        · rw [if_pos ⟨h1, hc.2.1, hc.2.2⟩, if_pos hc]; congr 2; omega
        · rw [if_neg (fun h => hc ⟨by omega, h.2.1, h.2.2⟩), if_neg hc]
      · rw [if_neg (fun h => h1 h.1)]
        by_cases hc : va ≤ x ∧ x < endv ∧ walk t x = none
        · rw [if_pos ⟨hc.1, by omega, hc.2.1, hc.2.2⟩, if_pos hc]
        · rw [if_neg (fun h => hc ⟨h.1, h.2.2.1, h.2.2.2⟩), if_neg hc]
    · rw [if_neg hlt, if_neg (fun h => hlt (by omega))]

/-- **`map_range` correctness** (page-aligned arguments): every page of `[va, va+size)` that was
unmapped now translates to `pa + (x - va)` with attributes `prot`; every other translation,
in particular every previously mapped page, is unchanged. -/
theorem mapRange_spec (t : PT) (va pa size prot : Nat) (hva : va % SZ4K = 0) (hpa : pa % SZ4K = 0)
    (hs : size % SZ4K = 0) (hlim : va + size ≤ VA48) (x : Nat) (hx : x < VA48) :
    walk (mapRange t va pa size prot) x =
      if va ≤ x ∧ x < va + size ∧ walk t x = none then some (pa + (x - va), prot) else walk t x := by
  unfold mapRange
  have e1 : va / SZ4K * SZ4K = va := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hva)
  have e2 : pa / SZ4K * SZ4K = pa := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpa)
  have e3 : (va + size + SZ4K - 1) / SZ4K * SZ4K = va + size := by
    unfold SZ4K at hva hs ⊢; omega
  rw [e1, e2, e3]
  exact mapLoop_spec _ t va pa (va + size) prot hva hpa (by unfold SZ4K at *; omega) hlim
    (Nat.le_refl _) x hx

/-- For unaligned arguments the original C code mapped
`[ALIGN_DOWN(va), ALIGN_DOWN(va) + ALIGN_UP(size))`, which can miss the last page the range
touches. -/
theorem mapRangeV1_spec_unaligned (t : PT) (va pa size prot : Nat)
    (hlim : va / SZ4K * SZ4K + (size + SZ4K - 1) / SZ4K * SZ4K ≤ VA48) (x : Nat) (hx : x < VA48) :
    walk (mapRangeV1 t va pa size prot) x =
      if va / SZ4K * SZ4K ≤ x ∧ x < va / SZ4K * SZ4K + (size + SZ4K - 1) / SZ4K * SZ4K ∧ walk t x = none
      then some (pa / SZ4K * SZ4K + (x - va / SZ4K * SZ4K), prot) else walk t x := by
  unfold mapRangeV1
  exact mapLoop_spec _ t _ _ _ prot (by unfold SZ4K; omega) (by unfold SZ4K; omega)
    (by unfold SZ4K; omega) hlim (Nat.le_refl _) x hx

/-- **Fixed `map_range`, arbitrary (unaligned) arguments**: it maps exactly the pages that
`[va, va + size)` touches, i.e. `[ALIGN_DOWN(va), ALIGN_UP(va + size))`, page `x` to the
corresponding page of `ALIGN_DOWN(pa)`, and leaves every other translation unchanged. -/
theorem mapRange_spec_unaligned (t : PT) (va pa size prot : Nat)
    (hlim : (va + size + SZ4K - 1) / SZ4K * SZ4K ≤ VA48) (x : Nat) (hx : x < VA48) :
    walk (mapRange t va pa size prot) x =
      if va / SZ4K * SZ4K ≤ x ∧ x < (va + size + SZ4K - 1) / SZ4K * SZ4K ∧ walk t x = none
      then some (pa / SZ4K * SZ4K + (x - va / SZ4K * SZ4K), prot) else walk t x := by
  unfold mapRange
  exact mapLoop_spec _ t _ _ _ prot (by unfold SZ4K; omega) (by unfold SZ4K; omega)
    (by unfold SZ4K; omega) hlim (by unfold SZ4K; omega) x hx

/-- every byte of an unaligned range that was unmapped is translated after the fixed `map_range` -/
theorem mapRange_covers (t : PT) (va pa size prot : Nat)
    (hlim : (va + size + SZ4K - 1) / SZ4K * SZ4K ≤ VA48) (x : Nat) (hx1 : va ≤ x) (hx2 : x < va + size)
    (hnone : walk t x = none) : walk (mapRange t va pa size prot) x ≠ none := by
  have hx : x < VA48 := by unfold SZ4K at *; omega
  rw [mapRange_spec_unaligned t va pa size prot hlim x hx,
    if_pos ⟨by unfold SZ4K; omega, by unfold SZ4K; omega, hnone⟩]
  simp

/-- **Bug (latent, fixed in orbit-os `1a8385b`)**, on the original `map_range`: mapping the 4 KiB range `[0x1800, 0x2800)` leaves the page at 0x2000
unmapped although the range covers its first 0x800 bytes. `mmu_init` passes the DTB's
address and size unaligned; on the boards supported today the DTB lies inside the RAM window,
which is mapped as well, so the kernel does not fault. Reproduced on the C code of
orbit-os `ba8bac1`; `tests/test_mmu_diff.py::test_unaligned_range_fixed` is the regression test. -/
theorem unaligned_bug :
    walk (mapRangeV1 empty 0x1800 0x1800 0x1000 1) 0x1800 = some (0x1800, 1) ∧
    walk (mapRangeV1 empty 0x1800 0x1800 0x1000 1) 0x2000 = none := by
  constructor <;> rfl

/-- the same mapping with the fixed `map_range` (orbit-os `1a8385b`) covers both pages -/
theorem unaligned_fixed :
    walk (mapRange empty 0x1800 0x1800 0x1000 1) 0x1800 = some (0x1800, 1) ∧
    walk (mapRange empty 0x1800 0x1800 0x1000 1) 0x27ff = some (0x27ff, 1) := by
  constructor <;> rfl

/-! ## Sequences of mappings (first mapping wins) -/

structure Region where
  va : Nat
  pa : Nat
  size : Nat
  prot : Nat

def mapAll (t : PT) : List Region → PT
  | [] => t
  | r :: rs => mapAll (mapRange t r.va r.pa r.size r.prot) rs

def lookup (x : Nat) : List Region → Option (Nat × Nat)
  | [] => none
  | r :: rs => if r.va ≤ x ∧ x < r.va + r.size then some (r.pa + (x - r.va), r.prot) else lookup x rs

def Region.ok (r : Region) : Prop :=
  r.va % SZ4K = 0 ∧ r.pa % SZ4K = 0 ∧ r.size % SZ4K = 0 ∧ r.va + r.size ≤ VA48

theorem mapAll_spec : ∀ (rs : List Region) (t : PT), (∀ r ∈ rs, r.ok) → ∀ x, x < VA48 →
    walk (mapAll t rs) x = (walk t x).or (lookup x rs)
  | [], t, _, x, _ => by simp only [mapAll, lookup]; cases walk t x <;> rfl
  | r :: rs, t, h, x, hx => by
    have ⟨a, b, c, d⟩ := h r (List.mem_cons_self ..)
    simp only [mapAll]
    rw [mapAll_spec rs _ (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) x hx,
      mapRange_spec t r.va r.pa r.size r.prot a b c d x hx]
    simp only [lookup]
    cases hw : walk t x with
    | some v =>
      rw [if_neg (fun h => nomatch h.2.2)]
      rfl
    | none =>
      by_cases hin : r.va ≤ x ∧ x < r.va + r.size
      · rw [if_pos ⟨hin.1, hin.2, rfl⟩, if_pos hin]; try rfl
      · rw [if_neg (fun h => hin ⟨h.1, h.2.1⟩), if_neg hin]; try rfl

/-! ## Attribute constants (from mmu.c) and their meaning -/

def PTE_AP_EL0 : Nat := 0x40
def PTE_AP_RO : Nat := 0x80
def PROT_KDATA : Nat := 0x60000000000708
def PROT_KTEXT : Nat := 0x40000000000788
def PROT_KRO : Nat := 0x60000000000788
def PROT_UTEXT : Nat := 0x200000000007c8
def PROT_UDATA : Nat := 0x60000000000748
def PROT_DEVICE : Nat := 0x60000000000404

def el0 (p : Nat) : Bool := p.testBit 6        -- AP[1]
def readOnly (p : Nat) : Bool := p.testBit 7   -- AP[2]
def pxn (p : Nat) : Bool := p.testBit 53
def uxn (p : Nat) : Bool := p.testBit 54

def allProts : List Nat := [PROT_KDATA, PROT_KTEXT, PROT_KRO, PROT_UTEXT, PROT_UDATA, PROT_DEVICE]

/-- W^X at EL1 and EL0 for every attribute set the kernel uses -/
theorem wx_all : ∀ p ∈ allProts, (!readOnly p → pxn p) ∧ (!readOnly p → uxn p ∨ !el0 p) := by decide

theorem el0_flags :
    el0 PROT_UTEXT ∧ el0 PROT_UDATA ∧ !el0 PROT_KDATA ∧ !el0 PROT_KTEXT ∧ !el0 PROT_KRO ∧
    !el0 PROT_DEVICE ∧ readOnly PROT_KTEXT ∧ readOnly PROT_UTEXT ∧ readOnly PROT_KRO := by decide

/-! ## `mmu_init`'s identity map: kernel/user separation -/

structure Layout where
  ks : Nat     -- __kernel_start
  uts : Nat    -- __user_text_start
  ute : Nat    -- __user_text_end
  te : Nat     -- __text_end
  re : Nat     -- __rodata_end
  uss : Nat    -- __user_stack_start
  use : Nat    -- __user_stack_end
  kend : Nat   -- ALIGN_UP(_end, 4K)
  ramb : Nat
  ramm : Nat   -- min(ram_size, 4 GiB)
  dtb : Nat
  dtbs : Nat
  devb : Nat
  devs : Nat

/-- `map_ident(start, end, prot)` maps only when `end > start` -/
def ident (a b p : Nat) : List Region := if a < b then [⟨a, a, b - a, p⟩] else []

/-- the TTBR0 region list of `mmu_init`, in program order -/
def ttbr0 (L : Layout) : List Region :=
  ident L.ks L.uts PROT_KTEXT ++ ident L.uts L.ute PROT_UTEXT ++ ident L.ute L.te PROT_KTEXT ++
  ident L.te L.re PROT_KRO ++ ident L.re L.uss PROT_KDATA ++ ident L.uss L.use PROT_UDATA ++
  ident L.use L.kend PROT_KDATA ++ [⟨L.ramb, L.ramb, L.ramm, PROT_KDATA⟩] ++
  (if L.dtb ≠ 0 then [⟨L.dtb, L.dtb, L.dtbs, PROT_KRO⟩] else []) ++ [⟨L.devb, L.devb, L.devs, PROT_DEVICE⟩]

def Layout.ok (L : Layout) : Prop :=
  L.ks ≤ L.uts ∧ L.uts ≤ L.ute ∧ L.ute ≤ L.te ∧ L.te ≤ L.re ∧ L.re ≤ L.uss ∧ L.uss ≤ L.use ∧
  L.use ≤ L.kend ∧ ∀ r ∈ ttbr0 L, r.ok

theorem lookup_append (x : Nat) (a b : List Region) :
    lookup x (a ++ b) = (lookup x a).or (lookup x b) := by
  induction a with
  | nil => simp [lookup]
  | cons r rs ih =>
    simp only [List.cons_append, lookup]
    split
    · rfl
    · exact ih

theorem lookup_some_mem {x : Nat} : ∀ {rs : List Region} {v : Nat × Nat}, lookup x rs = some v →
    ∃ r ∈ rs, r.va ≤ x ∧ x < r.va + r.size ∧ v = (r.pa + (x - r.va), r.prot)
  | [], _, h => by simp [lookup] at h
  | r :: rs, v, h => by
    simp only [lookup] at h
    by_cases hin : r.va ≤ x ∧ x < r.va + r.size
    · rw [if_pos hin] at h
      exact ⟨r, List.mem_cons_self .., hin.1, hin.2, (Option.some.inj h).symm⟩
    · rw [if_neg hin] at h
      obtain ⟨r', hr', h1, h2, h3⟩ := lookup_some_mem h
      exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2, h3⟩

theorem mem_ident {r : Region} {a b p : Nat} (h : r ∈ ident a b p) :
    r.va = a ∧ r.pa = a ∧ r.va + r.size = b ∧ r.prot = p := by
  unfold ident at h
  split at h
  · simp at h; subst h; simp; omega
  · simp at h

/-- **No aliasing of kernel and user memory** in the identity map built by `mmu_init` on an
empty table: every mapped address translates to itself, and an address is accessible from EL0
exactly when it lies in the user-text or user-stack section. In particular kernel text,
rodata, data/BSS, the rest of RAM, the DTB and MMIO are never EL0-accessible. -/
theorem ttbr0_separation (L : Layout) (hL : L.ok) (x : Nat) (hx : x < VA48) :
    (∀ v, walk (mapAll empty (ttbr0 L)) x = some v → v.1 = x) ∧
    ((∃ v, walk (mapAll empty (ttbr0 L)) x = some v ∧ el0 v.2 = true) ↔
      ((L.uts ≤ x ∧ x < L.ute) ∨ (L.uss ≤ x ∧ x < L.use))) := by
  have hw := mapAll_spec (ttbr0 L) empty hL.2.2.2.2.2.2.2 x hx
  have he : walk empty x = none := rfl
  rw [he] at hw
  simp only [Option.none_or] at hw
  rw [hw]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hL
  -- every region of the identity map has pa = va
  have hid : ∀ r ∈ ttbr0 L, r.pa = r.va := by
    intro r hr
    simp only [ttbr0, List.mem_append] at hr
    rcases hr with ((((((((hr | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr
    all_goals first
      | (have := mem_ident hr; omega)
      | (simp at hr; subst hr; rfl)
      | (split at hr <;> simp at hr; subst hr; rfl)
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨r, hr, hr1, -, rfl⟩ := lookup_some_mem hv
    simp only [hid r hr]; omega
  constructor
  · rintro ⟨v, hv, hel⟩
    obtain ⟨r, hr, hx1, hx2, rfl⟩ := lookup_some_mem hv
    simp only at hel
    simp only [ttbr0, List.mem_append] at hr
    rcases hr with ((((((((hr | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr) | hr
    · have := mem_ident hr; rw [this.2.2.2] at hel; exact absurd hel (by decide)
    · have := mem_ident hr; left; omega
    · have := mem_ident hr; rw [this.2.2.2] at hel; exact absurd hel (by decide)
    · have := mem_ident hr; rw [this.2.2.2] at hel; exact absurd hel (by decide)
    · have := mem_ident hr; rw [this.2.2.2] at hel; exact absurd hel (by decide)
    · have := mem_ident hr; right; omega
    · have := mem_ident hr; rw [this.2.2.2] at hel; exact absurd hel (by decide)
    · simp at hr; subst hr; simp only at hel; exact absurd hel (by decide)
    · split at hr
      · simp at hr; subst hr; simp only at hel; exact absurd hel (by decide)
      · simp at hr
    · simp at hr; subst hr; simp only at hel; exact absurd hel (by decide)
  · intro hu
    have n1 : lookup x (ident L.ks L.uts PROT_KTEXT) = none := by
      unfold ident; split <;> simp only [lookup] <;> (try rw [if_neg (by omega)]) <;> rfl
    rcases hu with hu | hu
    · refine ⟨(x, PROT_UTEXT), ?_, show el0 PROT_UTEXT = true by decide⟩
      have n2 : lookup x (ident L.uts L.ute PROT_UTEXT) = some (x, PROT_UTEXT) := by
        unfold ident; rw [if_pos (by omega)]; simp only [lookup]
        rw [if_pos (by omega)]; congr 2; omega
      unfold ttbr0
      simp only [lookup_append, n1, n2, Option.none_or, Option.some_or]
    · refine ⟨(x, PROT_UDATA), ?_, show el0 PROT_UDATA = true by decide⟩
      have nz : ∀ a b p, (b ≤ x ∨ x < a) → lookup x (ident a b p) = none := by
        intro a b p h
        unfold ident; split <;> simp only [lookup] <;> (try rw [if_neg (by omega)]) <;> rfl
      have n6 : lookup x (ident L.uss L.use PROT_UDATA) = some (x, PROT_UDATA) := by
        unfold ident; rw [if_pos (by omega)]; simp only [lookup]
        rw [if_pos (by omega)]; congr 2; omega
      unfold ttbr0
      simp only [lookup_append, n1, nz L.uts L.ute PROT_UTEXT (by omega),
        nz L.ute L.te PROT_KTEXT (by omega), nz L.te L.re PROT_KRO (by omega),
        nz L.re L.uss PROT_KDATA (by omega), n6, Option.none_or, Option.some_or]

/-! ## TTBR1: the higher-half alias -/

def KVA : Nat := 0xffff000000000000

theorem idx_shift (va k : Nat) :
    i0 (va + VA48 * k) = i0 va ∧ i1 (va + VA48 * k) = i1 va ∧ i2 (va + VA48 * k) = i2 va ∧
    i3 (va + VA48 * k) = i3 va ∧ (va + VA48 * k) % SZ2M = va % SZ2M ∧ (va + VA48 * k) % SZ4K = va % SZ4K := by
  unfold i0 i1 i2 i3 VA48 SZ2M SZ4K; omega

theorem walk_shift (t : PT) (x k : Nat) : walk t (x + VA48 * k) = walk t x := by
  have ⟨a, b, c, d, e, f⟩ := idx_shift x k
  unfold walk walk1 walk2 walk3
  rw [a, b, c, d, e, f]

theorem step_shift (t : PT) (va pa endv prot k : Nat) :
    step t (va + VA48 * k) pa (endv + VA48 * k) prot = step t va pa endv prot := by
  have ⟨a, b, c, d, e, f⟩ := idx_shift va k
  have g : endv + VA48 * k - (va + VA48 * k) = endv - va := by omega
  unfold step put2 l1of l2of
  simp only [a, b, c, d, e, g]

theorem mapLoop_shift : ∀ (fuel : Nat) (t : PT) (va pa endv prot k : Nat),
    mapLoop fuel t (va + VA48 * k) pa (endv + VA48 * k) prot = mapLoop fuel t va pa endv prot
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, t, va, pa, endv, prot, k => by
    simp only [mapLoop, step_shift]
    by_cases h : va < endv
    · simp only [show va + VA48 * k < endv + VA48 * k by omega, h, if_true]
      rw [show va + VA48 * k + (step t va pa endv prot).2 = va + (step t va pa endv prot).2 + VA48 * k by omega]
      exact mapLoop_shift fuel _ _ _ _ _ k
    · simp only [show ¬ (va + VA48 * k < endv + VA48 * k) by omega, h, if_false]

/-- the TTBR1 alias behaves exactly like the same mapping made at `va - KERNEL_VA_BASE` -/
theorem mapRange_kva (t : PT) (va pa size prot : Nat) :
    mapRange t (va + KVA) pa size prot = mapRange t va pa size prot := by
  have hk : KVA = VA48 * 65535 := by unfold KVA VA48; rfl
  unfold mapRange
  dsimp only
  rw [hk]
  have e1 : (va + VA48 * 65535) / SZ4K * SZ4K = va / SZ4K * SZ4K + VA48 * 65535 := by
    unfold SZ4K VA48; omega
  have e2 : (va + VA48 * 65535 + size + SZ4K - 1) / SZ4K * SZ4K =
      (va + size + SZ4K - 1) / SZ4K * SZ4K + VA48 * 65535 := by
    have hk4 : (VA48 * 65535) % SZ4K = 0 := by unfold VA48 SZ4K; rfl
    clear e1 hk
    generalize VA48 * 65535 = K at hk4 ⊢
    unfold SZ4K at hk4 ⊢; omega
  rw [e1, e2]
  generalize va / SZ4K * SZ4K = A
  generalize (va + size + SZ4K - 1) / SZ4K * SZ4K = E
  generalize hK : VA48 * 65535 = K
  have e3 : E + K - (A + K) = E - A := by omega
  rw [e3, ← hK]
  exact mapLoop_shift _ t _ _ _ prot 65535

/-- the TTBR1 region list of `mmu_init` (higher-half linear alias of RAM and MMIO) -/
def ttbr1 (L : Layout) : List Region :=
  [⟨KVA + L.ramb, L.ramb, L.ramm, PROT_KDATA⟩, ⟨KVA + L.devb, L.devb, L.devs, PROT_DEVICE⟩]

/-- nothing in the TTBR1 alias is EL0-accessible -/
theorem ttbr1_el1_only (L : Layout) : ∀ r ∈ ttbr1 L, el0 r.prot = false := by
  intro r hr; simp [ttbr1] at hr; rcases hr with rfl | rfl
  · show el0 PROT_KDATA = false; decide
  · show el0 PROT_DEVICE = false; decide

end Mmu
