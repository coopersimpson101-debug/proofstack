/-!
# orbit-os buddy allocator: model and proofs

A faithful functional model of `kernel/mm/buddy.c` in orbit-os, working in page indices
relative to `b->base`.

| C (`buddy.c`)                              | model                                            |
|--------------------------------------------|--------------------------------------------------|
| `free[o]` lists, `list_push_back`          | one list `free`, appended at the end; the C list |
|                                            | `free[o]` is `free.filter (·.ord = o)` in order  |
| `list_remove` (`unlink_free`)              | `List.erase`                                     |
| `buddy_alloc` takes `free[o].next`         | first block of order `o` in `free`               |
| `meta[i] == (META_FREE | o)`               | `⟨i, o⟩ ∈ free`                                  |
| `meta[i] & META_ALLOC`                     | some block with index `i` in `alloc`             |
| `idx ^ (1 << order)` (idx aligned)         | `buddyOf idx order`                              |
| `free_pages`, `managed_pages` counters     | `freePages`, `managed`                           |

The C code is tied to this model by differential testing (`harness/`, `tests/test_buddy_diff.py`):
both are driven with the same random operation sequences and must agree on every returned
address, return code, `free_pages`, and every `nfree[o]`.
-/
namespace Buddy

def ORDERS : Nat := 11

structure Block where
  idx : Nat
  ord : Nat
deriving DecidableEq, Repr

def Block.size (b : Block) : Nat := 2 ^ b.ord

structure St where
  npages : Nat
  free : List Block
  alloc : List Block
  freePages : Nat
  managed : Nat
deriving Repr, DecidableEq

/-- `buddy_init`: every page reserved, nothing free. -/
def St.init (n : Nat) : St := ⟨n, [], [], 0, 0⟩

/-- `idx ^ (1 << o)` for an index aligned to `2^o`. -/
def buddyOf (i o : Nat) : Nat := if i % 2 ^ (o + 1) = 0 then i + 2 ^ o else i - 2 ^ o

/-- `push_free` -/
def push (s : St) (i o : Nat) : St :=
  { s with free := s.free ++ [⟨i, o⟩], freePages := s.freePages + 2 ^ o }

/-- `unlink_free` -/
def unlink (s : St) (i o : Nat) : St :=
  { s with free := s.free.erase ⟨i, o⟩, freePages := s.freePages - 2 ^ o }

/-- `free_block`: free the block `⟨i, o⟩`, coalescing upward. `fuel` only makes the
recursion structural; callers pass `ORDERS`, which is never exhausted (`10 ≤ fuel + o`). -/
def freeBlock : Nat → St → Nat → Nat → St
  | 0, s, i, o => push s i o
  | fuel + 1, s, i, o =>
    if o + 1 < ORDERS then
      if s.npages < buddyOf i o + 2 ^ o then push s i o
      else if (⟨buddyOf i o, o⟩ : Block) ∈ s.free then
        freeBlock fuel (unlink s (buddyOf i o) o) (min i (buddyOf i o)) (o + 1)
      else push s i o
    else push s i o

/-- smallest order `≥ order` with a non-empty free list -/
def findOrder (s : St) (order : Nat) : Option Nat :=
  (List.range ORDERS).find? (fun o => decide (order ≤ o) && s.free.any (fun b => b.ord == o))

/-- the `while (o > order) { o--; push_free(idx + 2^o, o); }` loop of `buddy_alloc` -/
def split (i order : Nat) : Nat → St → St
  | 0, s => s
  | o + 1, s => if order ≤ o then split i order o (push s (i + 2 ^ o) o) else s

/-- `buddy_alloc`: returns the page index of the block (C: `base + idx * PAGE_SIZE`). -/
def alloc (s : St) (order : Nat) : Option Nat × St :=
  if order < ORDERS then
    match findOrder s order with
    | none => (none, s)
    | some o =>
      match s.free.find? (fun b => b.ord == o) with
      | none => (none, s)
      | some b =>
        let s2 := split b.idx order o (unlink s b.idx o)
        (some b.idx, { s2 with alloc := ⟨b.idx, order⟩ :: s2.alloc })
  else (none, s)

/-- `buddy_free`: `true` = 0, `false` = -1 (not an allocated block head: double free etc.) -/
def free (s : St) (i : Nat) : Bool × St :=
  match s.alloc.find? (fun b => b.idx == i) with
  | none => (false, s)
  | some b => (true, freeBlock ORDERS { s with alloc := s.alloc.erase b } i b.ord)

/-- the order computation inside `buddy_add_range` -/
def fitOrder (i e : Nat) : Nat → Nat → Nat
  | 0, o => o
  | fuel + 1, o =>
    if o + 1 < ORDERS ∧ i % 2 ^ (o + 1) = 0 ∧ i + 2 ^ (o + 1) ≤ e then fitOrder i e fuel (o + 1) else o

/-- `b->meta[idx] & (META_FREE | META_ALLOC)` -/
def isHead (s : St) (i : Nat) : Bool := (s.free ++ s.alloc).any (fun b => b.idx == i)

def addLoop (e : Nat) : Nat → St → Nat → St
  | 0, s, _ => s
  | fuel + 1, s, i =>
    if i < e then
      if isHead s i then addLoop e fuel s (i + 1)
      else
        let o := fitOrder i e ORDERS 0
        addLoop e fuel (freeBlock ORDERS { s with managed := s.managed + 2 ^ o } i o) (i + 2 ^ o)
    else s

/-- `buddy_add_range` on page indices -/
def addRange (s : St) (i n : Nat) : St :=
  let e := min (i + n) s.npages
  addLoop e (e - i) s i

/-- `b->nfree[o]` -/
def nfree (s : St) (o : Nat) : Nat := (s.free.filter (fun b => b.ord == o)).length

/-! ## Invariants -/

def blocks (s : St) : List Block := s.free ++ s.alloc

def sumSize (l : List Block) : Nat := (l.map Block.size).sum

/-- every block is a naturally aligned power-of-two run inside the span -/
def WF (n : Nat) (b : Block) : Prop := b.ord < ORDERS ∧ 2 ^ b.ord ∣ b.idx ∧ b.idx + 2 ^ b.ord ≤ n

def Disj (a b : Block) : Prop := a.idx + 2 ^ a.ord ≤ b.idx ∨ b.idx + 2 ^ b.ord ≤ a.idx

def covers (b : Block) (p : Nat) : Prop := b.idx ≤ p ∧ p < b.idx + 2 ^ b.ord

/-- coalescing is complete: no free block has its buddy free at the same order -/
def Coal (s : St) : Prop :=
  ∀ b ∈ s.free, b.ord + 1 < ORDERS → buddyOf b.idx b.ord + 2 ^ b.ord ≤ s.npages →
    (⟨buddyOf b.idx b.ord, b.ord⟩ : Block) ∉ s.free

structure Core (s : St) : Prop where
  wf : ∀ b ∈ blocks s, WF s.npages b
  pw : (blocks s).Pairwise Disj
  fp : s.freePages = sumSize s.free
  coal : Coal s

/-- The allocator invariant. `managed = free + allocated` is "free + allocated = total". -/
def Inv (s : St) : Prop := Core s ∧ s.managed = s.freePages + sumSize s.alloc

/-! ## Arithmetic lemmas -/

theorem pow_pos' (o : Nat) : 0 < 2 ^ o := Nat.two_pow_pos o

theorem pow_succ2 (o : Nat) : 2 ^ (o + 1) = 2 ^ o + 2 ^ o := by
  rw [Nat.pow_succ]; omega

theorem buddy_cases {i o : Nat} (h : 2 ^ o ∣ i) :
    (2 ^ (o + 1) ∣ i ∧ buddyOf i o = i + 2 ^ o) ∨
    (2 ^ o ≤ i ∧ 2 ^ (o + 1) ∣ i - 2 ^ o ∧ buddyOf i o = i - 2 ^ o) := by
  obtain ⟨c, rfl⟩ := h
  have hm : 2 ^ o * c % 2 ^ (o + 1) = 2 ^ o * (c % 2) := by
    rw [Nat.pow_succ, Nat.mul_mod_mul_left]
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  · left
    refine ⟨?_, ?_⟩
    · exact Nat.dvd_of_mod_eq_zero (by rw [hm, hc, Nat.mul_zero])
    · simp [buddyOf, hm, hc]
  · right
    have hpos := pow_pos' o
    have hc1 : 1 ≤ c := by omega
    refine ⟨?_, ?_, ?_⟩
    · calc 2 ^ o = 2 ^ o * 1 := by omega
        _ ≤ 2 ^ o * c := Nat.mul_le_mul_left _ hc1
    · have : 2 ^ o * c - 2 ^ o = 2 ^ o * (c - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
      rw [this, Nat.pow_succ]
      exact Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero (by omega))
    · have : ¬ (2 ^ o * c % 2 ^ (o + 1) = 0) := by
        rw [hm, hc]; omega
      simp [buddyOf, this]

theorem dvd_pow_succ {i o : Nat} (h : 2 ^ (o + 1) ∣ i) : 2 ^ o ∣ i :=
  Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ o)) h

theorem buddy_add {i o : Nat} (h : 2 ^ (o + 1) ∣ i) : buddyOf (i + 2 ^ o) o = i := by
  have hlt : 2 ^ o < 2 ^ (o + 1) := by rw [pow_succ2]; have := pow_pos' o; omega
  have hm : (i + 2 ^ o) % 2 ^ (o + 1) = 2 ^ o := by
    obtain ⟨k, rfl⟩ := h
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hne : ¬ ((i + 2 ^ o) % 2 ^ (o + 1) = 0) := by rw [hm]; have := pow_pos' o; omega
  simp [buddyOf, hne]

theorem buddy_invol {i o : Nat} (h : 2 ^ o ∣ i) : buddyOf (buddyOf i o) o = i := by
  rcases buddy_cases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h2, buddy_add h1]
  · rw [h3]
    have hm : (i - 2 ^ o) % 2 ^ (o + 1) = 0 := Nat.mod_eq_zero_of_dvd h2
    simp [buddyOf, hm]; omega

theorem buddy_symm {c i o : Nat} (hc : 2 ^ o ∣ c) (h : buddyOf c o = i) : c = buddyOf i o := by
  rw [← h, buddy_invol hc]

theorem buddy_ne {i o : Nat} (h : 2 ^ o ∣ i) : buddyOf i o ≠ i := by
  have := pow_pos' o
  rcases buddy_cases h with ⟨_, h2⟩ | ⟨h1, _, h3⟩ <;> omega

theorem buddy_dvd {i o : Nat} (h : 2 ^ o ∣ i) : 2 ^ o ∣ buddyOf i o := by
  rcases buddy_cases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h2]; exact Nat.dvd_add h (Nat.dvd_refl _)
  · rw [h3]; exact dvd_pow_succ h2

theorem merge_cases {i o : Nat} (hal : 2 ^ o ∣ i) :
    (min i (buddyOf i o) = i ∧ buddyOf i o = i + 2 ^ o ∧ 2 ^ (o + 1) ∣ i) ∨
    (min i (buddyOf i o) = buddyOf i o ∧ buddyOf i o + 2 ^ o = i ∧ 2 ^ (o + 1) ∣ buddyOf i o) := by
  rcases buddy_cases hal with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · left; refine ⟨?_, h2, h1⟩; rw [h2]; exact Nat.min_eq_left (Nat.le_add_right _ _)
  · right; refine ⟨?_, by omega, by rw [h3]; exact h2⟩; rw [h3]; exact Nat.min_eq_right (Nat.sub_le _ _)

/-! ## List lemmas -/

theorem sumSize_append (l m : List Block) : sumSize (l ++ m) = sumSize l + sumSize m := by
  simp [sumSize, List.sum_append]

theorem sumSize_erase {l : List Block} {a : Block} (h : a ∈ l) :
    sumSize (l.erase a) + a.size = sumSize l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx; simp [sumSize, List.erase_cons_head]; omega
    · have ha : a ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      rw [List.erase_cons_tail (by simpa using hx)]
      have := ih ha
      simp [sumSize] at this ⊢; omega

theorem disj_symm {a b : Block} (h : Disj a b) : Disj b a := by
  unfold Disj at *; omega

theorem disj_irrefl (a : Block) : ¬ Disj a a := by
  unfold Disj; have := pow_pos' a.ord; omega

theorem pw_mem_erase {l : List Block} {x c : Block} (hp : l.Pairwise Disj) (hx : x ∈ l)
    (hc : c ∈ l.erase x) : Disj x c := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.pairwise_cons] at hp
    by_cases hy : y = x
    · subst hy
      rw [List.erase_cons_head] at hc
      exact hp.1 c hc
    · rw [List.erase_cons_tail (by simpa using hy)] at hc
      have hx' : x ∈ ys := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hy
        · exact h
      rcases List.mem_cons.mp hc with h | h
      · subst h; exact disj_symm (hp.1 x hx')
      · exact ih hp.2 hx' h

theorem mem_blocks_erase {s : St} {x c : Block} (h : c ∈ s.free.erase x ++ s.alloc) : c ∈ blocks s := by
  unfold blocks
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (List.mem_of_mem_erase h)
  · exact List.mem_append_right _ h

theorem pw_erase {s : St} (x : Block) (h : (blocks s).Pairwise Disj) :
    (s.free.erase x ++ s.alloc).Pairwise Disj :=
  h.sublist (List.Sublist.append (List.erase_sublist) (List.Sublist.refl _))

/-- disjointness of `c` from everything in a pairwise-disjoint list once `x` is erased -/
theorem disj_of_erase_free {s : St} {x c : Block} (hp : (blocks s).Pairwise Disj) (hx : x ∈ s.free)
    (hc : c ∈ s.free.erase x ++ s.alloc) : Disj x c := by
  have hxb : x ∈ blocks s := List.mem_append_left _ hx
  have : (blocks s).erase x = s.free.erase x ++ s.alloc := by
    unfold blocks; exact List.erase_append_left _ hx
  exact pw_mem_erase hp hxb (this ▸ hc)

theorem not_covers_disj {a b : Block} (h : ∀ p, covers a p → ¬ covers b p) : Disj a b := by
  unfold Disj; unfold covers at h
  have ha := pow_pos' a.ord; have hb := pow_pos' b.ord
  by_cases h1 : a.idx + 2 ^ a.ord ≤ b.idx
  · exact Or.inl h1
  · by_cases h2 : b.idx + 2 ^ b.ord ≤ a.idx
    · exact Or.inr h2
    · exfalso
      have := h (max a.idx b.idx); omega

/-! ## push / unlink preserve the core invariant -/

theorem push_core {s : St} {i o : Nat} (hc : Core s) (hw : WF s.npages ⟨i, o⟩)
    (hf : ∀ c ∈ blocks s, Disj ⟨i, o⟩ c)
    (hnew : o + 1 < ORDERS → buddyOf i o + 2 ^ o ≤ s.npages → (⟨buddyOf i o, o⟩ : Block) ∉ s.free)
    (hold : ∀ c ∈ s.free, c.ord = o → buddyOf c.idx c.ord = i → c.ord + 1 < ORDERS →
      buddyOf c.idx c.ord + 2 ^ c.ord ≤ s.npages → False) :
    Core (push s i o) := by
  obtain ⟨wf, pw, fp, coal⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [push, blocks, List.append_assoc, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl | hb
    · exact wf b (List.mem_append_left _ hb)
    · exact hw
    · exact wf b (List.mem_append_right _ hb)
  · simp only [push, blocks]
    have hperm : (s.free ++ ([⟨i, o⟩] : List Block) ++ s.alloc).Perm ((⟨i, o⟩ : Block) :: (s.free ++ s.alloc)) := by
      rw [List.append_assoc]; exact List.perm_middle
    rw [List.Perm.pairwise_iff (fun h => disj_symm h) hperm, List.pairwise_cons]
    exact ⟨hf, pw⟩
  · simp [push, sumSize_append, fp, sumSize, Block.size]
  · intro b hb hlt hle
    simp only [push, List.mem_append, List.mem_singleton] at hb ⊢
    rcases hb with hb | rfl
    · intro hm
      rcases hm with hm | hm
      · exact coal b hb hlt hle hm
      · cases hm
        exact (hold b hb rfl (by simpa using congrArg Block.idx ‹_›) hlt hle)
    · intro hm
      rcases hm with hm | hm
      · exact hnew hlt hle hm
      · have := congrArg Block.idx hm
        simp at this
        exact buddy_ne hw.2.1 this

theorem unlink_core {s : St} {x : Block} (hc : Core s) (hx : x ∈ s.free) :
    Core (unlink s x.idx x.ord) := by
  obtain ⟨wf, pw, fp, coal⟩ := hc
  have hx' : (⟨x.idx, x.ord⟩ : Block) = x := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb; exact wf b (mem_blocks_erase (by simpa [unlink, blocks, hx'] using hb))
  · simpa [unlink, blocks, hx'] using pw_erase x pw
  · have := sumSize_erase hx
    simp [unlink, hx', fp, Block.size] at this ⊢; omega
  · intro b hb hlt hle hm
    simp only [unlink, hx'] at hb hm hle
    exact coal b (List.mem_of_mem_erase hb) hlt hle (List.mem_of_mem_erase hm)

/-! ## free_block -/

/-- pages covered by blocks: `freeBlock` only adds the pages of the block being freed -/
def Covered (s : St) (p : Nat) : Prop := ∃ c ∈ blocks s, covers c p

theorem covered_push {s : St} {i o p : Nat} (h : Covered (push s i o) p) :
    Covered s p ∨ covers ⟨i, o⟩ p := by
  obtain ⟨c, hc, hp⟩ := h
  simp only [push, blocks, List.append_assoc, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl | hc
  · exact Or.inl ⟨c, List.mem_append_left _ hc, hp⟩
  · exact Or.inr hp
  · exact Or.inl ⟨c, List.mem_append_right _ hc, hp⟩

theorem covered_unlink {s : St} {i o p : Nat} (h : Covered (unlink s i o) p) : Covered s p := by
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, mem_blocks_erase (by simpa [unlink, blocks] using hc), hp⟩

theorem freeBlock_covered : ∀ (fuel : Nat) (s : St) (i o : Nat) (p : Nat),
    2 ^ o ∣ i → Covered (freeBlock fuel s i o) p → Covered s p ∨ covers ⟨i, o⟩ p
  | 0, s, i, o, p, _, h => covered_push h
  | fuel + 1, s, i, o, p, hal, h => by
    simp only [freeBlock] at h
    split at h
    · split at h
      · exact covered_push h
      · split at h
        · rename_i hb
          have hrec := freeBlock_covered fuel _ _ _ p ?_ h
          · rcases hrec with hr | hr
            · exact Or.inl (covered_unlink hr)
            · -- the merged block is the union of ⟨i,o⟩ and its buddy (a free block of s)
              have hpos := pow_pos' o
              rcases buddy_cases hal with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
              · unfold covers at hr; simp only [h2, pow_succ2] at hr
                by_cases hlo : p < i + 2 ^ o
                · right; unfold covers; simp; omega
                · left; refine ⟨⟨buddyOf i o, o⟩, List.mem_append_left _ hb, ?_⟩
                  unfold covers; simp [h2]; omega
              · unfold covers at hr; simp only [h3, pow_succ2] at hr
                by_cases hlo : p < i
                · left; refine ⟨⟨buddyOf i o, o⟩, List.mem_append_left _ hb, ?_⟩
                  unfold covers; simp [h3]; omega
                · right; unfold covers; simp; omega
          · rcases buddy_cases hal with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
            · rw [h2, Nat.min_eq_left (by omega)]; exact h1
            · rw [h3, Nat.min_eq_right (by omega)]; exact h2
        · exact covered_push h
    · exact covered_push h

theorem freeBlock_inv : ∀ (fuel : Nat) (s : St) (i o : Nat),
    10 ≤ fuel + o → Core s → WF s.npages ⟨i, o⟩ → (∀ c ∈ blocks s, Disj ⟨i, o⟩ c) →
    s.managed = s.freePages + sumSize s.alloc + 2 ^ o →
    Inv (freeBlock fuel s i o)
  | 0, s, i, o, hfuel, hc, hw, hf, hm => by
    refine ⟨push_core hc hw hf (fun h => by unfold ORDERS at h; omega) ?_, ?_⟩
    · intro c _ hco _ hlt; unfold ORDERS at hlt; omega
    · simp [freeBlock, push, hm]; omega
  | fuel + 1, s, i, o, hfuel, hc, hw, hf, hm => by
    have hpos := pow_pos' o
    have hal : 2 ^ o ∣ i := hw.2.1
    have hmp : (push s i o).managed = (push s i o).freePages + sumSize (push s i o).alloc := by
      simp [push, hm]; omega
    -- an old free block whose buddy is ⟨i,o⟩ is the buddy of ⟨i,o⟩
    have hsym : ∀ c ∈ s.free, c.ord = o → buddyOf c.idx c.ord = i → c = ⟨buddyOf i o, o⟩ := by
      intro c hcm hco hcb
      have hcw := hc.wf c (List.mem_append_left _ hcm)
      have := buddy_symm (hco ▸ hcw.2.1) (hco ▸ hcb)
      cases c; simp at hco this ⊢; exact ⟨this, hco⟩
    simp only [freeBlock]
    split
    · rename_i hord
      split
      · rename_i hout
        refine ⟨push_core hc hw hf (fun _ h => by omega) ?_, hmp⟩
        intro c hcm hco hcb _ _
        have := hsym c hcm hco hcb
        have hcw := hc.wf c (List.mem_append_left _ hcm)
        subst this; simp [WF] at hcw; omega
      · rename_i hin
        split
        · rename_i hb
          -- merge with the buddy and continue one order up
          have hbw := hc.wf _ (List.mem_append_left _ hb)
          have hcore := unlink_core (x := ⟨buddyOf i o, o⟩) hc hb
          have hfp := hc.fp
          have hsum := sumSize_erase hb
          apply freeBlock_inv fuel _ _ _ (by omega) hcore
          · have hwi : i + 2 ^ o ≤ s.npages := hw.2.2
            refine ⟨by simpa using hord, ?_, ?_⟩
            · show 2 ^ (o + 1) ∣ min i (buddyOf i o)
              rcases merge_cases hal with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1] <;> assumption
            · show min i (buddyOf i o) + 2 ^ (o + 1) ≤ s.npages
              rw [pow_succ2]
              rcases merge_cases hal with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1] <;> omega
          · intro c hcm
            have hcm' : c ∈ s.free.erase ⟨buddyOf i o, o⟩ ++ s.alloc := by simpa [unlink, blocks] using hcm
            have h1 := hf c (mem_blocks_erase hcm')
            have h2 := disj_of_erase_free hc.pw hb hcm'
            have hcp := pow_pos' c.ord
            unfold Disj at h1 h2 ⊢
            simp only at h1 h2 ⊢
            rw [pow_succ2]
            rcases merge_cases hal with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;> rw [e1] <;> omega
          · simp only [unlink]; rw [pow_succ2]
            simp [Block.size] at hsum; omega
        · rename_i hnb
          refine ⟨push_core hc hw hf (fun _ _ => hnb) ?_, hmp⟩
          intro c hcm hco hcb _ _
          have := hsym c hcm hco hcb
          subst this; exact hnb hcm
    · rename_i hord
      refine ⟨push_core hc hw hf (fun h => absurd h hord) ?_, hmp⟩
      intro c _ hco _ hlt _; rw [hco] at hlt; exact hord hlt

/-! ## buddy_free -/

theorem free_inv {s : St} {i : Nat} (h : Inv s) : Inv (free s i).2 := by
  unfold free
  split
  · exact h
  · rename_i b hb
    have hbm : b ∈ s.alloc := List.mem_of_find?_eq_some hb
    have hbi : b.idx = i := by simpa using List.find?_some hb
    obtain ⟨⟨wf, pw, fp, coal⟩, hm⟩ := h
    have hbw := wf b (List.mem_append_right _ hbm)
    have hblk : blocks { s with alloc := s.alloc.erase b } = (blocks s).erase b := by
      simp only [blocks]
      rw [List.erase_append_right]
      intro hbf
      exact disj_irrefl b (List.Pairwise.rel_of_mem_append (l₁ := s.free) (l₂ := s.alloc) (R := Disj)
        pw hbf hbm)
    apply freeBlock_inv _ _ _ _ (by unfold ORDERS; omega)
    · refine ⟨?_, ?_, fp, coal⟩
      · intro c hc; rw [hblk] at hc; exact wf c (List.mem_of_mem_erase hc)
      · rw [hblk]; exact pw.sublist (List.erase_sublist)
    · simpa [← hbi] using hbw
    · intro c hc; rw [hblk] at hc
      have := pw_mem_erase pw (List.mem_append_right _ hbm) hc
      simpa [← hbi] using this
    · have := sumSize_erase hbm
      simp [Block.size] at this ⊢; omega

/-- double free / wild free is rejected and changes nothing -/
theorem free_reject {s : St} {i : Nat} (h : ∀ b ∈ s.alloc, b.idx ≠ i) : free s i = (false, s) := by
  unfold free
  have : s.alloc.find? (fun b => b.idx == i) = none := by
    rw [List.find?_eq_none]; intro b hb; simpa using h b hb
  rw [this]

/-! ## buddy_alloc -/

/-- loop invariant of the split loop: the in-flight block `⟨i, o⟩` is owned by nobody -/
theorem split_inv : ∀ (o : Nat) (s : St) (i order : Nat),
    order ≤ o → Core s → WF s.npages ⟨i, o⟩ → (∀ c ∈ blocks s, Disj ⟨i, o⟩ c) →
    s.managed = s.freePages + sumSize s.alloc + 2 ^ o →
    let s' := split i order o s
    Core s' ∧ s'.npages = s.npages ∧ s'.alloc = s.alloc ∧ s'.managed = s.managed ∧
    WF s'.npages ⟨i, order⟩ ∧ (∀ c ∈ blocks s', Disj ⟨i, order⟩ c) ∧
    s'.managed = s'.freePages + sumSize s'.alloc + 2 ^ order
  | 0, s, i, order, hle, hc, hw, hf, hm => by
    have : order = 0 := by omega
    subst this; exact ⟨hc, rfl, rfl, rfl, hw, hf, hm⟩
  | o + 1, s, i, order, hle, hc, hw, hf, hm => by
    simp only [split]
    by_cases hlo : order ≤ o
    · rw [if_pos hlo]
      have hpos := pow_pos' o
      have hal : 2 ^ (o + 1) ∣ i := hw.2.1
      have hin : i + 2 ^ (o + 1) ≤ s.npages := hw.2.2
      rw [pow_succ2] at hin
      -- the upper half becomes free
      have hhw : WF s.npages ⟨i + 2 ^ o, o⟩ := by
        refine ⟨by have := hw.1; simp at this ⊢; omega, Nat.dvd_add (dvd_pow_succ hal) (Nat.dvd_refl _), ?_⟩
        show i + 2 ^ o + 2 ^ o ≤ s.npages; omega
      have hlow : (⟨i, o⟩ : Block) ∉ s.free := by
        intro hm'
        have := hf _ (List.mem_append_left _ hm')
        unfold Disj at this; simp at this; rw [pow_succ2] at this; omega
      have hpush : Core (push s (i + 2 ^ o) o) := by
        refine push_core hc hhw ?_ ?_ ?_
        · intro c hcm; have := hf c hcm; unfold Disj at this ⊢; simp at this ⊢
          rw [pow_succ2] at this; omega
        · intro _ _; rw [buddy_add hal]; exact hlow
        · intro c hcm hco hcb _ _
          have hcw := hc.wf c (List.mem_append_left _ hcm)
          have := buddy_symm (hco ▸ hcw.2.1) (hco ▸ hcb)
          rw [buddy_add hal] at this
          apply hlow; cases c; simp at hco this; subst hco; subst this; exact hcm
      have := split_inv o (push s (i + 2 ^ o) o) i order hlo hpush
        ⟨by have := hw.1; simp at this ⊢; omega, dvd_pow_succ hal, show i + 2 ^ o ≤ s.npages by omega⟩
        (by
          intro c hcm
          simp only [push, blocks, List.append_assoc, List.mem_append, List.mem_singleton] at hcm
          rcases hcm with hcm | rfl | hcm
          · have := hf c (List.mem_append_left _ hcm); unfold Disj at this ⊢; simp at this ⊢
            rw [pow_succ2] at this; omega
          · unfold Disj; simp
          · have := hf c (List.mem_append_right _ hcm); unfold Disj at this ⊢; simp at this ⊢
            rw [pow_succ2] at this; omega)
        (by simp [push, hm, pow_succ2]; omega)
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := this
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · rw [if_neg hlo]
      have : order = o + 1 := by omega
      subst this; exact ⟨hc, rfl, rfl, rfl, hw, hf, hm⟩

theorem findOrder_spec {s : St} {order o : Nat} (h : findOrder s order = some o) :
    o < ORDERS ∧ order ≤ o := by
  unfold findOrder at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp at h1 h2
  exact ⟨h2, h1.1⟩

/-- `buddy_alloc` preserves the invariant, and a returned block is naturally aligned, inside
the span, recorded as allocated, and overlaps no block that was free or allocated before
other than the free block it was carved from. -/
theorem alloc_inv {s : St} {order : Nat} (h : Inv s) : Inv (alloc s order).2 := by
  unfold alloc
  split
  · split
    · exact h
    · rename_i o ho
      split
      · exact h
      · rename_i b hb
        have hbm : b ∈ s.free := List.mem_of_find?_eq_some hb
        have hbo : b.ord = o := by simpa using List.find?_some hb
        have ⟨_, hle⟩ := findOrder_spec ho
        obtain ⟨hc, hm⟩ := h
        have hbw := hc.wf b (List.mem_append_left _ hbm)
        have hu := unlink_core hc hbm
        rw [hbo] at hu
        have hsum := sumSize_erase hbm
        obtain ⟨c1, _, c3, c4, c5, c6, c7⟩ := split_inv o (unlink s b.idx o) b.idx order hle hu
          (by rw [← hbo]; exact hbw)
          (by
            intro c hcm
            have hcm' : c ∈ s.free.erase b ++ s.alloc := by
              have : (⟨b.idx, o⟩ : Block) = b := by cases b; simp at hbo ⊢; exact hbo.symm
              simpa [unlink, blocks, this] using hcm
            have := disj_of_erase_free hc.pw hbm hcm'
            rw [← hbo]; exact this)
          (by simp [unlink]; have := hc.fp; simp [Block.size, hbo] at hsum; omega)
        refine ⟨⟨?_, ?_, c1.fp, ?_⟩, ?_⟩
        · intro x hx
          simp only [blocks, List.mem_append, List.mem_cons] at hx
          rcases hx with hx | rfl | hx
          · exact c1.wf x (List.mem_append_left _ hx)
          · simpa using c5
          · exact c1.wf x (List.mem_append_right _ hx)
        · simp only [blocks]
          have hperm : (_ ++ ((⟨b.idx, order⟩ : Block) :: _)).Perm
              ((⟨b.idx, order⟩ : Block) :: (blocks (split b.idx order o (unlink s b.idx o)))) :=
            List.perm_middle
          rw [List.Perm.pairwise_iff (fun h => disj_symm h) hperm, List.pairwise_cons]
          exact ⟨c6, c1.pw⟩
        · exact c1.coal
        · simp [sumSize, Block.size] at c7 ⊢; omega
  · exact h

theorem alloc_some {s : St} {order i : Nat} {s' : St} (h : Inv s) (ha : alloc s order = (some i, s')) :
    2 ^ order ∣ i ∧ i + 2 ^ order ≤ s.npages ∧ (⟨i, order⟩ : Block) ∈ s'.alloc ∧ s'.npages = s.npages := by
  unfold alloc at ha
  split at ha
  · split at ha
    · simp at ha
    · rename_i o ho
      split at ha
      · simp at ha
      · rename_i b hb
        simp only [Prod.mk.injEq, Option.some.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        have hbm : b ∈ s.free := List.mem_of_find?_eq_some hb
        have hbo : b.ord = o := by simpa using List.find?_some hb
        have ⟨_, hle⟩ := findOrder_spec ho
        obtain ⟨hc, hm⟩ := h
        have hbw := hc.wf b (List.mem_append_left _ hbm)
        have hu := unlink_core hc hbm
        rw [hbo] at hu
        have hsum := sumSize_erase hbm
        obtain ⟨_, c2, _, _, c5, _, _⟩ := split_inv o (unlink s b.idx o) b.idx order hle hu
          (by rw [← hbo]; exact hbw)
          (by
            intro c hcm
            have hcm' : c ∈ s.free.erase b ++ s.alloc := by
              have : (⟨b.idx, o⟩ : Block) = b := by cases b; simp at hbo ⊢; exact hbo.symm
              simpa [unlink, blocks, this] using hcm
            have := disj_of_erase_free hc.pw hbm hcm'
            rw [← hbo]; exact this)
          (by simp [unlink]; have := hc.fp; simp [Block.size, hbo] at hsum; omega)
        have c2' : (split b.idx order o (unlink s b.idx o)).npages = s.npages := by rw [c2]; rfl
        have c5' := c5.2.2
        rw [c2'] at c5'
        exact ⟨c5.2.1, c5', by simp, by simp [c2']⟩
  · simp at ha

/-- No two allocated blocks overlap (and none overlaps a free block): immediate from `Inv`. -/
theorem no_overlap {s : St} (h : Inv s) {a b : Block} (ha : a ∈ s.alloc) (hb : b ∈ s.alloc)
    (hne : a ≠ b) : ∀ p, ¬ (covers a p ∧ covers b p) := by
  have hpw := h.1.pw
  have hpw2 := (List.pairwise_append.mp hpw).2.1
  have : Disj a b := pw_mem_erase hpw2 ha ((List.mem_erase_of_ne (fun e => hne e.symm)).mpr hb)
  intro p ⟨h1, h2⟩; unfold Disj at this; unfold covers at h1 h2; omega

theorem alloc_aligned {s : St} {order i : Nat} {s' : St} (h : Inv s) (ha : alloc s order = (some i, s')) :
    i % 2 ^ order = 0 := Nat.mod_eq_zero_of_dvd (alloc_some h ha).1

/-! ## buddy_add_range -/

theorem fitOrder_spec : ∀ (fuel : Nat) (i e o : Nat), o < ORDERS → 2 ^ o ∣ i → i + 2 ^ o ≤ e →
    let o' := fitOrder i e fuel o
    o' < ORDERS ∧ 2 ^ o' ∣ i ∧ i + 2 ^ o' ≤ e
  | 0, _, _, _, h1, h2, h3 => ⟨h1, h2, h3⟩
  | fuel + 1, i, e, o, h1, h2, h3 => by
    simp only [fitOrder]
    split
    · rename_i hc
      exact fitOrder_spec fuel i e (o + 1) hc.1 (Nat.dvd_of_mod_eq_zero hc.2.1) hc.2.2
    · exact ⟨h1, h2, h3⟩

theorem isHead_false {s : St} {i e : Nat} (hi : i < e)
    (hr : ∀ c ∈ blocks s, ∀ p, i ≤ p → p < e → ¬ covers c p) : isHead s i = false := by
  unfold isHead
  rw [Bool.eq_false_iff]
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨c, hc, hci⟩ := h
  have : c.idx = i := by simpa using hci
  exact hr c hc i (Nat.le_refl _) hi ⟨by omega, by have := pow_pos' c.ord; omega⟩

theorem addLoop_inv : ∀ (fuel : Nat) (e : Nat) (s : St) (i : Nat),
    e ≤ s.npages → Inv s → (∀ c ∈ blocks s, ∀ p, i ≤ p → p < e → ¬ covers c p) →
    Inv (addLoop e fuel s i)
  | 0, _, s, _, _, h, _ => h
  | fuel + 1, e, s, i, he, h, hr => by
    simp only [addLoop]
    split
    · rename_i hi
      rw [isHead_false hi hr]
      simp only [Bool.false_eq_true, ite_false]
      have ⟨f1, f2, f3⟩ := fitOrder_spec ORDERS i e 0 (by unfold ORDERS; omega) (Nat.one_dvd _) (by simp; omega)
      generalize fitOrder i e ORDERS 0 = o at f1 f2 f3
      have hfb := freeBlock_inv ORDERS { s with managed := s.managed + 2 ^ o } i o
        (by unfold ORDERS; omega) ⟨h.1.wf, h.1.pw, h.1.fp, h.1.coal⟩ ⟨f1, f2, by simp; omega⟩
        (by
          intro c hc
          have := not_covers_disj (a := ⟨i, o⟩) (b := c) (by
            intro p hp hq
            unfold covers at hp; simp at hp
            exact hr c hc p hp.1 (by omega) hq)
          exact this)
        (by simp [h.2])
      apply addLoop_inv fuel e _ _ (by
        have : ∀ fu (s : St) i o, (freeBlock fu s i o).npages = s.npages := by
          intro fu; induction fu with
          | zero => intro s i o; simp [freeBlock, push]
          | succ n ih => intro s i o; simp only [freeBlock]; split <;> (try split) <;> (try split) <;> simp [push, ih, unlink]
        rw [this]; simpa using he) hfb
      intro c hc p hp1 hp2 hcv
      have := freeBlock_covered ORDERS { s with managed := s.managed + 2 ^ o } i o p f2 ⟨c, hc, hcv⟩
      rcases this with ⟨c0, hc0, hcv0⟩ | hcv0
      · exact hr c0 hc0 p (by have := pow_pos' o; omega) hp2 hcv0
      · unfold covers at hcv0; simp at hcv0; omega
    · exact h

/-- `buddy_add_range` of a range that overlaps no managed page preserves the invariant. -/
theorem addRange_inv {s : St} {i n : Nat} (h : Inv s)
    (hr : ∀ c ∈ blocks s, ∀ p, i ≤ p → p < i + n → ¬ covers c p) : Inv (addRange s i n) := by
  unfold addRange
  exact addLoop_inv _ _ s i (Nat.min_le_right _ _) h
    (fun c hc p h1 h2 => hr c hc p h1 (by have := Nat.min_le_left (i + n) s.npages; omega))

theorem init_inv (n : Nat) : Inv (St.init n) := by
  refine ⟨⟨?_, ?_, rfl, ?_⟩, rfl⟩
  · intro b hb; simp [blocks, St.init] at hb
  · simp [blocks, St.init]
  · intro b hb; simp [St.init] at hb

/-! ## alloc-then-free restores the allocator state -/

/-- the free blocks `split` creates, highest order first -/
def splitList (i order : Nat) : Nat → List Block
  | 0 => []
  | o + 1 => if order ≤ o then ⟨i + 2 ^ o, o⟩ :: splitList i order o else []

theorem split_eq : ∀ (o : Nat) (i order : Nat) (s : St),
    split i order o s = { s with free := s.free ++ splitList i order o,
                                 freePages := s.freePages + sumSize (splitList i order o) }
  | 0, i, order, s => by simp [split, splitList, sumSize]
  | o + 1, i, order, s => by
    simp only [split, splitList]
    by_cases h : order ≤ o
    · rw [if_pos h, if_pos h, split_eq o]
      simp [push, sumSize, Block.size, List.append_assoc]; omega
    · rw [if_neg h, if_neg h]; simp [sumSize]

theorem splitList_self (i order : Nat) : splitList i order order = [] := by
  cases order with
  | zero => rfl
  | succ n => simp [splitList]

theorem splitList_snoc : ∀ (o : Nat) (i order : Nat), order < o →
    splitList i order o = splitList i (order + 1) o ++ [⟨i + 2 ^ order, order⟩]
  | 0, _, _, h => by omega
  | o + 1, i, order, h => by
    simp only [splitList]
    rw [if_pos (by omega : order ≤ o)]
    by_cases h2 : order + 1 ≤ o
    · rw [if_pos h2, splitList_snoc o i order (by omega)]; simp
    · have : order = o := by omega
      subst this; rw [if_neg h2, splitList_self]; simp

theorem splitList_mem {i order o : Nat} {x : Block} (h : x ∈ splitList i order o) :
    order ≤ x.ord ∧ x.ord < o ∧ x.idx = i + 2 ^ x.ord := by
  induction o with
  | zero => simp [splitList] at h
  | succ n ih =>
    simp only [splitList] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp; omega
      · have := ih h; omega
    · simp at h

theorem erase_snoc {l : List Block} {x : Block} (h : x ∉ l) : (l ++ [x]).erase x = l := by
  rw [List.erase_append_right _ h]; simp

theorem pow_le_pow' {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h

theorem buddy_of_aligned {i o : Nat} (h : 2 ^ (o + 1) ∣ i) : buddyOf i o = i + 2 ^ o := by
  simp [buddyOf, Nat.mod_eq_zero_of_dvd h]

/-- freeing `⟨i, order⟩` re-merges, one order at a time, exactly the blocks `split` created -/
theorem freeBlock_unsplit (i o : Nat) (L : List Block) (hal : 2 ^ o ∣ i) (ho : o < ORDERS)
    (hL : ∀ x ∈ L, ∀ j, j < o → x ≠ ⟨i + 2 ^ j, j⟩) :
    ∀ (k order fuel : Nat) (s : St), o = order + k → 10 ≤ fuel + order →
    i + 2 ^ o ≤ s.npages → s.free = L ++ splitList i order o →
    freeBlock fuel s i order =
      freeBlock (fuel - k) { s with free := L, freePages := s.freePages - sumSize (splitList i order o) } i o
  | 0, order, fuel, s, hk, _, _, hf => by
    have : order = o := by omega
    subst this
    rw [splitList_self] at hf ⊢
    simp at hf
    have : ({ s with free := L, freePages := s.freePages - sumSize [] } : St) = s := by
      obtain ⟨n, fr, al, fp, mg⟩ := s
      simp only at hf
      subst hf
      simp [sumSize]
    rw [this]; rfl
  | k + 1, order, fuel, s, hk, hfuel, hn, hf => by
    have hpo := pow_pos' order
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by unfold ORDERS at ho; omega⟩
    have hal1 : 2 ^ (order + 1) ∣ i := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hal
    have hb : buddyOf i order = i + 2 ^ order := buddy_of_aligned hal1
    have hsnoc := splitList_snoc o i order (by omega)
    have hx : (⟨i + 2 ^ order, order⟩ : Block) ∉ L ++ splitList i (order + 1) o := by
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hL _ hm order (by omega) rfl
      · have := splitList_mem hm; simp at this; omega
    have hmem : (⟨buddyOf i order, order⟩ : Block) ∈ s.free := by
      rw [hf, hsnoc, hb]; simp
    have hle : 2 ^ (order + 1) ≤ 2 ^ o := pow_le_pow' (by omega)
    simp only [freeBlock]
    rw [if_pos (by unfold ORDERS at ho ⊢; omega)]
    rw [if_neg (by rw [hb]; rw [pow_succ2] at hle; omega)]
    rw [if_pos hmem]
    rw [Nat.min_eq_left (by omega)]
    have hrec := freeBlock_unsplit i o L hal ho hL k (order + 1) f (unlink s (buddyOf i order) order)
      (by omega) (by omega) (by simpa [unlink] using hn)
      (by simp only [unlink]; rw [hf, hsnoc, hb, ← List.append_assoc, erase_snoc hx])
    rw [hrec, show f + 1 - (k + 1) = f - k by omega]
    congr 1
    simp only [unlink]
    rw [hsnoc]
    simp [sumSize_append, sumSize, Block.size, Nat.sub_sub]
    omega

/-- **alloc-then-free restores the state**: `buddy_free(buddy_alloc(order))` succeeds and gives
back exactly the original allocator state, up to the order of blocks inside the free lists. -/
theorem alloc_free_roundtrip {s : St} {order i : Nat} {s' : St} (h : Inv s)
    (ha : alloc s order = (some i, s')) :
    (free s' i).1 = true ∧ (free s' i).2.free.Perm s.free ∧ (free s' i).2.alloc = s.alloc ∧
    (free s' i).2.freePages = s.freePages ∧ (free s' i).2.managed = s.managed ∧
    (free s' i).2.npages = s.npages := by
  unfold alloc at ha
  split at ha
  · split at ha
    · simp at ha
    · rename_i o ho
      split at ha
      · simp at ha
      · rename_i b hb
        simp only [Prod.mk.injEq, Option.some.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        have hbm : b ∈ s.free := List.mem_of_find?_eq_some hb
        have hbo : b.ord = o := by simpa using List.find?_some hb
        have ⟨hoO, hle⟩ := findOrder_spec ho
        obtain ⟨hc, hm⟩ := h
        have hbw := hc.wf b (List.mem_append_left _ hbm)
        have hbeq : (⟨b.idx, o⟩ : Block) = b := by cases b; simp at hbo ⊢; exact hbo.symm
        have hal : 2 ^ o ∣ b.idx := by rw [← hbo]; exact hbw.2.1
        have hin : b.idx + 2 ^ o ≤ s.npages := by rw [← hbo]; exact hbw.2.2
        have hsum := sumSize_erase hbm
        have hfp := hc.fp
        have hfind : List.find? (fun x : Block => x.idx == b.idx) (⟨b.idx, order⟩ :: s.alloc) =
            some ⟨b.idx, order⟩ := by simp
        rw [split_eq]
        simp only [free, unlink, hbeq]
        rw [hfind]
        simp only [List.erase_cons_head]
        refine ⟨by simp, ?_⟩
        have hL : ∀ x ∈ s.free.erase b, ∀ j, j < o → x ≠ ⟨b.idx + 2 ^ j, j⟩ := by
          intro x hx j hj hxe
          have := disj_of_erase_free hc.pw hbm (List.mem_append_left _ hx)
          subst hxe; unfold Disj at this; rw [hbo] at this; simp at this
          have : 2 ^ j < 2 ^ o := Nat.pow_lt_pow_right (by omega) hj
          have := pow_pos' j
          omega
        rw [freeBlock_unsplit b.idx o (s.free.erase b) hal hoO hL (o - order) order ORDERS _
          (by omega) (by unfold ORDERS; omega) (by simpa using hin) rfl]
        obtain ⟨f, hf⟩ : ∃ f, ORDERS - (o - order) = f + 1 :=
          ⟨ORDERS - (o - order) - 1, by unfold ORDERS at hoO ⊢; omega⟩
        rw [hf]
        -- at the top order the buddy is not free (coalescing invariant), so the block is pushed
        have hcoal := hc.coal b hbm
        rw [hbo] at hcoal
        have hnot : o + 1 < ORDERS → (⟨buddyOf b.idx o, o⟩ : Block) ∉ s.free.erase b := by
          intro hO hm'
          have hw' := hc.wf _ (List.mem_append_left _ (List.mem_of_mem_erase hm'))
          exact hcoal hO hw'.2.2 (List.mem_of_mem_erase hm')
        have hpush : ∀ (t : St), t.free = s.free.erase b →
            freeBlock (f + 1) t b.idx o = push t b.idx o := by
          intro t ht
          simp only [freeBlock]
          split
          · rename_i hO
            split
            · rfl
            · rw [ht, if_neg (hnot hO)]
          · rfl
        rw [hpush _ rfl]
        simp only [push, hbeq]
        refine ⟨(List.perm_append_singleton _ _).trans (List.perm_cons_erase hbm).symm, by simp, ?_, by simp, by simp⟩
        have hsz : b.size = 2 ^ o := by simp [Block.size, hbo]
        rw [hsz, ← hfp] at hsum
        show s.freePages - 2 ^ o + sumSize (splitList b.idx order o) - sumSize (splitList b.idx order o) + 2 ^ o = s.freePages
        omega
  · simp at ha

/-! ## A real bug: overlapping `buddy_add_range` double-manages pages

`buddy_add_range`'s "already managed; skip (overlapping add)" check only looks at the
metadata byte of the *head* page of each candidate block. A range that starts inside an
existing free block passes the check, so its pages are inserted a second time.
`mm_init` never issues overlapping adds, so the kernel does not hit this today; the API comment
claims overlapping adds are handled. The differential test reproduces the same behaviour in
the C code (`tests/test_buddy_diff.py::test_overlapping_add_range_bug`). -/

def bugState : St := addRange (addRange (St.init 4) 0 4) 1 1

theorem bug_state_free : bugState.free = [⟨0, 2⟩, ⟨1, 0⟩] ∧ bugState.freePages = 5 := by decide

theorem bug_breaks_invariant : ¬ Inv bugState := by
  intro h
  have hp := h.1.pw
  have : blocks bugState = [⟨0, 2⟩, ⟨1, 0⟩] := by decide
  rw [this] at hp
  simp [Disj] at hp

/-- after the bad add, two live allocations overlap: page 1 is handed out twice -/
theorem bug_double_allocation :
    (alloc bugState 0).1 = some 1 ∧ (alloc (alloc bugState 0).2 2).1 = some 0 := by decide

end Buddy
