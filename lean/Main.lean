import OrbitProofs

/-!
`orbitmodel` runs the *same definitions the proofs are about* (`Buddy.alloc`, `Mmu.mapRange`,
...) on commands read from stdin, speaking the protocol of the C drivers in `harness/`, so the
Python differential tests can compare the verified model with the real C code line by line.

    orbitmodel buddy      init N | add I N | alloc O | free I | state
    orbitmodel mmu        reset | map VA PA SIZE PROT | layout ... | dump lo|hi LO HI | query lo|hi VA  (hex)
-/

def parseHex (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
      else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0
    acc * 16 + d) 0

def hex (n : Nat) : String := String.mk (Nat.toDigits 16 n)

def clean (s : String) : String :=
  String.mk (s.toList.filter (fun c => c.toNat != 10 && c.toNat != 13))

def words (s : String) : List String := ((clean s).splitOn " ").filter (· ≠ "")

partial def loop (step : String → IO Unit) : IO Unit := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := clean line
  if !l.isEmpty then step l
  (← IO.getStdout).flush
  loop step

def buddyMain : IO Unit := do
  let st ← IO.mkRef (Buddy.St.init 0)
  loop fun l => do
    match words l with
    | ["init", n] => st.set (Buddy.St.init (min n.toNat! 4096)); IO.println "ok"
    | ["add", i, n] => st.modify (fun s => Buddy.addRange s i.toNat! n.toNat!); IO.println "ok"
    | ["alloc", o] =>
      let (r, s') := Buddy.alloc (← st.get) o.toNat!
      st.set s'
      IO.println (match r with | some i => toString i | none => "-1")
    | ["free", i] =>
      let (ok, s') := Buddy.free (← st.get) i.toNat!
      st.set s'
      IO.println (if ok then "0" else "-1")
    | ["state"] =>
      let s ← st.get
      IO.println (String.intercalate " " (toString s.freePages ::
        (List.range Buddy.ORDERS).map (fun o => toString (Buddy.nfree s o))))
    | _ => IO.eprintln s!"bad command: {l}"

def dump (t : Mmu.PT) (lo hi : Nat) : IO Unit := do
  let mut run : Option (Nat × Nat × Nat × Nat) := none   -- va, pa, n, attrs
  let mut va := lo
  while va < hi do
    match Mmu.walk t va with
    | some (pa, att) =>
      match run with
      | some (rva, rpa, rn, rat) =>
        if va == rva + rn * 4096 && pa == rpa + rn * 4096 && att == rat then
          run := some (rva, rpa, rn + 1, rat)
        else
          IO.println s!"{hex rva} {hex rpa} {hex rn} {hex rat}"
          run := some (va, pa, 1, att)
      | none => run := some (va, pa, 1, att)
    | none => pure ()
    va := va + 4096
  if let some (rva, rpa, rn, rat) := run then
    IO.println s!"{hex rva} {hex rpa} {hex rn} {hex rat}"
  IO.println "end"

def mmuMain : IO Unit := do
  let lo ← IO.mkRef Mmu.empty
  let hiT ← IO.mkRef Mmu.empty
  loop fun l => do
    match words l with
    | ["reset"] => lo.set Mmu.empty; hiT.set Mmu.empty; IO.println "ok"
    | ["map", va, pa, sz, p] =>
      lo.modify (fun t => Mmu.mapRange t (parseHex va) (parseHex pa) (parseHex sz) (parseHex p))
      IO.println "ok"
    | "layout" :: args =>
      match args.map parseHex with
      | [ks, uts, ute, te, re, uss, use, kend, ramb, rams, devb, devs, dtb, dtbs] =>
        let L : Mmu.Layout := ⟨ks, uts, ute, te, re, uss, use, (kend + 4095) / 4096 * 4096, ramb,
          min rams (4 * 1024 * 1024 * 1024), dtb, dtbs, devb, devs⟩
        lo.set (Mmu.mapAll Mmu.empty (Mmu.ttbr0 L))
        hiT.set (Mmu.mapAll Mmu.empty (Mmu.ttbr1 L))
        IO.println "ok"
      | _ => IO.eprintln "bad layout"
    | ["dump", "lo", a, b] => dump (← lo.get) (parseHex a) (parseHex b)
    | ["query", root, a] =>
      let t ← if root == "hi" then hiT.get else lo.get
      IO.println (match Mmu.walk t (parseHex a) with
        | some (pa, att) => s!"{a} {hex pa} {hex att}"
        | none => s!"{a} fault")
    | ["dump", "hi", a, b] => dump (← hiT.get) (parseHex a) (parseHex b)
    | _ => IO.eprintln s!"bad command: {l}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["buddy"] => buddyMain; return 0
  | ["mmu"] => mmuMain; return 0
  | _ => IO.eprintln "usage: orbitmodel buddy|mmu"; return 2
