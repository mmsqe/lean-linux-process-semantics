/-
  * decoder — a small CLI over `Decode.decodeAny`.

  Reads whitespace-separated hex instruction words (with or without a
  `0x` prefix), one per line or many per line, and prints the decoded
  instruction and its encoded length.  With `--width 16` it decodes
  compressed halfwords directly.

  This exists so the port can be differentially tested against
  `objdump -d` (or any other reference decoder) when one is available:
  feed the same words to both and diff.

  Usage:
      lake exe decoder < words.txt
      printf '0x00000013\n0x8082\n' | lake exe decoder
-/
import LinuxSem.Riscv.DecodeC

open LinuxSem.Riscv

/-- Parse `0x`-prefixed or bare hexadecimal. -/
def parseHex (s : String) : Option Nat :=
  let s := if s.startsWith "0x" || s.startsWith "0X" then (s.drop 2).toString else s
  if s.isEmpty then none
  else
    let digits := s.toList
    if digits.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) then
      some (digits.foldl (fun acc c =>
        let d := if c.isDigit then c.toNat - '0'.toNat
                 else if 'a' ≤ c then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10
        acc * 16 + d) 0)
    else none

def main (args : List String) : IO UInt32 := do
  let width :=
    match args with
    | "--width" :: "16" :: _ => 16
    | _ => 32
  let stdin ← IO.getStdin
  let hadError ← IO.mkRef false
  let mut line := (← stdin.getLine).trimAscii.toString
  while !line.isEmpty do
    for tok in line.splitOn " " do
      if !tok.isEmpty then
        match parseHex tok with
        | none =>
            IO.eprintln s!"decoder: not a hex word: {tok}"
            hadError.set true
        | some n =>
            if width == 16 then
              match decode16 (BitVec.ofNat 16 n) with
              | some ci => IO.println s!"{tok}\t{repr ci}\t2"
              | none => IO.println s!"{tok}\t<none>\t2"
            else
              match decodeAny (BitVec.ofNat 32 n) with
              | some (i, len) => IO.println s!"{tok}\t{repr i}\t{len}"
              | none => IO.println s!"{tok}\t<none>\t4"
    line := (← stdin.getLine).trimAscii.toString
  return if (← hadError.get) then 1 else 0
