/-
  * Sem: the abstract RV64GC semantics, as a first-order effect tree.


  The semantics is a plain function

      exec : word -> instr -> core -> eff

  from a decoded instruction and the CORE state (registers, FP registers,
  pc, fcsr, LR/SC reservation) to a finite, first-order tree of residual
  effects.  There is no monad parameter and no typeclass: core state is
  threaded concretely through the continuations, and only the operations
  this semantics deliberately does NOT interpret appear as tree nodes:

  - `ELoad n a k` / `EStore n a v k`: the MEMORY boundary.  Memory belongs
    to the interpreter (`RiscvSemantics`); the semantics only issues sized
    little-endian accesses.  `n` is the access width in bits.
  - `EEcall c` / `EEbreak c`: the process/hardware split.  They carry the
    core state with pc ALREADY ADVANCED.
  - `EIllegal c`: an undecodable fetch or a CSR address this model does
    not implement.  The MODEL declining, not the architecture.
  - `EDefinedIllegal c`: the ARCHITECTURE defines this instruction to raise
    an illegal-instruction exception (a CSR write to a read-only address).
    The carried core is the PRE-state: nothing retires.
  - `EFault c`: the instruction TRAPS by the ISA's own rules (misaligned
    atomics).  The carried core is the PRE-state.
  - `EDone c`: the instruction retired with core state `c`.

  Every instruction terminates, so `eff` is a plain inductive and an
  interpreter is a structural fixpoint — no fuel, no coinduction.

  Design decisions (unchanged):
  - x0 hardwiring lives HERE, in the `rget`/`rset` wrappers over a dumb
    `bvmap` register store.
  - fcsr is the ONLY stored FP CSR; fflags (0x001) and frm (0x002) are
    read and written as slices of it.
  - AMOs compose from plain sized loads/stores: a deliberately
    sequential, single-hart memory model.
  - FP: F and D execute HERE, in full.  The IEEE side lives in `Fpu`; this
    file owns the ISA side: which register file each operand comes from,
    NaN boxing of single-precision values, resolving the instruction's
    rounding-mode field against fcsr's frm, and accruing the flags into
    fcsr[4:0].  A reserved rounding mode is `EIllegal`, not a default.

  PC-advance contract: `exec sz i` reads pc once, and for every
  non-control-flow instruction the resulting core carries pc := pc + sz.
  Branches/jumps instead carry their target (a not-taken branch carries
  pc + sz); the link value of jal/jalr is pc + sz.
-/
import LinuxSem.Riscv.Prelude
import LinuxSem.Riscv.Instr
import LinuxSem.Riscv.Fpu

namespace LinuxSem.Riscv

open LinuxSem.Flocq

/-! ## Pure helpers -/

def w0 : word := 0
def w1 : word := 1

def low32 (v : word) : BitVec 32 := bits 0 32 v

def is_x0 (r : reg) : Bool := r.toNat == 0

/-- Integer ALU at any width.  Shift amounts are masked to the low
    `log2 n` bits (6 for n=64, 5 for n=32), per the ISA; `shmask` is that
    mask. -/
def alu {n : Nat} (shmask : Int) (op : AluOp) (a b : BitVec n) : BitVec n :=
  let sh (x : BitVec n) : Nat := (x &&& BitVec.ofInt n shmask).toNat
  match op with
  | .ADD => a + b
  | .SUB => a - b
  | .SLL => a <<< sh b
  | .SLT => if bv_lts a b then BitVec.ofInt n 1 else BitVec.ofInt n 0
  | .SLTU => if bv_ltu a b then BitVec.ofInt n 1 else BitVec.ofInt n 0
  | .XOR => a ^^^ b
  | .SRL => a >>> sh b
  | .SRA => a.sshiftRight (sh b)
  | .OR => a ||| b
  | .AND => a &&& b

def alu64 : AluOp → word → word → word := alu 63
def alu32 : AluOp → BitVec 32 → BitVec 32 → BitVec 32 := alu 31

def branch_taken (c : BranchCond) (a b : word) : Bool :=
  match c with
  | .EQ => bv_eqb a b
  | .NE => !(bv_eqb a b)
  | .LT => bv_lts a b
  | .GE => !(bv_lts a b)
  | .LTU => bv_ltu a b
  | .GEU => !(bv_ltu a b)

/-- M extension at any width; MULH* shift the exact product right by the
    width.  RISC-V division is TRUNCATING (`sdiv`/`srem`, not floor
    division).  Division by zero: div/divu = all ones, rem/remu = the
    dividend.  Signed overflow (min / -1) needs no special case. -/
def mul_div {n : Nat} (op : MulOp) (a b : BitVec n) : BitVec n :=
  let div0 := b.toNat == 0
  match op with
  | .MUL => a * b
  | .MULH => bv_mulhss a b
  | .MULHSU => bv_mulhsu a b
  | .MULHU => bv_mulhuu a b
  | .DIV => if div0 then BitVec.ofInt n (-1) else a.sdiv b
  | .DIVU => if div0 then BitVec.ofInt n (-1) else a.udiv b
  | .REM => if div0 then a else a.srem b
  | .REMU => if div0 then a else a.umod b

/-- Natural alignment for the A extension. -/
def amo_bytes : AWidth → Int
  | .W => 4
  | .D => 8

def amo_aligned (wd : AWidth) (a : word) : Bool :=
  a.toNat % (amo_bytes wd).toNat == 0

/-- AMO combine function (`old` is the memory value). -/
def amo_val {n : Nat} (op : AmoOp) (old src : BitVec n) : BitVec n :=
  match op with
  | .SWAP => src
  | .ADD => old + src
  | .XOR => old ^^^ src
  | .AND => old &&& src
  | .OR => old ||| src
  | .MIN => if bv_lts old src then old else src
  | .MAX => if bv_lts old src then src else old
  | .MINU => if bv_ltu old src then old else src
  | .MAXU => if bv_ltu old src then src else old

/-! ## Read-only CSRs -/

/-- The CSR address encodes its own writability: csr[11:10] = 11 is
    read-only. -/
def csr_read_only (csr : BitVec 12) : Bool :=
  ((csr.toNat >>> 10) &&& 3) == 3

/-- The write side of a CSR instruction is architecturally illegal exactly
    when it happens at all and the address is read-only. -/
def csr_write_illegal (writes : Bool) (csr : BitVec 12) : Bool :=
  writes && csr_read_only csr

/-- CSR address map: only the fcsr aliases exist; each is a (lo, len)
    slice of the stored 32-bit fcsr. -/
def csr_slice (csr : BitVec 12) : Option (Int × Int) :=
  let c := csr.toNat
  if c = 1 then some (0, 5)
  else if c = 2 then some (5, 3)
  else if c = 3 then some (0, 8)
  else none

/-- The read-only fault arm cannot swallow an instruction this model
    answers: every address `csr_slice` resolves is read/write. -/
theorem csr_read_only_unimplemented (csr : BitVec 12)
    (h : csr_read_only csr = true) : csr_slice csr = none := by
  unfold csr_slice at *
  unfold csr_read_only at h
  by_cases h1 : csr.toNat = 1
  · simp [h1] at h
  · by_cases h2 : csr.toNat = 2
    · simp [h2] at h
    · by_cases h3 : csr.toNat = 3
      · simp [h3] at h
      · simp [h1, h2, h3]

def slice_get (f : BitVec 32) (lo len : Int) : word :=
  BitVec.ofInt 64 (((f.toNat >>> lo.toNat) &&& (2 ^ len.toNat - 1) : Nat) : Int)

def slice_set (f : BitVec 32) (lo len : Int) (v : word) : BitVec 32 :=
  let mask : Nat := (2 ^ len.toNat - 1) <<< lo.toNat
  let nmask : Nat := Nat.xor mask (2 ^ 32 - 1)
  BitVec.ofInt 32 (((f.toNat &&& nmask) ||| ((v.toNat <<< lo.toNat) &&& mask) : Nat) : Int)

/-- NaN boxing for single-precision values in 64-bit FP registers. -/
def nan_box (v : BitVec 32) : word := (BitVec.ofInt 32 (-1)).append v

/-- An S-format input that is not properly NaN-boxed is treated as the
    canonical NaN. -/
def unbox_s (v : word) : BitVec 32 :=
  if (bits 32 32 v).toNat == 2 ^ 32 - 1 then low32 v
  else BitVec.ofInt 32 0x7fc00000

/-- Sign injection at any width (n = 32 after unboxing, or 64). -/
def sgnj_val {n : Nat} (op : FsgnOp) (a b : BitVec n) : BitVec n :=
  let sa := bit (n - 1) a
  let sb := bit (n - 1) b
  let s := match op with
           | .SGNJ => sb
           | .SGNJN => !sb
           | .SGNJX => xor sa sb
  (a &&& BitVec.ofInt n ((2 : Int) ^ (n - 1) - 1))
    ||| BitVec.ofInt n (if s then (2 : Int) ^ (n - 1) else 0)

/-! ## Core state: what the ISA owns -/

structure core : Type where
  c_regs : BvMap word
  c_fregs : BvMap word
  c_pc : word
  c_fcsr : BitVec 32
  c_resv : Option word

/-- Hand-written field updaters (extraction-friendly). -/
def with_regs (f : BvMap word → BvMap word) (c : core) : core :=
  ⟨f c.c_regs, c.c_fregs, c.c_pc, c.c_fcsr, c.c_resv⟩
def with_fregs (f : BvMap word → BvMap word) (c : core) : core :=
  ⟨c.c_regs, f c.c_fregs, c.c_pc, c.c_fcsr, c.c_resv⟩
def with_pc (v : word) (c : core) : core :=
  ⟨c.c_regs, c.c_fregs, v, c.c_fcsr, c.c_resv⟩
def with_fcsr (v : BitVec 32) (c : core) : core :=
  ⟨c.c_regs, c.c_fregs, c.c_pc, v, c.c_resv⟩
def with_resv (v : Option word) (c : core) : core :=
  ⟨c.c_regs, c.c_fregs, c.c_pc, c.c_fcsr, v⟩

/-- Register stores are dumb `bvmap`s; missing keys read as 0. -/
def reg_get (rm : BvMap word) (r : reg) : word :=
  (bvmapGet r rm).getD w0

/-- x0 hardwiring: reads 0, writes discarded. -/
def rget (c : core) (r : reg) : word :=
  if is_x0 r then w0 else reg_get c.c_regs r

def rset (r : reg) (v : word) (c : core) : core :=
  if is_x0 r then c else with_regs (bvmapSet r v) c

def fget (c : core) (r : reg) : word := reg_get c.c_fregs r

def fset (r : reg) (v : word) (c : core) : core :=
  with_fregs (bvmapSet r v) c

/-! ## The FP register file's ISA-side plumbing -/

def fp_format : FFmt → format
  | .S => fmt_single
  | .D => fmt_double

def fread (c : core) (fmt : FFmt) (r : reg) : Int :=
  match fmt with
  | .S => (unbox_s (fget c r)).toNat
  | .D => (fget c r).toNat

def fwrite (fmt : FFmt) (r : reg) (v : Int) (c : core) : core :=
  match fmt with
  | .S => fset r (nan_box (BitVec.ofInt 32 v)) c
  | .D => fset r (BitVec.ofInt 64 v) c

/-- fcsr[7:5] is frm, the DYNAMIC rounding mode. -/
def frm_of (c : core) : Int :=
  ((c.c_fcsr.toNat >>> 5) &&& 7 : Nat)

def resolve_rm (rm : BitVec 3) (c : core) : Option rmode :=
  rmode_of_field rm.toNat (frm_of c)

/-- Flags ACCRUE: fcsr[4:0] is sticky. -/
def accrue (fl : fflags) (c : core) : core :=
  with_fcsr (BitVec.ofInt 32 ((c.c_fcsr.toNat ||| (fflags_bits fl).toNat : Nat) : Int)) c

/-- A store or AMO from this hart to the reserved address invalidates the
    LR/SC reservation. -/
def inval_resv (a : word) (c : core) : core :=
  match c.c_resv with
  | some r => if r.toNat == a.toNat then with_resv none c else c
  | none => c

/-! ## The effect tree -/

inductive eff : Type where
  | eDone (c : core)
  | eIllegal (c : core)
  | eDefinedIllegal (c : core)
  | eEcall (c : core)
  | eEbreak (c : core)
  | eFault (c : core)
  | eLoad (n : Nat) (a : word) (k : BitVec n → eff)
  | eStore (n : Nat) (a : word) (v : BitVec n) (k : eff)

/-- Load a value of size `sz`: the interpreter answers with the `n` bits at
    `a` assembled little-endian; signed loads sign-extend, unsigned
    zero-extend (for SZ8 both are the identity). -/
def load_val (sz : MSize) (sgn : Bool) (a : word) (k : word → eff) : eff :=
  match sz with
  | .SZ1 => .eLoad 8 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | .SZ2 => .eLoad 16 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | .SZ4 => .eLoad 32 a (fun v => k (if sgn then sext 64 v else zext 64 v))
  | .SZ8 => .eLoad 64 a k

def store_val (sz : MSize) (a : word) (v : word) (k : eff) : eff :=
  match sz with
  | .SZ1 => .eStore 8 a (bits 0 8 v) k
  | .SZ2 => .eStore 16 a (bits 0 16 v) k
  | .SZ4 => .eStore 32 a (low32 v) k
  | .SZ8 => .eStore 64 a v k

/-- CSR access (`writes` is the write-enable, and the read-always
    boundary). -/
def exec_csr (op : CsrOp) (rd : reg) (operand : word)
    (writes : Bool) (csr : BitVec 12) (c : core) : eff :=
  match csr_slice csr with
  | none => .eIllegal c
  | some (lo, len) =>
      let f := c.c_fcsr
      let old := slice_get f lo len
      let newv : word :=
        match op with
        | .RW => operand
        | .RS => old ||| operand
        | .RC => old &&& ~~~operand
      .eDone (rset rd old
               (if writes then with_fcsr (slice_set f lo len newv) c else c))

/-! ## The semantics -/

/-- Execute one already-decoded instruction, including the pc update. -/
def exec (sz : word) (i : Instr) (c : core) : eff :=
  let pc := c.c_pc
  let npc := pc + sz
  let cn := with_pc npc c
  match i with
  -- RV64I
  | .lui rd imm =>
      .eDone (rset rd (sext 64 (imm.append (0 : BitVec 12))) cn)
  | .auipc rd imm =>
      .eDone (rset rd (pc + sext 64 (imm.append (0 : BitVec 12))) cn)
  | .jal rd imm =>
      .eDone (rset rd npc (with_pc (pc + sext 64 imm) c))
  | .jalr rd rs1 imm =>
      let a := rget c rs1
      .eDone (rset rd npc (with_pc ((a + sext 64 imm) &&& ~~~w1) c))
  | .branch bc rs1 rs2 imm =>
      .eDone (with_pc (if branch_taken bc (rget c rs1) (rget c rs2)
                       then pc + sext 64 imm else npc) c)
  | .load msz sgn rd rs1 imm =>
      load_val msz sgn (rget c rs1 + sext 64 imm)
        (fun v => .eDone (rset rd v cn))
  | .store msz rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm
      store_val msz a (rget c rs2) (.eDone (inval_resv a cn))
  | .opImm op rd rs1 imm =>
      .eDone (rset rd (alu64 op (rget c rs1) (sext 64 imm)) cn)
  | .shiftImm op rd rs1 shamt =>
      .eDone (rset rd (alu64 op (rget c rs1) (zext 64 shamt)) cn)
  | .op op rd rs1 rs2 =>
      .eDone (rset rd (alu64 op (rget c rs1) (rget c rs2)) cn)
  | .opImm32 rd rs1 imm =>
      .eDone (rset rd (sext 64 (alu32 .ADD (low32 (rget c rs1)) (sext 32 imm))) cn)
  | .shiftImm32 op rd rs1 shamt =>
      .eDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (zext 32 shamt))) cn)
  | .op32 op rd rs1 rs2 =>
      .eDone (rset rd (sext 64 (alu32 op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  | .fence _ _ _ _ _ | .fenceI _ _ _ =>
      .eDone cn   -- single hart: fences are no-ops
  | .ecall => .eEcall cn
  | .ebreak => .eEbreak cn
  -- M
  | .mul op rd rs1 rs2 =>
      .eDone (rset rd (mul_div op (rget c rs1) (rget c rs2)) cn)
  -- Operands truncated to 32 bits BEFORE the divide.
  | .mul32 op rd rs1 rs2 =>
      .eDone (rset rd (sext 64 (mul_div op (low32 (rget c rs1)) (low32 (rget c rs2)))) cn)
  -- A: sequential single-hart model, composed from plain memory ops.
  | .lr wd _ _ rd rs1 =>
      let a := rget c rs1
      if !(amo_aligned wd a) then .eFault c
      else match wd with
      | .W => .eLoad 32 a (fun v =>
                .eDone (with_resv (some a) (rset rd (sext 64 v) cn)))
      | .D => .eLoad 64 a (fun v =>
                .eDone (with_resv (some a) (rset rd v cn)))
  | .sc wd _ _ rd rs1 rs2 =>
      let a := rget c rs1
      if !(amo_aligned wd a) then .eFault c
      else
        let ok := match c.c_resv with
                  | some r => r.toNat == a.toNat
                  | none => false
        let c1 := with_resv none cn
        if ok then
          (match wd with
           | .W => eff.eStore 32 a (low32 (rget c rs2))
           | .D => eff.eStore 64 a (rget c rs2)) (.eDone (rset rd w0 c1))
        else .eDone (rset rd w1 c1)
  | .amo op wd _ _ rd rs1 rs2 =>
      let a := rget c rs1
      if !(amo_aligned wd a) then .eFault c
      else
        let src := rget c rs2
        let c1 := inval_resv a cn
        match wd with
        | .W => .eLoad 32 a (fun old =>
                  .eStore 32 a (amo_val op old (low32 src))
                    (.eDone (rset rd (sext 64 old) c1)))
        | .D => .eLoad 64 a (fun old =>
                  .eStore 64 a (amo_val op old src)
                    (.eDone (rset rd old c1)))
  -- Zicsr.  The architectural read-only check runs on the PRE-state core.
  | .csr op rd rs1 csr =>
      let writes := match op with | .RW => true | _ => !(is_x0 rs1)
      if csr_write_illegal writes csr then .eDefinedIllegal c
      else exec_csr op rd (rget c rs1) writes csr cn
  | .csrI op rd uimm csr =>
      let writes :=
        match op with
        | .RW => true
        | _ => !(uimm.toNat == 0)
      if csr_write_illegal writes csr then .eDefinedIllegal c
      else exec_csr op rd (zext 64 uimm) writes csr cn
  -- F/D data movement executes concretely.
  | .fLoad fmt rd rs1 imm =>
      let a := rget c rs1 + sext 64 imm
      match fmt with
      | .S => .eLoad 32 a (fun v => .eDone (fset rd (nan_box v) cn))
      | .D => .eLoad 64 a (fun v => .eDone (fset rd v cn))
  | .fStore fmt rs1 rs2 imm =>
      let a := rget c rs1 + sext 64 imm
      let v := fget c rs2
      (match fmt with
       | .S => eff.eStore 32 a (low32 v)
       | .D => eff.eStore 64 a v) (.eDone (inval_resv a cn))
  | .fmv dir fmt rd rs1 =>
      .eDone (match dir, fmt with
              | .X_F, .S => rset rd (sext 64 (low32 (fget c rs1))) cn
              | .X_F, .D => rset rd (fget c rs1) cn
              | .F_X, .S => fset rd (nan_box (low32 (rget c rs1))) cn
              | .F_X, .D => fset rd (rget c rs1) cn)
  | .fsgnj op fmt rd rs1 rs2 =>
      let a := fget c rs1
      let b := fget c rs2
      .eDone (match fmt with
              | .S => fset rd (nan_box (sgnj_val op (unbox_s a) (unbox_s b))) cn
              | .D => fset rd (sgnj_val op a b) cn)
  -- F/D arithmetic: resolve rm (reserved -> EIllegal with pc advanced),
  -- read at the format's width, call Fpu, write back, accrue flags.
  | .fari op fmt rd rs1 rs2 rm =>
      match resolve_rm rm cn with
      | none => .eIllegal cn
      | some md =>
        let f := fp_format fmt
        let a := fread c fmt rs1
        let b := fread c fmt rs2
        let (v, fl) :=
          match op with
          | .ADD => fp_add f md a b
          | .SUB => fp_sub f md a b
          | .MUL => fp_mul f md a b
          | .DIV => fp_div f md a b
        .eDone (fwrite fmt rd v (accrue fl cn))
  | .fsqrt fmt rd rs1 rm =>
      match resolve_rm rm cn with
      | none => .eIllegal cn
      | some md =>
        let (v, fl) := fp_sqrt (fp_format fmt) md (fread c fmt rs1)
        .eDone (fwrite fmt rd v (accrue fl cn))
  -- The four fused forms differ only by which operand is sign-flipped.
  | .fma op fmt rd rs1 rs2 rs3 rm =>
      match resolve_rm rm cn with
      | none => .eIllegal cn
      | some md =>
        let f := fp_format fmt
        let a := fread c fmt rs1
        let b := fread c fmt rs2
        let z := fread c fmt rs3
        let (a', z') :=
          match op with
          | .MADD => (a, z)
          | .MSUB => (a, fp_neg f z)
          | .NMSUB => (fp_neg f a, z)
          | .NMADD => (fp_neg f a, fp_neg f z)
        let (v, fl) := fp_fma f md a' b z'
        .eDone (fwrite fmt rd v (accrue fl cn))
  | .fminmax op fmt rd rs1 rs2 =>
      let (v, fl) :=
        fp_minmax (fp_format fmt) (match op with | .MIN => false | .MAX => true)
                  (fread c fmt rs1) (fread c fmt rs2)
      .eDone (fwrite fmt rd v (accrue fl cn))
  -- The compares and fclass write an INTEGER register.
  | .fcmp op fmt rd rs1 rs2 =>
      let f := fp_format fmt
      let a := fread c fmt rs1
      let b := fread c fmt rs2
      let (v, fl) :=
        match op with
        | .EQ => fp_eq f a b
        | .LT => fp_lt f a b
        | .LE => fp_le f a b
      .eDone (rset rd (if v then w1 else w0) (accrue fl cn))
  | .fclass fmt rd rs1 =>
      .eDone (rset rd (BitVec.ofInt 64 (fp_class (fp_format fmt) (fread c fmt rs1))) cn)
  -- fcvt.  The (dst, src) pair says which direction this is; the decoder
  -- only produces the architecturally valid pairs, so the leftovers are
  -- dead and answer EIllegal rather than inventing a meaning.
  | .fcvt dst src rd rs1 rm =>
      match resolve_rm rm cn with
      | none => .eIllegal cn
      | some md =>
        let ity : (FcvtTy) → Option (Bool × Int) := fun t =>
          match t with
          | .W => some (true, 32) | .WU => some (false, 32)
          | .L => some (true, 64) | .LU => some (false, 64)
          | _ => none
        let fty : FcvtTy → Option FFmt := fun t =>
          match t with | .S => some .S | .D => some .D | _ => none
        match fty dst, fty src with
        | some df, some sf =>
            let (v, fl) := fp_convert (fp_format sf) (fp_format df) md (fread c sf rs1)
            .eDone (fwrite df rd v (accrue fl cn))
        | none, some sf =>
            match ity dst with
            | none => .eIllegal cn
            | some (sgn, bits) =>
              let (v, fl) := fp_to_int (fp_format sf) md sgn bits (fread c sf rs1)
              .eDone (rset rd (if bits == 32 then sext 64 (BitVec.ofInt 32 v)
                              else BitVec.ofInt 64 v)
                          (accrue fl cn))
        | some df, none =>
            match ity src with
            | none => .eIllegal cn
            | some (sgn, bits) =>
              let (v, fl) :=
                fp_of_int (fp_format df) md sgn bits (rget c rs1).toNat
              .eDone (fwrite df rd v (accrue fl cn))
        | none, none => .eIllegal cn

/-- Fetch, decode, dispatch.  `decode_any` is supplied by the driver and
    returns the decoded instruction with its size in bytes (2 or 4).  On
    an undecodable word we issue `EIllegal` with pc NOT advanced. -/
def step (decode_any : BitVec 32 → Option (Instr × Int)) (c : core) : eff :=
  .eLoad 32 c.c_pc (fun w32 =>
    match decode_any w32 with
    | some (i, isz) => exec (BitVec.ofInt 64 isz) i c
    | none => .eIllegal c)

end LinuxSem.Riscv
