/-
  * LinuxProcessSem.StateNet — the network environment: what a hostile peer
    may do

  CHUNK B4.  This file holds the network-environment operations and their
  lemmas: `net_take`, `net_bytes`, `net_rest` and the `net_take_*` lemma
  group, `net_ended`, `net_take_z`, the queue projections `nq_peer`,
  `nq_script`, `nq_rest`, and the quiet environment `net_silent`.

  WHAT IS **NOT** HERE, and why.  The data types this file operates on —
  `NetStep`, `NetStream`, `NFin`/`NRst`/`NTimedOut`/`NCons`, `PeerAddr`,
  `NetQueue`, `NConn`, and `SockState` — were already ported in chunk A1
  and live in `LinuxProcessSem.State`.  They are imported, not redefined.
  `SockState` is likewise already in `State.lean`;
  its constructor doc comment, which sits in this line range, is carried
  there.  `PIPE_BUF` (2434) is past the end of the range and also already
  in `State.lean`.

  DEFERRED. `net_take_pos` and its correctness lemma `net_take_pos_eq` (2266–2292)
  are deferred, together with their `stream_take_pos` twins in chunk B3. They exist
  ONLY to avoid unary `nat` in extracted OCaml: they read a `positive` by repeated
  squaring so that the cost of a take is logarithmic in the index. Lean compiles
  `Nat` to a machine word, so the trick buys nothing and the two proofs are the
  hardest in the file. `net_take_z` is instead defined directly as `net_take s
  n.toNat` for `n ≥ 0` and `([], s)` below — see `net_take_z` and `net_take_z_eq`
  below. the observable behaviour of `net_take_z` is exactly (`net_take_pos_eq` /
  `net_take_z_eq` are the equations that justify it).

  `NetStream` is `Nat → NetStep` and `NetQueue` is `Nat → (PeerAddr × NetStream)`
  here, so there is no corecursion: `net_take` matches on `s 0` and recurses on `fun
  n => s (n + 1)`, and `net_silent` is `fun _ => (⟨0, 0⟩, NFin)`. A terminal
  `NetStep` makes `net_take` return the stream it was given, unchanged, so the
  returned remainder is always the original stream shifted by the number of steps
  actually taken — which is what lets the lemma proofs below re-instantiate an
  induction hypothesis at the shifted stream.

  TRUST BOUNDARY: this file is part of the trusted specification.
-/
import LinuxSem.LinuxProcessSem.State

open LinuxSem.Riscv

namespace LinuxSem.LinuxProcessSem

/- =========================================================================
   Taking bytes off a connection's script
   ========================================================================= -/

/-- Take up to `k` bytes off the front of a connection's script: the
    bytes actually available (fewer than `k` when a terminal comes
    first) together with the REMAINING script.  The exact analogue of
    `stream_take`, with the three terminals where `IEof` is.

    Indexed by a `nat` rather than a `word` for the same reason: the
    index is always the length of a delivered byte list, never guest
    arithmetic, so no wrapping is possible.

  here the stream is a function, so the match is on its first observation `s 0` and
  the recursive call moves to the stream one step on, `fun n => s (n + 1)`. Nothing
  follows a terminal that a reader could see. -/
def net_take (s : NetStream) : Nat → List byte × NetStream
  | 0 => ([], s)
  | k + 1 =>
      match s 0 with
      | NetStep.cons b =>
          let r := net_take (fun n => s (n + 1)) k
          (b :: r.1, r.2)
      | _ => ([], s)

/-- The bytes a read of at most `k` delivers. -/
def net_bytes (s : NetStream) (k : Nat) : List byte :=
  (net_take s k).1

/-- What is left after such a read. -/
def net_rest (s : NetStream) (k : Nat) : NetStream :=
  (net_take s k).2

theorem net_take_zero (s : NetStream) : net_take s 0 = ([], s) := rfl

theorem net_take_fin (k : Nat) : net_take NFin k = ([], NFin) := by
  cases k with
  | zero => rfl
  | succ _ => rfl

theorem net_take_rst (k : Nat) : net_take NRst k = ([], NRst) := by
  cases k with
  | zero => rfl
  | succ _ => rfl

theorem net_take_timedout (k : Nat) : net_take NTimedOut k = ([], NTimedOut) := by
  cases k with
  | zero => rfl
  | succ _ => rfl

theorem net_take_cons (b : byte) (s : NetStream) (k : Nat) :
    net_take (NCons b s) (k + 1) = (b :: (net_take s k).1, (net_take s k).2) := by
  rfl

/-- PORT AUXILIARY.  Unfolding `net_take` at a
    successor when the head is known to be a byte: the general form of
    `net_take_cons`, for a stream that is not syntactically `NCons` but
    agrees with it at observation 0.  Needed because the encoding's
    recursion moves to `fun n => s (n + 1)` rather than to a
    constructor's field, so `net_take_cons` does not match a stream known
    only by its head. -/
theorem net_take_succ_of_cons (b : byte) (s : NetStream)
    (h : s 0 = NetStep.cons b) (k : Nat) :
    net_take s (k + 1) = (b :: (net_take (fun n => s (n + 1)) k).1,
                          (net_take (fun n => s (n + 1)) k).2) := by
  simp [net_take, h]

/-- A read never delivers more than it was asked for. -/
theorem net_take_length : ∀ (k : Nat) (s : NetStream), (net_take s k).1.length ≤ k
  | 0, _ => Nat.zero_le _
  | k + 1, s => by
      simp only [net_take]
      split
      · rename_i b
        simp only [List.length_cons]
        have ih := net_take_length k (fun n => s (n + 1))
        omega
      · exact Nat.zero_le _

/-- Taking exactly as many bytes as were delivered is idempotent: the
    delivered list is the script's prefix of its own length.  No consumer
    yet -- it is here for the same reason its stdin twin
    `stream_take_bytes_self` is, which is that reading the choice
    condition of a read spec BOTH WAYS needs it, and the first proof
    about a socket-reading program will.  Stated rather than claimed to
    be in use. -/
theorem net_take_bytes_self : ∀ (k : Nat) (s : NetStream),
    (net_take s (net_take s k).1.length).1 = (net_take s k).1
  | 0, _ => rfl
  | k + 1, s => by
      simp only [net_take]
      split
      · rename_i b h
        simp only [List.length_cons]
        rw [net_take_succ_of_cons b s h]
        rw [net_take_bytes_self k (fun n => s (n + 1))]
      · rfl

/-- Re-taking exactly what was delivered leaves the same remainder — the
    lemma the read spec needs to know that consuming `length bs` bytes
    and consuming "the bytes it chose" are the same step. -/
theorem net_take_rest_self : ∀ (k : Nat) (s : NetStream),
    (net_take s (net_take s k).1.length).2 = (net_take s k).2
  | 0, _ => rfl
  | k + 1, s => by
      simp only [net_take]
      split
      · rename_i b h
        simp only [List.length_cons]
        rw [net_take_succ_of_cons b s h]
        rw [net_take_rest_self k (fun n => s (n + 1))]
      · rfl

/-- A nonempty delivery is only possible from a script whose head is a
    byte: each terminal delivers nothing, at every length. -/
theorem net_take_nil_of_fin (k : Nat) : (net_take NFin k).1 = [] := by
  rw [net_take_fin]

theorem net_take_nil_of_rst (k : Nat) : (net_take NRst k).1 = [] := by
  rw [net_take_rst]

theorem net_take_nil_of_timedout (k : Nat) : (net_take NTimedOut k).1 = [] := by
  rw [net_take_timedout]

/-- Whether the script has ended: true on every terminal step, false when
    the head is a byte. -/
def net_ended (s : NetStream) : Bool :=
  match s 0 with
  | NetStep.cons _ => false
  | _ => true

theorem net_take_ended (s : NetStream) (k : Nat) (h : net_ended s = true) :
    net_take s k = ([], s) := by
  cases hk : s 0 with
  | cons b => simp [net_ended, hk] at h
  | fin =>
      cases k with
      | zero => rfl
      | succ k => simp [net_take, hk]
  | rst =>
      cases k with
      | zero => rfl
      | succ k => simp [net_take, hk]
  | timedOut =>
      cases k with
      | zero => rfl
      | succ k => simp [net_take, hk]

/-- The `NetStream` halves of `stream_take_add` and `stream_take_z`; see
    those for why the `Z`-indexed take exists and how it stays cheap. -/
theorem net_take_add (a b : Nat) (s : NetStream) :
    net_take s (a + b)
      = ((net_take s a).1 ++ (net_take (net_take s a).2 b).1,
         (net_take (net_take s a).2 b).2) := by
  induction a generalizing b s with
  | zero =>
      rw [Nat.zero_add, net_take_zero]
      rfl
  | succ a ih =>
      rw [Nat.succ_add]
      cases h : s 0 with
      | cons c =>
          rw [net_take_succ_of_cons c s h]
          rw [net_take_succ_of_cons c s h]
          rw [ih b (fun n => s (n + 1))]
          simp [List.cons_append]
      | fin =>
          have hb : net_take s b = ([], s) := net_take_ended s b (by simp [net_ended, h])
          simp [net_take, h, hb]
      | rst =>
          have hb : net_take s b = ([], s) := net_take_ended s b (by simp [net_ended, h])
          simp [net_take, h, hb]
      | timedOut =>
          have hb : net_take s b = ([], s) := net_take_ended s b (by simp [net_ended, h])
          simp [net_take, h, hb]

/-! ## The `Z`-indexed take

    The binary-indexed take `net_take_pos` and its bridge `net_take_pos_eq`
    are not present; see the file header for why the `Int`-indexed form
    below is enough.
    -/

/-- `net_take` at an `Int` index: a negative index takes nothing (a `Z`
    match returns `([], s)` on `Z0` and `Zneg`), and a
    non-negative one takes `n.toNat` bytes. -/
def net_take_z (s : NetStream) (n : Int) : List byte × NetStream :=
  if n < 0 then ([], s) else net_take s n.toNat

theorem net_take_z_eq (s : NetStream) (n : Int) :
    net_take_z s n = net_take s n.toNat := by
  unfold net_take_z
  split
  · rename_i hn
    rw [Int.toNat_of_nonpos (by omega)]
    rfl
  · rfl

/- =========================================================================
   The connection queue
   ========================================================================= -/

/-- **THE QUIET ENVIRONMENT**: connection after connection, each from
    0.0.0.0:0 with nothing to say — the peer opens the connection and
    closes its sending half at once, so every read on an accepted socket
    delivers 0.

    It is one point of the input space and carries no special status;
    it is here because fixtures and callers of the extracted checker both need
    SOME queue to name, and a queue that says nothing is the only one
    whose bytes neither of them has to predict.  Proofs about programs
    quantify over `in_net`, as `Equivalence.strong_equiv` does — they do
    not use this.

  `net_silent`
    becomes the constant function: every observation of the queue is the
    same connection. -/
def net_silent : NetQueue := fun _ => (⟨0, 0⟩, NFin)

/-- The head connection's peer, script, and the queue behind it. -/
def nq_peer (q : NetQueue) : PeerAddr :=
  (q 0).1

def nq_script (q : NetQueue) : NetStream :=
  (q 0).2

def nq_rest (q : NetQueue) : NetQueue :=
  fun n => q (n + 1)

/-! ## Sanity checks on the queue projections -/

example (p : PeerAddr) (s : NetStream) (q : NetQueue) : nq_peer (NConn p s q) = p := rfl
example (p : PeerAddr) (s : NetStream) (q : NetQueue) : nq_script (NConn p s q) = s := rfl
example (p : PeerAddr) (s : NetStream) (q : NetQueue) : nq_rest (NConn p s q) = q := rfl

-- observation 0 of a connection is its peer and script
example (p : PeerAddr) (s : NetStream) (q : NetQueue) : NConn p s q 0 = (p, s) := rfl

-- the rest of the queue is what `accept` would offer next
example (p : PeerAddr) (s : NetStream) (q : NetQueue) :
    (nq_rest (NConn p s q)) 0 = q 0 := rfl

-- the peer of a concrete connection, decided
example : nq_peer (NConn ⟨0x7f000001, 0x1f90⟩ (NCons 5 NFin) net_silent) = ⟨0x7f000001, 0x1f90⟩ := by
  decide
example : (net_take (nq_script (NConn ⟨0x7f000001, 0x1f90⟩ (NCons 5 NFin) net_silent)) 1).1
    = [5] := by decide

-- `net_silent` says nothing: 0.0.0.0:0 and a FIN, at every observation
example : net_silent 0 = ((⟨0, 0⟩ : PeerAddr), NFin) := rfl
example : (net_silent 0).1 = (⟨0, 0⟩ : PeerAddr) := by decide
example : (net_silent 0).2 0 = NetStep.fin := by decide
example : (net_silent 0).1 = (⟨0, 0⟩ : PeerAddr) ∧
    (net_silent 0).2 0 = NetStep.fin := by decide
example : (net_silent 7).2 3 = NetStep.fin := by decide
example : (net_silent 7).1 = (⟨0, 0⟩ : PeerAddr) := by decide

-- a read on the quiet environment delivers nothing, at any length
example : (net_take (nq_script net_silent) 3).1 = [] := by decide

/-! ## Sanity checks on `net_take`

    `NetStream` is a function type, so equality of two `NetStream`s is not
    decidable and the pair `net_take s k` as a whole has no `DecidableEq`.
    The checks therefore split: the BYTE LIST is decided (`by decide`), and
    the REMAINDER is pinned either definitionally (`rfl`) or by its
    observation at an index (`by decide`). -/

-- a terminal delivers nothing, at any length, and stays put
example : net_take NFin 3 = ([], NFin) := rfl
example : (net_take NFin 3).1 = [] := by decide
-- the whole pair, decided componentwise (a `NetStream` has no
-- `DecidableEq`, so the conjunction pins the remainder at observation 0)
example : (net_take NFin 3).1 = [] ∧ (net_take NFin 3).2 0 = NetStep.fin := by decide

-- one byte off a one-byte script: delivered, with the terminal behind it
example : net_take (NCons 5 NFin) 1 = ([5], NFin) := rfl
example : (net_take (NCons 5 NFin) 1).1 = [5] := by decide
example : (net_take (NCons 5 NFin) 1).1 = [5] ∧
    (net_take (NCons 5 NFin) 1).2 0 = NetStep.fin := by decide

-- asking for more than is there delivers exactly the prefix
example : net_take (NCons 5 NFin) 4 = ([5], NFin) := rfl

-- and a zero-length read takes nothing at all
example : net_take (NCons 5 NFin) 0 = ([], NCons 5 NFin) := rfl
example : (net_take (NCons 5 NFin) 0).1 = [] := by decide

-- two bytes: the delivery is the prefix, in order
example : (net_take (NCons 5 (NCons 6 NFin)) 2).1 = [5, 6] := by decide
example : (net_take (NCons 5 (NCons 6 NFin)) 1).2 0 = NetStep.cons 6 := by decide

-- the projections: `net_bytes` is the first component, `net_rest` the second
example : net_bytes (NCons 5 NFin) 1 = [5] := by decide
example : net_rest (NCons 5 NFin) 1 0 = NetStep.fin := by decide
example : net_rest (NCons 5 (NCons 6 NFin)) 1 0 = NetStep.cons 6 := by decide

-- `net_ended`: true on the terminals, false on a byte
example : net_ended NFin = true := by decide
example : net_ended NRst = true := by decide
example : net_ended NTimedOut = true := by decide
example : net_ended (NCons 5 NFin) = false := by decide

-- `net_take_z`: a positive index takes, zero and negative take nothing
example : net_take_z (NCons 5 NFin) 1 = ([5], NFin) := rfl
example : net_take_z (NCons 5 NFin) 0 = ([], NCons 5 NFin) := rfl
example : net_take_z (NCons 5 NFin) (-1) = ([], NCons 5 NFin) := rfl
example : (net_take_z (NCons 5 (NCons 6 NFin)) 2).1 = [5, 6] := by decide

end LinuxSem.LinuxProcessSem
