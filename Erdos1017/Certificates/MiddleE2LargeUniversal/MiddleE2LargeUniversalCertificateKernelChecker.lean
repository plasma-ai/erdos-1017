module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateChecker

/-!
# Kernel form of the large-atom leaf test

The leaf test `leafOK` of `MiddleE2LargeUniversalCertificateChecker`, written
for evaluation by the kernel. The integer operations `zadd`, `zsub`, `zmul`,
`zdiv`, `zle` and `zlt` match on `Int.ofNat` and `Int.negSucc` and apply
`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.ble` and `Nat.blt` directly, so
the kernel does not unfold the instances behind `+`, `-`, `*`, `/`, `≤` and `<`;
`Int.neg`, `Int.negOfNat` and `Int.toNat` are such matches already. Every other
definition copies the definition of the same name in `FixedPoint` on these
operations. Each definition is proved equal to the one it replaces, for all
arguments, ending with `leafOK_eq`.
-/

@[expose] public section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint.Kernel

/-! Integer operations by constructor cases. -/

/-- `Int.subNatNat` on `Nat.sub`. -/
def zsubNatNat (m n : ℕ) : ℤ :=
  match Nat.sub n m with
  | 0 => .ofNat (Nat.sub m n)
  | k + 1 => .negSucc k

/-- `Int.add` on `Nat.add`. -/
def zadd : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => .ofNat (Nat.add m n)
  | .ofNat m, .negSucc n => zsubNatNat m (Nat.succ n)
  | .negSucc m, .ofNat n => zsubNatNat n (Nat.succ m)
  | .negSucc m, .negSucc n => .negSucc (Nat.succ (Nat.add m n))

/-- `a - b` by cases, without the negation and addition of `Int.sub`. -/
def zsub : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => zsubNatNat m n
  | .ofNat m, .negSucc n => .ofNat (Nat.add m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.negOfNat (Nat.add (Nat.succ m) n)
  | .negSucc m, .negSucc n => zsubNatNat n m

/-- `Int.mul` on `Nat.mul`. -/
def zmul : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => .ofNat (Nat.mul m n)
  | .ofNat m, .negSucc n => Int.negOfNat (Nat.mul m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.negOfNat (Nat.mul (Nat.succ m) n)
  | .negSucc m, .negSucc n => .ofNat (Nat.mul (Nat.succ m) (Nat.succ n))

/-- `Int.ediv`, the `/` of `ℤ`, on `Nat.div`. -/
def zdiv : ℤ → ℤ → ℤ
  | .ofNat m, .ofNat n => .ofNat (Nat.div m n)
  | .ofNat m, .negSucc n => Int.negOfNat (Nat.div m (Nat.succ n))
  | .negSucc _, .ofNat 0 => .ofNat 0
  | .negSucc m, .ofNat (n + 1) => .negSucc (Nat.div m (Nat.succ n))
  | .negSucc m, .negSucc n => .ofNat (Nat.succ (Nat.div m (Nat.succ n)))

/-- `decide (a ≤ b)` on `Nat.ble`. -/
def zle : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m

/-- `decide (a < b)` on `Nat.blt`. -/
def zlt : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => Nat.blt m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.blt n m

/-- `min a b`. -/
def zmin (a b : ℤ) : ℤ := cond (zle a b) a b

/-- `max a b`. -/
def zmax (a b : ℤ) : ℤ := cond (zle a b) b a

/-! Operations. -/

def fl (n d : ℤ) : ℤ := zdiv n d

def ce (n d : ℤ) : ℤ := Int.neg (zdiv (Int.neg n) d)

def fint (k : ℤ) : FI := ⟨zmul k S, zmul k S⟩

def frat (p d : ℤ) : FI := ⟨fl (zmul p S) d, ce (zmul p S) d⟩

def fadd (a b : FI) : FI := ⟨zadd a.lo b.lo, zadd a.hi b.hi⟩

def fsub (a b : FI) : FI := ⟨zsub a.lo b.hi, zsub a.hi b.lo⟩

def fnsmul (n : ℕ) (a : FI) : FI := ⟨zmul (.ofNat n) a.lo, zmul (.ofNat n) a.hi⟩

def fdivn (a : FI) (n : ℕ) : FI := ⟨fl a.lo (.ofNat n), ce a.hi (.ofNat n)⟩

def fmin (a b : FI) : FI := ⟨zmin a.lo b.lo, zmin a.hi b.hi⟩

def fmax (a b : FI) : FI := ⟨zmax a.lo b.lo, zmax a.hi b.hi⟩

def fmul (a b : FI) : FI :=
  ⟨fl (zmin (zmin (zmul a.lo b.lo) (zmul a.lo b.hi)) (zmin (zmul a.hi b.lo) (zmul a.hi b.hi))) S,
    ce (zmax (zmax (zmul a.lo b.lo) (zmul a.lo b.hi)) (zmax (zmul a.hi b.lo) (zmul a.hi b.hi))) S⟩

def fsq (a : FI) : FI :=
  cond (zle 0 a.lo) ⟨fl (zmul a.lo a.lo) S, ce (zmul a.hi a.hi) S⟩
    (cond (zle a.hi 0) ⟨fl (zmul a.hi a.hi) S, ce (zmul a.lo a.lo) S⟩
      ⟨0, ce (zmax (zmul a.lo a.lo) (zmul a.hi a.hi)) S⟩)

def frecip (a : FI) : FI := ⟨fl (zmul S S) a.hi, ce (zmul S S) a.lo⟩

def fdiv (a b : FI) : FI := fmul a (frecip b)

def fsqrt (a : FI) : FI :=
  let l : ℤ := .ofNat (isqrt (zmul a.lo S).toNat)
  let h : ℤ := zadd (.ofNat (isqrt (zmul a.hi S).toNat)) 1
  ⟨cond (zle 0 l && zle (zmul l l) (zmul a.lo S)) l 0,
    cond (zle 0 h && zle (zmul a.hi S) (zmul h h)) h (zmax S a.hi)⟩

/-! Initial box at scale `S = 1000·2^30`. -/

def seg (off W : ℤ) (i k : ℕ) : FI :=
  ⟨zadd off (zdiv (zmul W (.ofNat i)) (.ofNat (Nat.pow 2 k))),
    zadd off (zdiv (zmul W (zadd (.ofNat i) 1)) (.ofNat (Nat.pow 2 k)))⟩

namespace IBox

def qI (B : IBox) : FI := seg qOff qW B.iq B.kq
def AI (B : IBox) : FI := seg aOff aW B.iA B.kA
def bI (B : IBox) : FI := seg 0 bW B.ib B.kb
def uI (B : IBox) : FI := seg 0 bW B.iu B.ku

end IBox

/-! Parameter enclosures at one exact scaled point `Q`. -/

def rAt (Q : ℤ) : FI := fadd (fadd (fint 1) (fnsmul 7 (fpt Q))) (fmul (fpt Q) (fpt Q))
def ellAt (Q : ℤ) : FI := fdiv (fsub (fint 2) (fpt Q)) (fadd (fint 2) (fpt Q))
def gAt (Q : ℤ) : FI := fdiv (fmul (fpt Q) (fadd (fint 1) (fnsmul 2 (fpt Q)))) (fnsmul 2 (rAt Q))
def yAt (Q : ℤ) : FI := fdiv (fnsmul 9 (fpt Q)) (fnsmul 2 (rAt Q))
def f1At (Q : ℤ) : FI := fdiv (fadd (fpt Q) (fint 2)) (rAt Q)
def f2At (Q : ℤ) : FI := fdiv (fpt Q) (rAt Q)
def pAt (Q : ℤ) : FI := fadd (fadd (fint 1) (fnsmul 4 (fpt Q))) (fnsmul 13 (fmul (fpt Q) (fpt Q)))
def rpAt (Q A : ℤ) : FI :=
  fadd (fsub (fmul (ellAt Q) (fsub (fint 1) (fpt A))) (fpt A)) (gAt Q)
def surAt (Q A : ℤ) : FI :=
  fsub (fdivn (fsub (fadd (fint (-1)) (fnsmul 6 (fpt A)))
    (fmul (fsub (fint 8) (fnsmul 3 (fsub (fint 1) (ellAt Q)))) (fsq (fpt A)))) 3) (gAt Q)

/-- Positivity of every parameter division at the point `Q`. -/
def atOK (Q : ℤ) : Bool :=
  zlt 0 (fadd (fint 2) (fpt Q)).lo && zlt 0 (fnsmul 2 (rAt Q)).lo && zlt 0 (rAt Q).lo

/-! Box parameter enclosures, from monotonicity in `q`. -/

def ellB (q : FI) : FI := ⟨(ellAt q.hi).lo, (ellAt q.lo).hi⟩
def deB (q : FI) : FI := fsub (fint 1) (ellB q)
def gB (q : FI) : FI := ⟨(gAt q.lo).lo, (gAt q.hi).hi⟩
def yB (q : FI) : FI := ⟨(yAt q.lo).lo, (yAt q.hi).hi⟩
def f1B (q : FI) : FI := ⟨(f1At q.hi).lo, (f1At q.lo).hi⟩
def pB (q : FI) : FI := ⟨(pAt q.lo).lo, (pAt q.hi).hi⟩
def f2B (q : FI) : FI := ⟨(f2At q.lo).lo, (f2At q.hi).hi⟩
def hB (q : FI) : FI := fdivn (fmul (fmul (f1B q) (f1B q)) (pB q)) 8
def KB (q : FI) : FI :=
  fmul (frat 9 4) (fmul (fmul (f2B q) (f2B q)) (fsub (fint 1) (fmul q q)))
def RPB (q A : FI) : FI := ⟨(rpAt q.hi A.hi).lo, (rpAt q.lo A.lo).hi⟩
def surB (q A : FI) : FI := ⟨(surAt q.hi A.lo).lo, (surAt q.lo A.hi).hi⟩

/-! Local contraction. -/

def narrowHi (a c : FI) : FI := ⟨a.lo, zmin a.hi c.hi⟩
def narrowLo (a c : FI) : FI := ⟨zmax a.lo c.lo, a.hi⟩

def cA (q A b : FI) : FI :=
  narrowHi (narrowHi (narrowHi A (yB q)) (fdivn (fadd (fint 1) b) 3))
    (fdivn (fsub (fint 1) b) 2)
def cb (q A b : FI) : FI :=
  narrowHi (narrowHi (narrowLo b (fsub (fnsmul 3 A) (fint 1))) (fsub (fint 1) (fnsmul 2 A)))
    (fsub A (KB q))
def cu (q A u : FI) : FI :=
  narrowHi (narrowHi (narrowLo u (fdiv (RPB q A) (fnsmul 2 (ellB q))))
    (fsub (fint 1) (fnsmul 2 A)))
    (fsub (fsub (fint 1) (fnsmul 2 (fmul (ellB q) A))) (fnsmul 3 (gB q)))

def empty (a : FI) : Bool := zlt a.hi a.lo

/-! The strict tests on contracted intervals `q, A, b, u`. -/

def etaF (A b u : FI) : FI := fsub (fsub (fsub (fint 1) A) b) u
def r0F (A : FI) : FI := fsub (fint 1) (fnsmul 2 A)
def RCF (q A b u : FI) : FI :=
  fmin (fadd (fsub (fint 1) (fnsmul 3 A)) b)
    (fdiv (fsub (fsub (fsub (fint 1) u) (fnsmul 2 (fmul (ellB q) A))) (fnsmul 3 (gB q)))
      (ellB q))
def sdenF (q : FI) : FI := fsub (frat 1 5) (deB q)
def scF (q A : FI) : FI := fdiv (surB q A) (sdenF q)
def TF (q A : FI) : FI := fsqrt (scF q A)
def CF (q A b : FI) : FI :=
  fmin (fmin (fsub (r0F A) b) (fsub (fsub A b) (KB q))) (fsub (TF q A) b)
def QF (q A b u : FI) : FI :=
  fmin (fmin (fmul (CF q A b) (etaF A b u)) (fsq (etaF A b u)))
    (fsub (fsub (fsub (hB q) (fsq A)) (fsq b)) (fnsmul 2 (fmul b (etaF A b u))))
def pF (q u : FI) : FI := fsub (yB q) u
def lp0F (q A b u : FI) : FI :=
  fsub (pF q u) (fmin (fdivn (etaF A b u) 2) (fsub (etaF A b u) (CF q A b)))
def vF (q u : FI) : FI := fsub (fsub (fint 1) (fnsmul 2 (hB q))) u
def gapF (q A u : FI) : FI :=
  fmax (fmax (fsub A u) (fadd (fsub (fsub (fint 1) (fnsmul 2 A)) u) (KB q)))
    (fsub (fsub (fsub (fint 1) A) u) (TF q A))
def t0F (q A u : FI) : FI := fdiv (fmax (fint 0) (gapF q A u)) (fnsmul 3 (vF q u))
def lpfF (q A b u : FI) : FI :=
  fmin (fdivn (etaF A b u) 2)
    (fadd (gapF q A u) (fmul (fsub (etaF A b u) (fnsmul 2 (gapF q A u)))
      (fmin (frat 1 2) (t0F q A u))))
def denF (q A b u : FI) : FI := fsub (fnsmul 2 (gapF q A u)) (etaF A b u)
def dgapF (q A : FI) : FI :=
  fmax (fmax (fsub A (yB q)) (fadd (fsub (fsub (fint 1) (fnsmul 2 A)) (yB q)) (KB q)))
    (fsub (fsub (fsub (fint 1) A) (TF q A)) (yB q))
/-- A lower endpoint for the atomic floor `t_*`. -/
def tfLo (q A b u : FI) : ℤ :=
  cond (zlt 0 (denF q A b u).lo)
    (fmax (t0F q A u) (fmax (fint 0) (fdiv (dgapF q A) (denF q A b u)))).lo
    (t0F q A u).lo
/-- A lower endpoint for the joint expression. -/
def jointLo (q A b u : FI) : ℤ :=
  zsub (fsub (fsq (fsub (fsub (fsub (fint 1) A) b) (yB q))) (fmul (fsub (yB q) A) (pF q u))).lo
    (ce (zmul (zmax 0 (zsub S (zmul 2 (tfLo q A b u)))) (QF q A b u).hi) S)
def poleF (q A b u : FI) : FI :=
  fmax (fmax (fsub (fsub (fadd (fnsmul 3 A) b) (fint 1)) (RCF q A b u))
      (fsub (fadd b (KB q)) (RCF q A b u)))
    (fmax (fsub (fsub (fadd A b) (TF q A)) (RCF q A b u)) (fsub (fnsmul 6 A) (fint 2)))
def edenF (q A : FI) : FI := fadd (fmul (fsub (fnsmul 2 (ellB q)) (fint 1)) A) (fnsmul 3 (gB q))
def thetaF (q A : FI) : FI := fsub (fdiv (fnsmul 3 (gB q)) A) (deB q)
def momentF (q A b u : FI) : FI :=
  fsub (fmul (thetaF q A) (fsub A (RCF q A b u))) (fmul (deB q) (pF q u))
def zeropriceF (q A b u : FI) : FI :=
  fsub (gB q) (fmul (fmax (fint 0) (fsub (fint 1) (fnsmul 2 (thetaF q A)))) (RCF q A b u))
def EF (q A _b u : FI) : FI :=
  fmul (fmul (fdiv (fmax (fint 0) (fsub A (fnsmul 3 (gB q)))) (edenF q A)) (fsub (r0F A) u))
    (fmax (fint 0) (fsub (fnsmul 2 (ellB q)) (fdiv (RPB q A) u)))
def GF (q A b u : FI) : FI :=
  fadd (fsub (fadd (fdiv (fmul (fmax (fint 0) (fsub (fmul b (ellB q)) (gB q))) (etaF A b u))
    (poleF q A b u)) (fmul (ellB q) (fadd (fsub (RCF q A b u) A) b))) (gB q)) (EF q A b u)

/-- Rejection by a violated necessary inequality. -/
def necFail (q A b u : FI) : Bool :=
  zlt (fsub (yB q) A).hi 0 || zlt (etaF A b u).hi 0 ||
    zlt (fsub (r0F A) b).hi 0 || zlt (fsub (r0F A) u).hi 0 ||
    zlt (fsub (fnsmul 2 (fmul (ellB q) u)) (RPB q A)).hi 0 ||
    zlt (RCF q A b u).hi 0 || zlt (scF q A).hi 0 ||
    zlt (CF q A b).hi 0 || zlt (QF q A b u).hi 0 ||
    zlt (lp0F q A b u).hi 0 || zle (vF q u).hi 0 ||
    (zlt 0 (vF q u).lo && zlt (fsub (pF q u) (lpfF q A b u)).hi 0) ||
    (zlt 0 (vF q u).lo && zlt 0 (jointLo q A b u))

/-- Acceptance by all five price tests and their denominators. -/
def priceOK (q A b u : FI) : Bool :=
  zlt 0 (poleF q A b u).lo && zlt 0 u.lo && zlt 0 (RPB q A).lo &&
    zlt 0 (edenF q A).lo && zlt 0 A.lo &&
    zlt 0 (momentF q A b u).lo && zlt 0 (zeropriceF q A b u).lo &&
    zlt 0 (fsub (gB q) (EF q A b u)).lo && zlt (GF q A b u).hi 0

/-- The tests on contracted intervals; the parameter and denominator guards
are part of the test. -/
def tests (q A b u : FI) : Bool :=
  zlt 0 (ellB q).lo && zlt 0 (sdenF q).lo &&
    (necFail q A b u || priceOK q A b u)

/-- Two contraction rounds followed by the tests. -/
def leafAfter (q A b u : FI) : Bool :=
  let A1 := cA q A b
  let b1 := cb q A1 b
  let u1 := cu q A1 u
  let A2 := cA q A1 b1
  let b2 := cb q A2 b1
  let u2 := cu q A2 u1
  empty A1 || empty b1 || empty u1 || empty A2 || empty b2 || empty u2 || tests q A2 b2 u2

/-- The leaf test of one dyadic box. The prefix form `IBox.qI B` names the copies above;
the dot form `B.qI` would name the originals in `FixedPoint.IBox`. -/
def leafOK (B : IBox) : Bool :=
  atOK (IBox.qI B).lo && atOK (IBox.qI B).hi && zlt 0 (ellB (IBox.qI B)).lo &&
    leafAfter (IBox.qI B) (IBox.AI B) (IBox.bI B) (IBox.uI B)

/-! Equality with the replaced operations and definitions. -/

theorem zsubNatNat_eq (m n : ℕ) : zsubNatNat m n = Int.subNatNat m n := rfl

theorem zadd_eq (a b : ℤ) : zadd a b = a + b := by
  cases a <;> cases b <;> rfl

theorem zsub_eq (a b : ℤ) : zsub a b = a - b := by
  cases a <;> cases b <;>
    simp [zsub, zsubNatNat_eq, Int.subNatNat_eq_coe, Int.negOfNat_eq, Int.negSucc_eq] <;> omega

theorem zmul_eq (a b : ℤ) : zmul a b = a * b := by
  cases a <;> cases b <;> rfl

theorem zdiv_eq (a b : ℤ) : zdiv a b = a / b := by
  rcases a with m | m <;> rcases b with (_ | n) | n <;> rfl

theorem zle_eq (a b : ℤ) : zle a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases a <;> cases b <;> simp [zle] <;> omega

theorem zlt_eq (a b : ℤ) : zlt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases a <;> cases b <;> simp [zlt] <;> omega

theorem zmin_eq (a b : ℤ) : zmin a b = min a b := by
  simp only [zmin, zle_eq, Bool.cond_decide]
  rfl

theorem zmax_eq (a b : ℤ) : zmax a b = max a b := by
  simp only [zmax, zle_eq, Bool.cond_decide]
  rfl

theorem fl_eq (n d : ℤ) : fl n d = FixedPoint.fl n d := zdiv_eq n d

theorem ce_eq (n d : ℤ) : ce n d = FixedPoint.ce n d := by
  simp only [ce, FixedPoint.ce, zdiv_eq]
  rfl

theorem fint_eq (k : ℤ) : fint k = FixedPoint.fint k := by
  simp only [fint, FixedPoint.fint, zmul_eq]

theorem frat_eq (p d : ℤ) : frat p d = FixedPoint.frat p d := by
  simp only [frat, FixedPoint.frat, fl_eq, ce_eq, zmul_eq]

theorem fadd_eq (a b : FI) : fadd a b = FixedPoint.fadd a b := by
  simp only [fadd, FixedPoint.fadd, zadd_eq]

theorem fsub_eq (a b : FI) : fsub a b = FixedPoint.fsub a b := by
  simp only [fsub, FixedPoint.fsub, zsub_eq]

theorem fnsmul_eq (n : ℕ) (a : FI) : fnsmul n a = FixedPoint.fnsmul n a := by
  simp only [fnsmul, FixedPoint.fnsmul, zmul_eq, Int.ofNat_eq_natCast]

theorem fdivn_eq (a : FI) (n : ℕ) : fdivn a n = FixedPoint.fdivn a n := by
  simp only [fdivn, FixedPoint.fdivn, fl_eq, ce_eq, Int.ofNat_eq_natCast]

theorem fmin_eq (a b : FI) : fmin a b = FixedPoint.fmin a b := by
  simp only [fmin, FixedPoint.fmin, zmin_eq]

theorem fmax_eq (a b : FI) : fmax a b = FixedPoint.fmax a b := by
  simp only [fmax, FixedPoint.fmax, zmax_eq]

theorem fmul_eq (a b : FI) : fmul a b = FixedPoint.fmul a b := by
  simp only [fmul, FixedPoint.fmul, fl_eq, ce_eq, zmin_eq, zmax_eq, zmul_eq]

theorem fsq_eq (a : FI) : fsq a = FixedPoint.fsq a := by
  simp only [fsq, FixedPoint.fsq, zle_eq, Bool.cond_decide, fl_eq, ce_eq, zmax_eq, zmul_eq]

theorem frecip_eq (a : FI) : frecip a = FixedPoint.frecip a := by
  simp only [frecip, FixedPoint.frecip, fl_eq, ce_eq, zmul_eq]

theorem fdiv_eq (a b : FI) : fdiv a b = FixedPoint.fdiv a b := by
  simp only [fdiv, FixedPoint.fdiv, fmul_eq, frecip_eq]

theorem fsqrt_eq (a : FI) : fsqrt a = FixedPoint.fsqrt a := by
  simp only [fsqrt, FixedPoint.fsqrt, zle_eq, zmax_eq, zadd_eq, zmul_eq, Int.ofNat_eq_natCast,
    ← Bool.decide_and, Bool.cond_decide]

theorem seg_eq (off W : ℤ) (i k : ℕ) : seg off W i k = FixedPoint.seg off W i k := by
  simp only [seg, FixedPoint.seg, zadd_eq, zdiv_eq, zmul_eq, Int.ofNat_eq_natCast]
  rfl

theorem IBox.qI_eq (B : IBox) : IBox.qI B = FixedPoint.IBox.qI B := seg_eq _ _ _ _

theorem IBox.AI_eq (B : IBox) : IBox.AI B = FixedPoint.IBox.AI B := seg_eq _ _ _ _

theorem IBox.bI_eq (B : IBox) : IBox.bI B = FixedPoint.IBox.bI B := seg_eq _ _ _ _

theorem IBox.uI_eq (B : IBox) : IBox.uI B = FixedPoint.IBox.uI B := seg_eq _ _ _ _

theorem rAt_eq (Q : ℤ) : rAt Q = FixedPoint.rAt Q := by
  simp only [rAt, FixedPoint.rAt, fadd_eq, fint_eq, fnsmul_eq, fmul_eq]

theorem ellAt_eq (Q : ℤ) : ellAt Q = FixedPoint.ellAt Q := by
  simp only [ellAt, FixedPoint.ellAt, fdiv_eq, fsub_eq, fadd_eq, fint_eq]

theorem gAt_eq (Q : ℤ) : gAt Q = FixedPoint.gAt Q := by
  simp only [gAt, FixedPoint.gAt, fdiv_eq, fmul_eq, fadd_eq, fint_eq, fnsmul_eq, rAt_eq]

theorem yAt_eq (Q : ℤ) : yAt Q = FixedPoint.yAt Q := by
  simp only [yAt, FixedPoint.yAt, fdiv_eq, fnsmul_eq, rAt_eq]

theorem f1At_eq (Q : ℤ) : f1At Q = FixedPoint.f1At Q := by
  simp only [f1At, FixedPoint.f1At, fdiv_eq, fadd_eq, fint_eq, rAt_eq]

theorem f2At_eq (Q : ℤ) : f2At Q = FixedPoint.f2At Q := by
  simp only [f2At, FixedPoint.f2At, fdiv_eq, rAt_eq]

theorem pAt_eq (Q : ℤ) : pAt Q = FixedPoint.pAt Q := by
  simp only [pAt, FixedPoint.pAt, fadd_eq, fint_eq, fnsmul_eq, fmul_eq]

theorem rpAt_eq (Q A : ℤ) : rpAt Q A = FixedPoint.rpAt Q A := by
  simp only [rpAt, FixedPoint.rpAt, fadd_eq, fsub_eq, fmul_eq, fint_eq, ellAt_eq, gAt_eq]

theorem surAt_eq (Q A : ℤ) : surAt Q A = FixedPoint.surAt Q A := by
  simp only [surAt, FixedPoint.surAt, fsub_eq, fdivn_eq, fadd_eq, fint_eq, fnsmul_eq, fmul_eq,
    fsq_eq, ellAt_eq, gAt_eq]

theorem atOK_eq (Q : ℤ) : atOK Q = FixedPoint.atOK Q := by
  simp only [atOK, FixedPoint.atOK, zlt_eq, fadd_eq, fint_eq, fnsmul_eq, rAt_eq]

theorem ellB_eq (q : FI) : ellB q = FixedPoint.ellB q := by
  simp only [ellB, FixedPoint.ellB, ellAt_eq]

theorem deB_eq (q : FI) : deB q = FixedPoint.deB q := by
  simp only [deB, FixedPoint.deB, fsub_eq, fint_eq, ellB_eq]

theorem gB_eq (q : FI) : gB q = FixedPoint.gB q := by
  simp only [gB, FixedPoint.gB, gAt_eq]

theorem yB_eq (q : FI) : yB q = FixedPoint.yB q := by
  simp only [yB, FixedPoint.yB, yAt_eq]

theorem f1B_eq (q : FI) : f1B q = FixedPoint.f1B q := by
  simp only [f1B, FixedPoint.f1B, f1At_eq]

theorem pB_eq (q : FI) : pB q = FixedPoint.pB q := by
  simp only [pB, FixedPoint.pB, pAt_eq]

theorem f2B_eq (q : FI) : f2B q = FixedPoint.f2B q := by
  simp only [f2B, FixedPoint.f2B, f2At_eq]

theorem hB_eq (q : FI) : hB q = FixedPoint.hB q := by
  simp only [hB, FixedPoint.hB, fdivn_eq, fmul_eq, f1B_eq, pB_eq]

theorem KB_eq (q : FI) : KB q = FixedPoint.KB q := by
  simp only [KB, FixedPoint.KB, fmul_eq, frat_eq, fsub_eq, fint_eq, f2B_eq]

theorem RPB_eq (q A : FI) : RPB q A = FixedPoint.RPB q A := by
  simp only [RPB, FixedPoint.RPB, rpAt_eq]

theorem surB_eq (q A : FI) : surB q A = FixedPoint.surB q A := by
  simp only [surB, FixedPoint.surB, surAt_eq]

theorem narrowHi_eq (a c : FI) : narrowHi a c = FixedPoint.narrowHi a c := by
  simp only [narrowHi, FixedPoint.narrowHi, zmin_eq]

theorem narrowLo_eq (a c : FI) : narrowLo a c = FixedPoint.narrowLo a c := by
  simp only [narrowLo, FixedPoint.narrowLo, zmax_eq]

theorem cA_eq (q A b : FI) : cA q A b = FixedPoint.cA q A b := by
  simp only [cA, FixedPoint.cA, narrowHi_eq, fdivn_eq, fadd_eq, fsub_eq, fint_eq, yB_eq]

theorem cb_eq (q A b : FI) : cb q A b = FixedPoint.cb q A b := by
  simp only [cb, FixedPoint.cb, narrowHi_eq, narrowLo_eq, fsub_eq, fnsmul_eq, fint_eq, KB_eq]

theorem cu_eq (q A u : FI) : cu q A u = FixedPoint.cu q A u := by
  simp only [cu, FixedPoint.cu, narrowHi_eq, narrowLo_eq, fdiv_eq, fsub_eq, fnsmul_eq, fmul_eq,
    fint_eq, ellB_eq, gB_eq, RPB_eq]

theorem empty_eq (a : FI) : empty a = FixedPoint.empty a := by
  simp only [empty, FixedPoint.empty, zlt_eq]

theorem etaF_eq (A b u : FI) : etaF A b u = FixedPoint.etaF A b u := by
  simp only [etaF, FixedPoint.etaF, fsub_eq, fint_eq]

theorem r0F_eq (A : FI) : r0F A = FixedPoint.r0F A := by
  simp only [r0F, FixedPoint.r0F, fsub_eq, fnsmul_eq, fint_eq]

theorem RCF_eq (q A b u : FI) : RCF q A b u = FixedPoint.RCF q A b u := by
  simp only [RCF, FixedPoint.RCF, fmin_eq, fadd_eq, fsub_eq, fdiv_eq, fnsmul_eq, fmul_eq, fint_eq,
    ellB_eq, gB_eq]

theorem sdenF_eq (q : FI) : sdenF q = FixedPoint.sdenF q := by
  simp only [sdenF, FixedPoint.sdenF, fsub_eq, frat_eq, deB_eq]

theorem scF_eq (q A : FI) : scF q A = FixedPoint.scF q A := by
  simp only [scF, FixedPoint.scF, fdiv_eq, surB_eq, sdenF_eq]

theorem TF_eq (q A : FI) : TF q A = FixedPoint.TF q A := by
  simp only [TF, FixedPoint.TF, fsqrt_eq, scF_eq]

theorem CF_eq (q A b : FI) : CF q A b = FixedPoint.CF q A b := by
  simp only [CF, FixedPoint.CF, fmin_eq, fsub_eq, r0F_eq, KB_eq, TF_eq]

theorem QF_eq (q A b u : FI) : QF q A b u = FixedPoint.QF q A b u := by
  simp only [QF, FixedPoint.QF, fmin_eq, fmul_eq, fsq_eq, fsub_eq, fnsmul_eq, CF_eq, etaF_eq,
    hB_eq]

theorem pF_eq (q u : FI) : pF q u = FixedPoint.pF q u := by
  simp only [pF, FixedPoint.pF, fsub_eq, yB_eq]

theorem lp0F_eq (q A b u : FI) : lp0F q A b u = FixedPoint.lp0F q A b u := by
  simp only [lp0F, FixedPoint.lp0F, fsub_eq, fmin_eq, fdivn_eq, pF_eq, etaF_eq, CF_eq]

theorem vF_eq (q u : FI) : vF q u = FixedPoint.vF q u := by
  simp only [vF, FixedPoint.vF, fsub_eq, fnsmul_eq, fint_eq, hB_eq]

theorem gapF_eq (q A u : FI) : gapF q A u = FixedPoint.gapF q A u := by
  simp only [gapF, FixedPoint.gapF, fmax_eq, fadd_eq, fsub_eq, fnsmul_eq, fint_eq, KB_eq, TF_eq]

theorem t0F_eq (q A u : FI) : t0F q A u = FixedPoint.t0F q A u := by
  simp only [t0F, FixedPoint.t0F, fdiv_eq, fmax_eq, fnsmul_eq, fint_eq, gapF_eq, vF_eq]

theorem lpfF_eq (q A b u : FI) : lpfF q A b u = FixedPoint.lpfF q A b u := by
  simp only [lpfF, FixedPoint.lpfF, fmin_eq, fadd_eq, fmul_eq, fsub_eq, fdivn_eq, fnsmul_eq,
    frat_eq, etaF_eq, gapF_eq, t0F_eq]

theorem denF_eq (q A b u : FI) : denF q A b u = FixedPoint.denF q A b u := by
  simp only [denF, FixedPoint.denF, fsub_eq, fnsmul_eq, gapF_eq, etaF_eq]

theorem dgapF_eq (q A : FI) : dgapF q A = FixedPoint.dgapF q A := by
  simp only [dgapF, FixedPoint.dgapF, fmax_eq, fadd_eq, fsub_eq, fnsmul_eq, fint_eq, yB_eq, KB_eq,
    TF_eq]

theorem tfLo_eq (q A b u : FI) : tfLo q A b u = FixedPoint.tfLo q A b u := by
  simp only [tfLo, FixedPoint.tfLo, zlt_eq, Bool.cond_decide, fmax_eq, fdiv_eq, fint_eq, denF_eq,
    t0F_eq, dgapF_eq]

theorem jointLo_eq (q A b u : FI) : jointLo q A b u = FixedPoint.jointLo q A b u := by
  simp only [jointLo, FixedPoint.jointLo, zsub_eq, zmul_eq, zmax_eq, ce_eq, fsub_eq, fsq_eq,
    fmul_eq, fint_eq, yB_eq, pF_eq, tfLo_eq, QF_eq]

theorem poleF_eq (q A b u : FI) : poleF q A b u = FixedPoint.poleF q A b u := by
  simp only [poleF, FixedPoint.poleF, fmax_eq, fadd_eq, fsub_eq, fnsmul_eq, fint_eq, KB_eq, TF_eq,
    RCF_eq]

theorem edenF_eq (q A : FI) : edenF q A = FixedPoint.edenF q A := by
  simp only [edenF, FixedPoint.edenF, fadd_eq, fmul_eq, fsub_eq, fnsmul_eq, fint_eq, ellB_eq,
    gB_eq]

theorem thetaF_eq (q A : FI) : thetaF q A = FixedPoint.thetaF q A := by
  simp only [thetaF, FixedPoint.thetaF, fsub_eq, fdiv_eq, fnsmul_eq, gB_eq, deB_eq]

theorem momentF_eq (q A b u : FI) : momentF q A b u = FixedPoint.momentF q A b u := by
  simp only [momentF, FixedPoint.momentF, fsub_eq, fmul_eq, thetaF_eq, RCF_eq, deB_eq, pF_eq]

theorem zeropriceF_eq (q A b u : FI) : zeropriceF q A b u = FixedPoint.zeropriceF q A b u := by
  simp only [zeropriceF, FixedPoint.zeropriceF, fsub_eq, fmul_eq, fmax_eq, fnsmul_eq, fint_eq,
    gB_eq, thetaF_eq, RCF_eq]

theorem EF_eq (q A b u : FI) : EF q A b u = FixedPoint.EF q A b u := by
  simp only [EF, FixedPoint.EF, fmul_eq, fdiv_eq, fmax_eq, fsub_eq, fnsmul_eq, fint_eq, gB_eq,
    edenF_eq, r0F_eq, ellB_eq, RPB_eq]

theorem GF_eq (q A b u : FI) : GF q A b u = FixedPoint.GF q A b u := by
  simp only [GF, FixedPoint.GF, fadd_eq, fsub_eq, fdiv_eq, fmul_eq, fmax_eq, fint_eq, ellB_eq,
    gB_eq, etaF_eq, poleF_eq, RCF_eq, EF_eq]

theorem necFail_eq (q A b u : FI) : necFail q A b u = FixedPoint.necFail q A b u := by
  simp only [necFail, FixedPoint.necFail, zlt_eq, zle_eq, fsub_eq, fnsmul_eq, fmul_eq, yB_eq,
    etaF_eq, r0F_eq, ellB_eq, RPB_eq, RCF_eq, scF_eq, CF_eq, QF_eq, lp0F_eq, vF_eq, pF_eq,
    lpfF_eq, jointLo_eq]

theorem priceOK_eq (q A b u : FI) : priceOK q A b u = FixedPoint.priceOK q A b u := by
  simp only [priceOK, FixedPoint.priceOK, zlt_eq, fsub_eq, poleF_eq, RPB_eq, edenF_eq,
    momentF_eq, zeropriceF_eq, gB_eq, EF_eq, GF_eq]

theorem tests_eq (q A b u : FI) : tests q A b u = FixedPoint.tests q A b u := by
  simp only [tests, FixedPoint.tests, zlt_eq, ellB_eq, sdenF_eq, necFail_eq, priceOK_eq]

theorem leafAfter_eq (q A b u : FI) : leafAfter q A b u = FixedPoint.leafAfter q A b u := by
  simp only [leafAfter, FixedPoint.leafAfter, cA_eq, cb_eq, cu_eq, empty_eq, tests_eq]

/-- The kernel form of the leaf test is `leafOK`. -/
theorem leafOK_eq (B : IBox) : leafOK B = FixedPoint.leafOK B := by
  simp only [leafOK, FixedPoint.leafOK, zlt_eq, atOK_eq, IBox.qI_eq, IBox.AI_eq, IBox.bI_eq,
    IBox.uI_eq, ellB_eq, leafAfter_eq]

end Erdos1017.MiddleE2LargeUniversal.FixedPoint.Kernel
