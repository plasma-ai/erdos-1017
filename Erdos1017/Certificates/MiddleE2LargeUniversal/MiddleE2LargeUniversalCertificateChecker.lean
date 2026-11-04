module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalFixedPoint

/-!
# Fixed-point checker for the large-atom certificate

The fixed-point large-atom checker. Boxes are dyadic index boxes, so a
child box is a few natural-number operations on its parent and no recursive
parent interval expression is ever evaluated. Contraction is performed
locally inside each leaf test and is never stored.
-/

@[expose] public section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

/-! Initial box at scale `S = 1000·2^30`. -/

/-- `157/1000·S`. -/
def qOff : ℤ := 168577466368
/-- `43/1000·S`. -/
def qW : ℤ := 46170898432
/-- `⌊S/3⌋`. -/
def aOff : ℤ := 357913941333
/-- `369/1000·S - ⌊S/3⌋`. -/
def aW : ℤ := 38296791723
/-- `⌈S/3⌉`. -/
def bW : ℤ := 357913941334

/-- The floored dyadic segment `off + [⌊W i / 2^k⌋, ⌊W (i + 1) / 2^k⌋]`. -/
def seg (off W : ℤ) (i k : ℕ) : FI :=
  ⟨off + W * i / ((2 ^ k : ℕ) : ℤ), off + W * (i + 1) / ((2 ^ k : ℕ) : ℤ)⟩

/-- A dyadic box of the initial box. -/
structure IBox where
  iq : ℕ
  kq : ℕ
  iA : ℕ
  kA : ℕ
  ib : ℕ
  kb : ℕ
  iu : ℕ
  ku : ℕ

namespace IBox

def qI (B : IBox) : FI := seg qOff qW B.iq B.kq
def AI (B : IBox) : FI := seg aOff aW B.iA B.kA
def bI (B : IBox) : FI := seg 0 bW B.ib B.kb
def uI (B : IBox) : FI := seg 0 bW B.iu B.ku

/-- Bisect a coordinate of least depth, in the order `q, A, b, u`. -/
def split (B : IBox) : IBox × IBox :=
  if B.kq ≤ B.kA ∧ B.kq ≤ B.kb ∧ B.kq ≤ B.ku then
    ({ B with iq := 2 * B.iq, kq := B.kq + 1 }, { B with iq := 2 * B.iq + 1, kq := B.kq + 1 })
  else if B.kA ≤ B.kb ∧ B.kA ≤ B.ku then
    ({ B with iA := 2 * B.iA, kA := B.kA + 1 }, { B with iA := 2 * B.iA + 1, kA := B.kA + 1 })
  else if B.kb ≤ B.ku then
    ({ B with ib := 2 * B.ib, kb := B.kb + 1 }, { B with ib := 2 * B.ib + 1, kb := B.kb + 1 })
  else
    ({ B with iu := 2 * B.iu, ku := B.ku + 1 }, { B with iu := 2 * B.iu + 1, ku := B.ku + 1 })

def root : IBox := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

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
  decide (0 < (fadd (fint 2) (fpt Q)).lo) && decide (0 < (fnsmul 2 (rAt Q)).lo) &&
    decide (0 < (rAt Q).lo)

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

def narrowHi (a c : FI) : FI := ⟨a.lo, min a.hi c.hi⟩
def narrowLo (a c : FI) : FI := ⟨max a.lo c.lo, a.hi⟩

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

def empty (a : FI) : Bool := decide (a.hi < a.lo)

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
  if 0 < (denF q A b u).lo then
    (fmax (t0F q A u) (fmax (fint 0) (fdiv (dgapF q A) (denF q A b u)))).lo
  else (t0F q A u).lo
/-- A lower endpoint for the joint expression. -/
def jointLo (q A b u : FI) : ℤ :=
  (fsub (fsq (fsub (fsub (fsub (fint 1) A) b) (yB q))) (fmul (fsub (yB q) A) (pF q u))).lo -
    ce (max 0 (S - 2 * tfLo q A b u) * (QF q A b u).hi) S
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
def EF (q A b u : FI) : FI :=
  fmul (fmul (fdiv (fmax (fint 0) (fsub A (fnsmul 3 (gB q)))) (edenF q A)) (fsub (r0F A) u))
    (fmax (fint 0) (fsub (fnsmul 2 (ellB q)) (fdiv (RPB q A) u)))
def GF (q A b u : FI) : FI :=
  fadd (fsub (fadd (fdiv (fmul (fmax (fint 0) (fsub (fmul b (ellB q)) (gB q))) (etaF A b u))
    (poleF q A b u)) (fmul (ellB q) (fadd (fsub (RCF q A b u) A) b))) (gB q)) (EF q A b u)

/-- Rejection by a violated necessary inequality. -/
def necFail (q A b u : FI) : Bool :=
  decide ((fsub (yB q) A).hi < 0) || decide ((etaF A b u).hi < 0) ||
    decide ((fsub (r0F A) b).hi < 0) || decide ((fsub (r0F A) u).hi < 0) ||
    decide ((fsub (fnsmul 2 (fmul (ellB q) u)) (RPB q A)).hi < 0) ||
    decide ((RCF q A b u).hi < 0) || decide ((scF q A).hi < 0) ||
    decide ((CF q A b).hi < 0) || decide ((QF q A b u).hi < 0) ||
    decide ((lp0F q A b u).hi < 0) || decide ((vF q u).hi ≤ 0) ||
    (decide (0 < (vF q u).lo) && decide ((fsub (pF q u) (lpfF q A b u)).hi < 0)) ||
    (decide (0 < (vF q u).lo) && decide (0 < jointLo q A b u))

/-- Acceptance by all five price tests and their denominators. -/
def priceOK (q A b u : FI) : Bool :=
  decide (0 < (poleF q A b u).lo) && decide (0 < u.lo) && decide (0 < (RPB q A).lo) &&
    decide (0 < (edenF q A).lo) && decide (0 < A.lo) &&
    decide (0 < (momentF q A b u).lo) && decide (0 < (zeropriceF q A b u).lo) &&
    decide (0 < (fsub (gB q) (EF q A b u)).lo) && decide ((GF q A b u).hi < 0)

/-- The tests on contracted intervals; the parameter and denominator guards
are part of the test. -/
def tests (q A b u : FI) : Bool :=
  decide (0 < (ellB q).lo) && decide (0 < (sdenF q).lo) &&
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

/-- The leaf test of one dyadic box. -/
def leafOK (B : IBox) : Bool :=
  atOK B.qI.lo && atOK B.qI.hi && decide (0 < (ellB B.qI).lo) &&
    leafAfter B.qI B.AI B.bI B.uI

/-- Depth-bounded bisection cover: every leaf passes `leafOK`. -/
def cover : ℕ → IBox → Bool
  | 0, B => leafOK B
  | n + 1, B => leafOK B || (cover n B.split.1 && cover n B.split.2)

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
