module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificatePartition
public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateContraction

/-!
# Soundness of the large-atom certificate

A successful leaf either contradicts a necessary inequality or verifies all
strict price tests, the dyadic cover is sound including boundary points, so the
fixed-point certificate entails the five price tests (`priceTests_of_cover`),
with the Boolean computation left as an explicit premise.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

private def val (n : ℤ) : ℝ := n / (S : ℝ)

private theorem mem_bounds {x : ℝ} {a : FI} (h : SMem x a) :
    val a.lo ≤ x ∧ x ≤ val a.hi := by
  exact ⟨(div_le_iff₀ S_posR).mpr h.1, (le_div_iff₀ S_posR).mpr h.2⟩

private theorem span_mem {x y z : ℝ} {a b : FI} (hx : SMem x a) (hy : SMem y b)
    (hxz : x ≤ z) (hzy : z ≤ y) : SMem z ⟨a.lo, b.hi⟩ :=
  ⟨hx.1.trans (mul_le_mul_of_nonneg_right hxz S_posR.le),
    (mul_le_mul_of_nonneg_right hzy S_posR.le).trans hy.2⟩

private theorem mem_rAt (Q : ℤ) : SMem (rq (val Q)) (rAt Q) := by
  simpa [rAt, rq, val] using
    mem_fadd (mem_fadd (mem_fint 1) (mem_fnsmul 7 (mem_fpt Q)))
      (mem_fmul (mem_fpt Q) (mem_fpt Q))

private theorem at_guards {Q : ℤ} (h : atOK Q = true) :
    0 < (fadd (fint 2) (fpt Q)).lo ∧ 0 < (fnsmul 2 (rAt Q)).lo ∧
      0 < (rAt Q).lo := by
  simpa only [atOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

private theorem mem_ellAt {Q : ℤ} (h : atOK Q = true) :
    SMem (ellq (val Q)) (ellAt Q) := by
  simpa [ellAt, ellq, val] using mem_fdiv
    (mem_fsub (mem_fint 2) (mem_fpt Q)) (mem_fadd (mem_fint 2) (mem_fpt Q))
    (at_guards h).1

private theorem mem_gAt {Q : ℤ} (h : atOK Q = true) :
    SMem (gq (val Q)) (gAt Q) := by
  simpa [gAt, gq, val] using mem_fdiv
    (mem_fmul (mem_fpt Q) (mem_fadd (mem_fint 1) (mem_fnsmul 2 (mem_fpt Q))))
    (mem_fnsmul 2 (mem_rAt Q)) (at_guards h).2.1

private theorem mem_yAt {Q : ℤ} (h : atOK Q = true) :
    SMem (yq (val Q)) (yAt Q) := by
  simpa [yAt, yq, val] using mem_fdiv (mem_fnsmul 9 (mem_fpt Q))
    (mem_fnsmul 2 (mem_rAt Q)) (at_guards h).2.1

private theorem mem_f1At {Q : ℤ} (h : atOK Q = true) :
    SMem (f1q (val Q)) (f1At Q) := by
  simpa [f1At, f1q, val] using mem_fdiv (mem_fadd (mem_fpt Q) (mem_fint 2))
    (mem_rAt Q) (at_guards h).2.2

private theorem mem_f2At {Q : ℤ} (h : atOK Q = true) :
    SMem (f2q (val Q)) (f2At Q) := by
  simpa [f2At, f2q, val] using mem_fdiv (mem_fpt Q) (mem_rAt Q) (at_guards h).2.2

private theorem mem_pAt (Q : ℤ) : SMem (pq (val Q)) (pAt Q) := by
  simpa [pAt, pq, val, mul_assoc] using
    mem_fadd (mem_fadd (mem_fint 1) (mem_fnsmul 4 (mem_fpt Q)))
      (mem_fnsmul 13 (mem_fmul (mem_fpt Q) (mem_fpt Q)))

private theorem mem_rpAt {Q : ℤ} (h : atOK Q = true) (A : ℤ) :
    SMem (rpq (val Q) (val A)) (rpAt Q A) := by
  simpa [rpAt, rpq, val] using
    mem_fadd (mem_fsub (mem_fmul (mem_ellAt h) (mem_fsub (mem_fint 1) (mem_fpt A)))
      (mem_fpt A)) (mem_gAt h)

private theorem mem_surAt {Q : ℤ} (h : atOK Q = true) (A : ℤ) :
    SMem (surq (val A) (val Q)) (surAt Q A) := by
  simpa [surAt, surq, deq, val] using mem_fsub
    (mem_fdivn 3 (by decide) (mem_fsub (mem_fadd (mem_fint (-1))
      (mem_fnsmul 6 (mem_fpt A))) (mem_fmul
      (mem_fsub (mem_fint 8) (mem_fnsmul 3 (mem_fsub (mem_fint 1) (mem_ellAt h))))
      (mem_fsq (mem_fpt A))))) (mem_gAt h)

private structure Params (P : Point) (q : FI) : Prop where
  qmem : SMem P.q q
  lo_window : QWindow (val q.lo)
  hi_window : QWindow (val q.hi)
  lo_ok : atOK q.lo = true
  hi_ok : atOK q.hi = true

private theorem Params.window {P : Point} {q : FI} (c : Params P q) : QWindow P.q :=
  ⟨c.lo_window.1.trans (mem_bounds c.qmem).1,
    (mem_bounds c.qmem).2.trans c.hi_window.2⟩

private theorem Params.ell {P : Point} {q : FI} (c : Params P q) :
    SMem P.ell (ellB q) := by
  exact span_mem (mem_ellAt c.hi_ok) (mem_ellAt c.lo_ok)
    (ellq_anti (by linarith [c.window.1]) (mem_bounds c.qmem).2)
    (ellq_anti (by linarith [c.lo_window.1]) (mem_bounds c.qmem).1)

private theorem Params.de {P : Point} {q : FI} (c : Params P q) :
    SMem P.de (deB q) := by
  simpa only [deB, Point.de, deq, Point.ell, Int.cast_one] using mem_fsub (mem_fint 1) c.ell

private theorem Params.g {P : Point} {q : FI} (c : Params P q) : SMem P.g (gB q) :=
  span_mem (mem_gAt c.lo_ok) (mem_gAt c.hi_ok)
    (gq_mono (by linarith [c.lo_window.1]) (mem_bounds c.qmem).1)
    (gq_mono (by linarith [c.window.1]) (mem_bounds c.qmem).2)

private theorem Params.y {P : Point} {q : FI} (c : Params P q) : SMem P.y (yB q) :=
  span_mem (mem_yAt c.lo_ok) (mem_yAt c.hi_ok)
    (yq_mono (by linarith [c.lo_window.1]) (mem_bounds c.qmem).1 (by linarith [c.window.2]))
    (yq_mono (by linarith [c.window.1]) (mem_bounds c.qmem).2 (by linarith [c.hi_window.2]))

private theorem Params.f1 {P : Point} {q : FI} (c : Params P q) :
    SMem (f1q P.q) (f1B q) :=
  span_mem (mem_f1At c.hi_ok) (mem_f1At c.lo_ok)
    (f1q_anti (by linarith [c.window.1]) (mem_bounds c.qmem).2)
    (f1q_anti (by linarith [c.lo_window.1]) (mem_bounds c.qmem).1)

private theorem Params.f2 {P : Point} {q : FI} (c : Params P q) :
    SMem (f2q P.q) (f2B q) :=
  span_mem (mem_f2At c.lo_ok) (mem_f2At c.hi_ok)
    (f2q_mono (by linarith [c.lo_window.1]) (mem_bounds c.qmem).1 (by linarith [c.window.2]))
    (f2q_mono (by linarith [c.window.1]) (mem_bounds c.qmem).2 (by linarith [c.hi_window.2]))

private theorem Params.poly {P : Point} {q : FI} (c : Params P q) :
    SMem (pq P.q) (pB q) :=
  span_mem (mem_pAt q.lo) (mem_pAt q.hi)
    (pq_mono (by linarith [c.lo_window.1]) (mem_bounds c.qmem).1)
    (pq_mono (by linarith [c.window.1]) (mem_bounds c.qmem).2)

private theorem Params.h {P : Point} {q : FI} (c : Params P q) : SMem P.h (hB q) := by
  exact (mem_fdivn 8 (by decide) (mem_fmul (mem_fmul c.f1 c.f1) c.poly)).of_eq
    (hq_eq (by linarith [c.window.1])).symm

private theorem Params.K {P : Point} {q : FI} (c : Params P q) : SMem P.K (KB q) := by
  apply (mem_fmul (mem_frat 9 4 (by decide)) (mem_fmul (mem_fmul c.f2 c.f2)
    (mem_fsub (mem_fint 1) (mem_fmul c.qmem c.qmem)))).of_eq
  rw [Point.K, kq_eq (by linarith [c.window.1])]
  push_cast
  ring

private theorem Params.RP {P : Point} {q A : FI} (c : Params P q)
    (hA : SMem P.A A) (hP : P.InBox) : SMem P.RP (RPB q A) := by
  apply span_mem (mem_rpAt c.hi_ok A.hi) (mem_rpAt c.lo_ok A.lo)
  · exact (rpq_anti_A c.hi_window (mem_bounds hA).2).trans
      (rpq_anti_q c.window c.hi_window (mem_bounds c.qmem).2 hP.2.2.2.1)
  · exact (rpq_anti_q c.lo_window c.window (mem_bounds c.qmem).1 hP.2.2.2.1).trans
      (rpq_anti_A c.lo_window (mem_bounds hA).1)

private theorem Params.sur {P : Point} {q A : FI} (c : Params P q)
    (hA : SMem P.A A) (hP : P.InBox)
    (hlo : 0 ≤ val A.lo) (hhi : val A.hi ≤ 369 / 1000) :
    SMem (surq P.A P.q) (surB q A) := by
  have hPA : 0 ≤ P.A := by linarith [hP.2.2.1]
  apply span_mem (mem_surAt c.hi_ok A.lo) (mem_surAt c.lo_ok A.hi)
  · exact (surq_mono_A c.hi_window hlo (mem_bounds hA).1 hP.2.2.2.1).trans
      (surq_anti_q c.window c.hi_window (mem_bounds c.qmem).2 hPA hP.2.2.2.1)
  · exact (surq_anti_q c.lo_window c.window (mem_bounds c.qmem).1 hPA hP.2.2.2.1).trans
      (surq_mono_A c.lo_window hPA (mem_bounds hA).2 hhi)

/-- All interval resources at one original Point and one locally contracted box. -/
private structure Ctx (P : Point) (q A b u : FI) : Prop where
  params : Params P q
  hA : SMem P.A A
  hb : SMem P.b b
  hu : SMem P.u u
  box : P.InBox
  nec : P.Necessary
  Alo : 0 ≤ val A.lo
  Ahi : val A.hi ≤ 369 / 1000

private theorem fnsmul_lo_pos (n : ℕ) (hn : 0 < n) {a : FI} (ha : 0 < a.lo) :
    0 < (fnsmul n a).lo := mul_pos (by exact_mod_cast hn) ha

section Enclosures

variable {P : Point} {q A b u : FI}

private theorem Ctx.eta (c : Ctx P q A b u) : SMem P.eta (etaF A b u) := by
  simpa only [Point.eta, etaF, Int.cast_one] using
    mem_fsub (mem_fsub (mem_fsub (mem_fint 1) c.hA) c.hb) c.hu

private theorem Ctx.r0 (c : Ctx P q A b u) : SMem P.r0 (r0F A) := by
  simpa only [Point.r0, r0F, Int.cast_one, Nat.cast_ofNat] using
    mem_fsub (mem_fint 1) (mem_fnsmul 2 c.hA)

private theorem Ctx.RC (c : Ctx P q A b u) (hl : 0 < (ellB q).lo) :
    SMem P.RC (RCF q A b u) := by
  simpa only [Point.RC, RCF, Int.cast_one, Nat.cast_ofNat, mul_assoc] using
    mem_fmin (mem_fadd (mem_fsub (mem_fint 1) (mem_fnsmul 3 c.hA)) c.hb)
      (mem_fdiv (mem_fsub (mem_fsub (mem_fsub (mem_fint 1) c.hu)
        (mem_fnsmul 2 (mem_fmul c.params.ell c.hA))) (mem_fnsmul 3 c.params.g))
        c.params.ell hl)

private theorem Ctx.sden (c : Ctx P q A b u) : SMem (1 / 5 - P.de) (sdenF q) := by
  simpa [sdenF] using mem_fsub (mem_frat 1 5 (by decide)) c.params.de

private theorem Ctx.sc (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.sc (scF q A) := by
  exact mem_fdiv (c.params.sur c.hA c.box c.Alo c.Ahi) c.sden hs

private theorem Ctx.T (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.T (TF q A) := mem_fsqrt (c.sc hs)

private theorem Ctx.C (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.C (CF q A b) :=
  mem_fmin (mem_fmin (mem_fsub c.r0 c.hb) (mem_fsub (mem_fsub c.hA c.hb) c.params.K))
    (mem_fsub (c.T hs) c.hb)

private theorem Ctx.Q (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.Q (QF q A b u) := by
  simpa only [Point.Q, QF, Nat.cast_ofNat, mul_assoc] using
    mem_fmin (mem_fmin (mem_fmul (c.C hs) c.eta) (mem_fsq c.eta))
      (mem_fsub (mem_fsub (mem_fsub c.params.h (mem_fsq c.hA)) (mem_fsq c.hb))
        (mem_fnsmul 2 (mem_fmul c.hb c.eta)))

private theorem Ctx.p (c : Ctx P q A b u) : SMem P.p (pF q u) := mem_fsub c.params.y c.hu

private theorem Ctx.lp0 (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem (P.p - min (P.eta / 2) (P.eta - P.C)) (lp0F q A b u) :=
  mem_fsub c.p (mem_fmin (mem_fdivn 2 (by decide) c.eta) (mem_fsub c.eta (c.C hs)))

private theorem Ctx.v (c : Ctx P q A b u) : SMem P.v (vF q u) := by
  simpa only [Point.v, vF, Int.cast_one, Nat.cast_ofNat] using
    mem_fsub (mem_fsub (mem_fint 1) (mem_fnsmul 2 c.params.h)) c.hu

private theorem Ctx.gap (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.gap (gapF q A u) := by
  simpa only [Point.gap, gapF, Int.cast_one, Nat.cast_ofNat] using
    mem_fmax (mem_fmax (mem_fsub c.hA c.hu)
      (mem_fadd (mem_fsub (mem_fsub (mem_fint 1) (mem_fnsmul 2 c.hA)) c.hu) c.params.K))
      (mem_fsub (mem_fsub (mem_fsub (mem_fint 1) c.hA) c.hu) (c.T hs))

private theorem Ctx.t0 (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo)
    (hv : 0 < (vF q u).lo) : SMem P.t0 (t0F q A u) := by
  simpa only [Point.t0, t0F, Int.cast_zero, Nat.cast_ofNat] using
    mem_fdiv (mem_fmax (mem_fint 0) (c.gap hs)) (mem_fnsmul 3 c.v)
      (fnsmul_lo_pos 3 (by decide) hv)

private theorem Ctx.lpf (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo)
    (hv : 0 < (vF q u).lo) : SMem P.lpf (lpfF q A b u) := by
  simpa only [Point.lpf, lpfF, Int.cast_one, Int.cast_ofNat, Nat.cast_ofNat] using
    mem_fmin (mem_fdivn 2 (by decide) c.eta) (mem_fadd (c.gap hs)
      (mem_fmul (mem_fsub c.eta (mem_fnsmul 2 (c.gap hs)))
        (mem_fmin (mem_frat 1 2 (by decide)) (c.t0 hs hv))))

private theorem Ctx.den (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.den (denF q A b u) := mem_fsub (mem_fnsmul 2 (c.gap hs)) c.eta

private theorem Ctx.dgap (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) :
    SMem P.dgap (dgapF q A) := by
  simpa only [Point.dgap, dgapF, Int.cast_one, Nat.cast_ofNat] using
    mem_fmax (mem_fmax (mem_fsub c.hA c.params.y)
      (mem_fadd (mem_fsub (mem_fsub (mem_fint 1) (mem_fnsmul 2 c.hA)) c.params.y) c.params.K))
      (mem_fsub (mem_fsub (mem_fsub (mem_fint 1) c.hA) (c.T hs)) c.params.y)

private theorem Ctx.tf_lower (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo)
    (hv : 0 < (vF q u).lo) : (tfLo q A b u : ℝ) ≤ P.tf * S := by
  have ht0 := c.t0 hs hv
  unfold tfLo Point.tf
  split_ifs with h1 h2 h2
  · simpa only [Int.cast_zero] using
      (mem_fmax ht0 (mem_fmax (mem_fint 0) (mem_fdiv (c.dgap hs) (c.den hs) h1))).1
  · exact absurd ((c.den hs).pos_of_lo h1) h2
  · exact ht0.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) S_posR.le)
  · exact ht0.1

private theorem Ctx.joint_lower (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo)
    (hv : 0 < (vF q u).lo) : (jointLo q A b u : ℝ) ≤ P.joint * S := by
  have hw := mem_fsub (mem_fsub (mem_fsub (mem_fint 1) c.hA) c.hb) c.params.y
  have hx := mem_fsub (mem_fsq hw) (mem_fmul (mem_fsub c.params.y c.hA) c.p)
  have ht := c.tf_lower hs hv
  have hQ := c.Q hs
  have hQ0 : 0 ≤ P.Q := c.nec.2.2.2.2.2.2.2.2.2.2.2.1
  have hfactor : max 0 (1 - 2 * P.tf) * S ≤ (max 0 (S - 2 * tfLo q A b u) : ℤ) := by
    push_cast
    rw [max_mul_of_nonneg _ _ S_posR.le, zero_mul]
    apply max_le_max le_rfl
    nlinarith
  have hf0 : 0 ≤ max 0 (1 - 2 * P.tf) * (S : ℝ) :=
    mul_nonneg (le_max_left _ _) S_posR.le
  have hprod := mul_le_mul hfactor hQ.2 (mul_nonneg hQ0 S_posR.le) (hf0.trans hfactor)
  have hce := le_ce (n := max 0 (S - 2 * tfLo q A b u) * (QF q A b u).hi) S_pos
  have hprod' : max 0 (1 - 2 * P.tf) * P.Q * S ≤
      (ce (max 0 (S - 2 * tfLo q A b u) * (QF q A b u).hi) S : ℝ) := by
    apply le_trans _ hce
    rw [le_div_iff₀ S_posR]
    push_cast at hprod ⊢
    nlinarith only [hprod]
  unfold jointLo
  push_cast
  change _ ≤ ((1 - P.A - P.b - P.y) ^ 2 - (P.y - P.A) * P.p -
    max 0 (1 - 2 * P.tf) * P.Q) * S
  norm_num only [Int.cast_one] at hx
  linarith [hx.1]

private theorem Ctx.pole (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo)
    (hl : 0 < (ellB q).lo) : SMem P.pole (poleF q A b u) := by
  simpa only [Point.pole, poleF, Nat.cast_ofNat, Int.cast_one, Int.cast_ofNat] using
    mem_fmax (mem_fmax (mem_fsub (mem_fsub (mem_fadd (mem_fnsmul 3 c.hA) c.hb)
      (mem_fint 1)) (c.RC hl)) (mem_fsub (mem_fadd c.hb c.params.K) (c.RC hl)))
      (mem_fmax (mem_fsub (mem_fsub (mem_fadd c.hA c.hb) (c.T hs)) (c.RC hl))
        (mem_fsub (mem_fnsmul 6 c.hA) (mem_fint 2)))

private theorem Ctx.eden (c : Ctx P q A b u) :
    SMem ((2 * P.ell - 1) * P.A + 3 * P.g) (edenF q A) := by
  simpa only [edenF, Nat.cast_ofNat, Int.cast_one] using
    mem_fadd (mem_fmul (mem_fsub (mem_fnsmul 2 c.params.ell) (mem_fint 1)) c.hA)
      (mem_fnsmul 3 c.params.g)

private theorem Ctx.theta (c : Ctx P q A b u) (hA : 0 < A.lo) :
    SMem P.theta (thetaF q A) :=
  mem_fsub (mem_fdiv (mem_fnsmul 3 c.params.g) c.hA hA) c.params.de

private theorem Ctx.moment (c : Ctx P q A b u) (hA : 0 < A.lo) (hl : 0 < (ellB q).lo) :
    SMem P.moment (momentF q A b u) :=
  mem_fsub (mem_fmul (c.theta hA) (mem_fsub c.hA (c.RC hl))) (mem_fmul c.params.de c.p)

private theorem Ctx.zeroprice (c : Ctx P q A b u) (hA : 0 < A.lo) (hl : 0 < (ellB q).lo) :
    SMem P.zeroprice (zeropriceF q A b u) := by
  simpa only [Point.zeroprice, zeropriceF, Int.cast_zero, Int.cast_one, Nat.cast_ofNat] using
    mem_fsub c.params.g (mem_fmul (mem_fmax (mem_fint 0)
      (mem_fsub (mem_fint 1) (mem_fnsmul 2 (c.theta hA)))) (c.RC hl))

private theorem Ctx.E (c : Ctx P q A b u) (he : 0 < (edenF q A).lo) (hu : 0 < u.lo) :
    SMem P.E (EF q A b u) := by
  simpa only [Point.E, EF, Int.cast_zero, Nat.cast_ofNat] using
    mem_fmul (mem_fmul (mem_fdiv (mem_fmax (mem_fint 0)
      (mem_fsub c.hA (mem_fnsmul 3 c.params.g))) c.eden he) (mem_fsub c.r0 c.hu))
      (mem_fmax (mem_fint 0) (mem_fsub (mem_fnsmul 2 c.params.ell)
        (mem_fdiv (c.params.RP c.hA c.box) c.hu hu)))

private theorem Ctx.G (c : Ctx P q A b u) (hs : 0 < (sdenF q).lo) (hl : 0 < (ellB q).lo)
    (hp : 0 < (poleF q A b u).lo) (he : 0 < (edenF q A).lo) (hu : 0 < u.lo) :
    SMem P.G (GF q A b u) := by
  simpa only [Point.G, GF, Int.cast_zero] using mem_fadd
    (mem_fsub (mem_fadd (mem_fdiv (mem_fmul (mem_fmax (mem_fint 0)
      (mem_fsub (mem_fmul c.hb c.params.ell) c.params.g)) c.eta) (c.pole hs hl) hp)
      (mem_fmul c.params.ell (mem_fadd (mem_fsub (c.RC hl) c.hA) c.hb))) c.params.g)
    (c.E he hu)

end Enclosures

section LeafTests

variable {P : Point} {q A b u : FI}

private theorem necFail_false (c : Ctx P q A b u) (hl : 0 < (ellB q).lo)
    (hs : 0 < (sdenF q).lo) : necFail q A b u ≠ true := by
  intro hf
  obtain ⟨nAy, _, nbr, _, nRP, nur, _, neta, nRC, nsc, nC, nQ, nlp0, nv, nlp1, njoint⟩ := c.nec
  simp only [necFail, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h | h | ⟨hv, h⟩ | ⟨hv, h⟩
  · have := (mem_fsub c.params.y c.hA).neg_of_hi h
    linarith
  · have := c.eta.neg_of_hi h
    linarith
  · have := (mem_fsub c.r0 c.hb).neg_of_hi h
    linarith
  · have := (mem_fsub c.r0 c.hu).neg_of_hi h
    linarith
  · have hh := (mem_fsub (mem_fnsmul 2 (mem_fmul c.params.ell c.hu))
      (c.params.RP c.hA c.box)).neg_of_hi h
    norm_num only [Nat.cast_ofNat] at hh
    nlinarith
  · have := (c.RC hl).neg_of_hi h
    linarith
  · have := (c.sc hs).neg_of_hi h
    linarith
  · have := (c.C hs).neg_of_hi h
    linarith
  · have := (c.Q hs).neg_of_hi h
    linarith
  · have := (c.lp0 hs).neg_of_hi h
    linarith
  · have := c.v.nonpos_of_hi h
    linarith
  · have := (mem_fsub c.p (c.lpf hs hv)).neg_of_hi h
    linarith
  · have hh : (0 : ℝ) < jointLo q A b u := by exact_mod_cast h
    have hj := c.joint_lower hs hv
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg njoint S_posR.le
    linarith

private theorem priceOK_sound (c : Ctx P q A b u) (hl : 0 < (ellB q).lo)
    (hs : 0 < (sdenF q).lo) (h : priceOK q A b u = true) : P.PriceTests := by
  simp only [priceOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hp, hu, hRP, he, hA, hm, hz, hE, hG⟩ := h
  exact ⟨(c.pole hs hl).pos_of_lo hp, c.hu.pos_of_lo hu,
    (c.params.RP c.hA c.box).pos_of_lo hRP, (c.moment hA hl).pos_of_lo hm,
    (c.zeroprice hA hl).pos_of_lo hz,
    (mem_fsub c.params.g (c.E he hu)).pos_of_lo hE, (c.G hs hl hp he hu).neg_of_hi hG⟩

private theorem tests_sound (c : Ctx P q A b u) (h : tests q A b u = true) :
    P.PriceTests := by
  simp only [tests, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hs⟩, hf | hp⟩ := h
  · exact False.elim (necFail_false c hl hs hf)
  · exact priceOK_sound c hl hs hp

private theorem empty_false {x : ℝ} {a : FI} (hx : SMem x a) : empty a ≠ true := by
  intro h
  exact not_lt.mpr hx.le (of_decide_eq_true h)

end LeafTests

private theorem cA_hi_le (q A b : FI) : (cA q A b).hi ≤ A.hi :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

private theorem contracted_context {P : Point} {q A b u : FI} (c : Ctx P q A b u)
    (hl : 0 < (ellB q).lo) :
    Ctx P q (cA q A b) (cb q (cA q A b) b) (cu q (cA q A b) u) := by
  have hA := cA_sound c.nec c.hA c.hb c.params.y
  have hb := cb_sound c.nec hA c.hb c.params.K
  have hu := cu_sound c.nec hA c.hu c.params.ell c.params.g (c.params.RP hA c.box) hl
  refine ⟨c.params, hA, hb, hu, c.box, c.nec, c.Alo, ?_⟩
  exact (div_le_div_of_nonneg_right (by exact_mod_cast cA_hi_le q A b) S_posR.le).trans c.Ahi

private theorem leafAfter_sound {P : Point} {q A b u : FI} (c : Ctx P q A b u)
    (hl : 0 < (ellB q).lo) (h : leafAfter q A b u = true) : P.PriceTests := by
  let A1 := cA q A b
  let b1 := cb q A1 b
  let u1 := cu q A1 u
  let A2 := cA q A1 b1
  let b2 := cb q A2 b1
  let u2 := cu q A2 u1
  have c1 : Ctx P q A1 b1 u1 := contracted_context c hl
  have c2 : Ctx P q A2 b2 u2 := contracted_context c1 hl
  change empty A1 || empty b1 || empty u1 || empty A2 || empty b2 || empty u2 ||
    tests q A2 b2 u2 = true at h
  simp only [Bool.or_eq_true, or_assoc] at h
  rcases h with h | h | h | h | h | h | h
  · exact False.elim (empty_false c1.hA h)
  · exact False.elim (empty_false c1.hb h)
  · exact False.elim (empty_false c1.hu h)
  · exact False.elim (empty_false c2.hA h)
  · exact False.elim (empty_false c2.hb h)
  · exact False.elim (empty_false c2.hu h)
  · exact tests_sound c2 h

private theorem initial_context {P : Point} {B : IBox} (hB : B.Valid)
    (hin : B.Contains P) (hP : P.InBox) (hN : P.Necessary)
    (hlo : atOK B.qI.lo = true) (hhi : atOK B.qI.hi = true) :
    Ctx P B.qI B.AI B.bI B.uI := by
  obtain ⟨hqlo, hqhi, hAlo, hAhi, _⟩ := B.endpoint_bounds hB
  have hq0 : 157 / 1000 ≤ val B.qI.lo := by
    calc
      157 / 1000 = val qOff := by norm_num [val, qOff, S]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hqlo) S_posR.le
  have hq1 : val B.qI.hi ≤ 1 / 5 := by
    calc
      _ ≤ val (qOff + qW) := div_le_div_of_nonneg_right (by exact_mod_cast hqhi) S_posR.le
      _ = _ := by norm_num [val, qOff, qW, S]
  have hqmem := mem_bounds hin.1
  refine ⟨⟨hin.1, ⟨hq0, hqmem.1.trans (hqmem.2.trans hq1)⟩,
    ⟨(hq0.trans hqmem.1).trans hqmem.2, hq1⟩, hlo, hhi⟩,
    hin.2.1, hin.2.2.1, hin.2.2.2, hP, hN, ?_, ?_⟩
  · exact div_nonneg (by exact_mod_cast hAlo) S_posR.le
  · calc
      _ ≤ val (aOff + aW) := div_le_div_of_nonneg_right (by exact_mod_cast hAhi) S_posR.le
      _ = _ := by norm_num [val, aOff, aW, S]

/-- A successful integer leaf either contradicts an original necessary
inequality or verifies all strict price tests. Contraction preserves the
same Point and both fixed-point division guards are checked. -/
theorem leafOK_sound {P : Point} {B : IBox} (hB : B.Valid) (hin : B.Contains P)
    (hP : P.InBox) (hN : P.Necessary) (h : leafOK B = true) : P.PriceTests := by
  simp only [leafOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hlo, hhi, hl, ht⟩ := h
  exact leafAfter_sound (initial_context hB hin hP hN hlo hhi) hl ht

/-- Soundness of the structural dyadic cover, including every shared
boundary point. No numerical evaluation is part of this theorem. -/
theorem cover_sound {P : Point} (hP : P.InBox) (hN : P.Necessary) :
    ∀ (n : ℕ) (B : IBox), B.Valid → B.Contains P → cover n B = true → P.PriceTests := by
  intro n
  induction n with
  | zero =>
    intro B hB hin h
    exact leafOK_sound hB hin hP hN h
  | succ n ih =>
    intro B hB hin h
    simp only [cover, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact leafOK_sound hB hin hP hN h
    · rcases B.split_cover hin with hleft | hright
      · exact ih _ (B.valid_split hB).1 hleft h1
      · exact ih _ (B.valid_split hB).2 hright h2

/-- The fast fixed-point certificate entails `PriceTests`, the original price tests.
The closed Boolean computation remains an explicit numerical proof premise. -/
theorem priceTests_of_cover (hcover : cover 80 IBox.root = true) {P : Point}
    (hP : P.InBox) (hN : P.Necessary) : P.PriceTests :=
  cover_sound hP hN 80 IBox.root IBox.root_valid (IBox.root_contains hP) hcover

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
