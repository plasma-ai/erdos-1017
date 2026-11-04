module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalParams

/-!
# Contract of the large-atom certificate

This module defines the structure `Point` of relaxed real quantities at a point
`(q,A,b,u)`, derived quantities such as `theta`, the error `E` and the signed
price `G`, the box `InBox`, the `Necessary` inequalities and the seven strict
inequalities `PriceTests`. It states what the certificate establishes for the
middle `E₂` exclusion.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MiddleE2LargeUniversal

/-- The relaxed real quantities of the large-atom certificate at one point
`(q,A,b,u)`. Every quantity is a fixed explicit function of the point. -/
structure Point where
  q : ℝ
  A : ℝ
  b : ℝ
  u : ℝ

namespace Point

variable (P : Point)

def ell : ℝ := ellq P.q
def de : ℝ := deq P.q
def g : ℝ := gq P.q
def h : ℝ := hq P.q
def y : ℝ := yq P.q
def K : ℝ := kq P.q

/-- `eta=1-A-b-u`. -/
def eta : ℝ := 1 - P.A - P.b - P.u

/-- `r_0=1-2A`. -/
def r0 : ℝ := 1 - 2 * P.A

/-- `R_{P,0}=ell+g_q-(1+ell)A`. -/
def RP : ℝ := P.ell * (1 - P.A) - P.A + P.g

/-- The relaxed bad-row cap `\widehat R`. -/
def RC : ℝ := min (1 - 3 * P.A + P.b) ((1 - P.u - 2 * P.ell * P.A - 3 * P.g) / P.ell)

/-- The lower-count selector radicand `(D_2(A)-g_q)/(1/5-delta)`. -/
def sc : ℝ := ((-1 + 6 * P.A - (8 - 3 * P.de) * P.A ^ 2) / 3 - P.g) / (1 / 5 - P.de)

/-- The relaxed closed-missing-mass cap `\widehat T`. -/
def T : ℝ := Real.sqrt P.sc

/-- The relaxed atom cap `C`. -/
def C : ℝ := min (min (P.r0 - P.b) (P.A - P.b - P.K)) (P.T - P.b)

/-- The missing-square budget `Q`. -/
def Q : ℝ := min (min (P.C * P.eta) (P.eta ^ 2)) (P.h - P.A ^ 2 - P.b ^ 2 - 2 * P.b * P.eta)

/-- The deficit upper bound `p=r_q^*-u`. -/
def p : ℝ := P.y - P.u

/-- `v_0=1-2h_q-u`. -/
def v : ℝ := 1 - 2 * P.h - P.u

/-- `gap=eta-C`, in its cancelled form. -/
def gap : ℝ := max (max (P.A - P.u) (1 - 2 * P.A - P.u + P.K)) (1 - P.A - P.u - P.T)

/-- The tangent floor `t_0=(eta-C)_+/(3v_0)`. -/
def t0 : ℝ := max 0 P.gap / (3 * P.v)

/-- The refined deficit floor. -/
def lpf : ℝ := min (P.eta / 2) (P.gap + (P.eta - 2 * P.gap) * min (1 / 2) P.t0)

/-- `eta-2C`. -/
def den : ℝ := 2 * P.gap - P.eta

/-- `eta-C-p`, in its cancelled form. -/
def dgap : ℝ := max (max (P.A - P.y) (1 - 2 * P.A - P.y + P.K)) (1 - P.A - P.T - P.y)

/-- The integrated atomic floor `t_*`. -/
def tf : ℝ := if 0 < P.den then max P.t0 (max 0 (P.dgap / P.den)) else P.t0

/-- The joint deficit expression `w^2-xp-(1-2t_*)_+Q`. -/
def joint : ℝ :=
  (1 - P.A - P.b - P.y) ^ 2 - (P.y - P.A) * P.p - max 0 (1 - 2 * P.tf) * P.Q

/-- The certified lower bound for the pole `A-\widehat R-C`. -/
def pole : ℝ :=
  max (max (3 * P.A + P.b - 1 - P.RC) (P.b + P.K - P.RC))
    (max (P.A + P.b - P.T - P.RC) (6 * P.A - 2))

/-- `theta_0=3g_q/A-delta`. -/
def theta : ℝ := 3 * P.g / P.A - P.de

/-- The moment license. -/
def moment : ℝ := P.theta * (P.A - P.RC) - P.de * P.p

/-- The zero-price license. -/
def zeroprice : ℝ := P.g - max 0 (1 - 2 * P.theta) * P.RC

/-- The additional-hole error `E_0`. -/
def E : ℝ :=
  max 0 (P.A - 3 * P.g) / ((2 * P.ell - 1) * P.A + 3 * P.g) * (P.r0 - P.u) *
    max 0 (2 * P.ell - P.RP / P.u)

/-- The final necessary signed price `\mathcal G_0`. -/
def G : ℝ :=
  max 0 (P.b * P.ell - P.g) * P.eta / P.pole + P.ell * (P.RC - P.A + P.b) - P.g + P.E

/-- The initial closed four-box. -/
def InBox : Prop :=
  157 / 1000 ≤ P.q ∧ P.q ≤ 1 / 5 ∧ 1 / 3 ≤ P.A ∧ P.A ≤ 369 / 1000 ∧
    0 ≤ P.b ∧ P.b ≤ 1 / 3 ∧ 0 ≤ P.u ∧ P.u ≤ 1 / 3

/-- Every necessary mass, row, cap, missing-square and deficit inequality
of the large-atom certificate, at the exact point. -/
def Necessary : Prop :=
  P.A ≤ P.y ∧ 3 * P.A - 1 ≤ P.b ∧ P.b ≤ P.r0 ∧ P.b ≤ P.A - P.K ∧
    P.RP ≤ 2 * P.ell * P.u ∧ P.u ≤ P.r0 ∧ P.u ≤ 1 - 2 * P.ell * P.A - 3 * P.g ∧
    0 ≤ P.eta ∧ 0 ≤ P.RC ∧ 0 ≤ P.sc ∧ 0 ≤ P.C ∧ 0 ≤ P.Q ∧
    min (P.eta / 2) (P.eta - P.C) ≤ P.p ∧ 0 < P.v ∧ P.lpf ≤ P.p ∧ P.joint ≤ 0

/-- Seven strict inequalities: the five price tests `0 < RP` (`R_{P,0}`),
`0 < moment`, `0 < zeroprice`, `0 < g - E` and `G < 0`, and the positive
denominators `0 < pole` and `0 < u`. -/
def PriceTests : Prop :=
  0 < P.pole ∧ 0 < P.u ∧ 0 < P.RP ∧ 0 < P.moment ∧ 0 < P.zeroprice ∧
    0 < P.g - P.E ∧ P.G < 0

end Point

end Erdos1017.MiddleE2LargeUniversal
