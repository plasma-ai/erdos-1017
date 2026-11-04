module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateChecker
public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalContract

/-!
# Soundness of the contraction steps

Each contraction of the common-peak coordinate, its partner and the
common-neighborhood coordinate (`cA_sound`, `cb_sound`, `cu_sound`) follows from
the necessary system and the supplied parameter enclosure, with the division
licensed by the positive multiplier enclosure.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

private theorem mem_narrowHi {x y : ℝ} {a c : FI}
    (hx : SMem x a) (hy : SMem y c) (hxy : x ≤ y) :
    SMem x (narrowHi a c) := by
  refine ⟨hx.1, ?_⟩
  change x * S ≤ ((min a.hi c.hi : ℤ) : ℝ)
  rw [Int.cast_min]
  exact le_min hx.2 ((mul_le_mul_of_nonneg_right hxy S_posR.le).trans hy.2)

private theorem mem_narrowLo {x y : ℝ} {a c : FI}
    (hx : SMem x a) (hy : SMem y c) (hyx : y ≤ x) :
    SMem x (narrowLo a c) := by
  refine ⟨?_, hx.2⟩
  change ((max a.lo c.lo : ℤ) : ℝ) ≤ x * S
  rw [Int.cast_max]
  exact max_le hx.1 (hy.1.trans (mul_le_mul_of_nonneg_right hyx S_posR.le))

/-- Every upper contraction of the common-peak coordinate follows from
the same necessary system and the supplied actual parameter enclosure. -/
theorem cA_sound {P : Point} {q A b : FI} (hN : P.Necessary)
    (hA : SMem P.A A) (hb : SMem P.b b) (hy : SMem P.y (yB q)) :
    SMem P.A (cA q A b) := by
  have h1 := mem_narrowHi hA hy hN.1
  have h3 := mem_fdivn 3 (by decide) (mem_fadd (mem_fint 1) hb)
  norm_num only [Int.cast_one, Nat.cast_ofNat] at h3
  have h2 := mem_narrowHi h1 h3 (show P.A ≤ (1 + P.b) / 3 by linarith [hN.2.1])
  have hdiv2 := mem_fdivn 2 (by decide) (mem_fsub (mem_fint 1) hb)
  exact mem_narrowHi h2 hdiv2 (by have := hN.2.2.1; unfold Point.r0 at this; linarith)

/-- The partner contraction keeps its original necessary lower bound and
both upper bounds, including the actual gap parameter. -/
theorem cb_sound {P : Point} {q A b : FI} (hN : P.Necessary)
    (hA : SMem P.A A) (hb : SMem P.b b) (hK : SMem P.K (KB q)) :
    SMem P.b (cb q A b) := by
  have hlo := mem_fsub (mem_fnsmul 3 hA) (mem_fint 1)
  have h1 := mem_narrowLo hb hlo (by simpa using hN.2.1)
  have hhi := mem_fsub (mem_fint 1) (mem_fnsmul 2 hA)
  have h2 := mem_narrowHi h1 hhi (by simpa [Point.r0] using hN.2.2.1)
  exact mem_narrowHi h2 (mem_fsub hA hK) hN.2.2.2.1

/-- The common-neighborhood contraction uses the actual row price at the
passed peak interval. Its division is licensed by the positive multiplier
enclosure; no parameter monotonicity or box domain is assumed here. -/
theorem cu_sound {P : Point} {q A u : FI} (hN : P.Necessary)
    (hA : SMem P.A A) (hu : SMem P.u u) (hl : SMem P.ell (ellB q))
    (hg : SMem P.g (gB q)) (hRP : SMem P.RP (RPB q A))
    (hell : 0 < (ellB q).lo) : SMem P.u (cu q A u) := by
  have hellR : 0 < P.ell := hl.pos_of_lo hell
  have hden : 0 < (fnsmul 2 (ellB q)).lo := by
    change 0 < (2 : ℤ) * (ellB q).lo
    positivity
  have hrow := mem_fdiv hRP (mem_fnsmul 2 hl) hden
  have h1 := mem_narrowLo hu hrow (by
    apply (div_le_iff₀ (show 0 < 2 * P.ell by positivity)).mpr
    nlinarith only [hN.2.2.2.2.1])
  have hhi := mem_fsub (mem_fint 1) (mem_fnsmul 2 hA)
  have h2 := mem_narrowHi h1 hhi (by simpa [Point.r0] using hN.2.2.2.2.2.1)
  have hlast := mem_fsub (mem_fsub (mem_fint 1) (mem_fnsmul 2 (mem_fmul hl hA)))
    (mem_fnsmul 3 hg)
  exact mem_narrowHi h2 hlast (by simpa only [Nat.cast_ofNat, Int.cast_one, mul_assoc]
    using hN.2.2.2.2.2.2.1)

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
