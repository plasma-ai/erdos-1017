module

public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSchurData
public import Erdos1017.SelectedModel.Structure.DegreeStraddle
public import Mathlib.Tactic.FieldSimp

/-!
# Necessary covariance inequality for a private set

Original whole-atom rows and a positive measurable private set force the strict
covariance inequality through one degree-zero tangent
(`private_covariance_necessary`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Classical RealInnerProductSpace

namespace Erdos1017.CappedModel.SelectedHighLowStructure

private theorem covariance_scalar {A k D ν DK E Q : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hD : 0 < D) (hν : 0 < ν)
    (hDK : 0 < DK) (hDKbound : DK ≤ k * (A + k))
    (hE : k < E) (hQ : 0 ≤ Q)
    (hneg : Q + 2 * (DK / (A * k)) * A * E - 4 * ν * (DK / D) ^ 2 ≤ 0) :
    D ^ 2 < 2 * ν * k * (A + k) := by
  have hstep : (DK / (A * k)) * A * E ≤ 2 * ν * (DK / D) ^ 2 := by
    linarith
  have heqL : (DK / (A * k)) * A * E = (DK / k) * E := by
    field_simp
  have heqR : 2 * ν * (DK / D) ^ 2 =
      (DK / k) * (2 * ν * k * DK / D ^ 2) := by
    field_simp
  rw [heqL, heqR] at hstep
  have hbound : E ≤ 2 * ν * k * DK / D ^ 2 :=
    le_of_mul_le_mul_left hstep (div_pos hDK hk)
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hupper : 2 * ν * k * DK / D ^ 2 ≤
      2 * ν * k * (k * (A + k)) / D ^ 2 := by
    gcongr
  have hstrict : k < 2 * ν * k * (k * (A + k)) / D ^ 2 :=
    hE.trans_le (hbound.trans hupper)
  have hdiv : 1 < 2 * ν * k * (A + k) / D ^ 2 := by
    have heq : 2 * ν * k * (k * (A + k)) / D ^ 2 =
        k * (2 * ν * k * (A + k) / D ^ 2) := by ring
    rw [heq] at hstrict
    exact lt_of_mul_lt_mul_left (by simpa only [mul_one] using hstrict) hk.le
  exact (one_lt_div hD2).mp hdiv

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- Actual original whole-atom rows and a positive measurable private set
force the strict covariance inequality through one degree-zero tangent. -/
theorem private_covariance_necessary
    (S : SelectedHighLowStructure W m) (i p : S.I)
    (K : Set Ω) (hK : MeasurableSet K)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hPI : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, (p.val : Ω → ℝ) x = 0)
    (hPK : ∀ᵐ x ∂μ.restrict K, (p.val : Ω → ℝ) x = 0)
    (hk : 0 < μ K) (D DK : ℝ)
    (hD : D = ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      Lp.const 2 μ (1 : ℝ) - S.normalizedHead p⟫)
    (hDpos : 0 < D)
    (hDI : ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      S.normalizedHead i - S.normalizedHead p⟫ = μ.real K)
    (hDK : DK = μ.real K * ⟪adjacencyOperator W (Lp.const 2 μ (1 : ℝ)),
      KernelOperator.normalizedSetL2 K hK - S.normalizedHead p⟫)
    (hDKpos : 0 < DK)
    (hDKupper : DK ≤ μ.real K * (μ.real {x | S.ρ x = i.val} + μ.real K))
    (hE : μ.real K < ∫ z in K, (i.val : Ω → ℝ) z ∂μ) :
    D ^ 2 < 2 * (2 * (c - m * d)) * μ.real K *
      (μ.real {x | S.ρ x = i.val} + μ.real K) := by
  let I := {x | S.ρ x = i.val}
  let A := μ.real I
  let k := μ.real K
  let a := S.normalizedHead i
  let b := S.normalizedHead p
  let z := KernelOperator.normalizedSetL2 (μ := μ) K hK
  let e := Lp.const 2 μ (1 : ℝ)
  let g := adjacencyOperator W e
  let B := schurForm W m
  let ν := 2 * (c - m * d)
  let f := b - e
  let wI := A • (b - a)
  let wK := k • (b - z)
  have hI : MeasurableSet I := (S.hfibers i.val i.property).1
  have hA : 0 < A := ENNReal.toReal_pos (S.hfibers i.val i.property).2.1.ne' (measure_ne_top μ I)
  have hk' : 0 < k := ENNReal.toReal_pos hk.ne' (measure_ne_top μ K)
  have hν : 0 < ν := (hW.strict_gap_structure hd hgap).stationary_pos
  have haa : B a a = 0 := S.schurForm_head_self i
  have hbb : B b b = 0 := S.schurForm_head_self p
  have hsym (x y : Lp ℝ 2 μ) : B x y = B y x := schurForm_symm x y
  have hbe : B e b = ν := S.schurForm_constant_head p hW
  have hee : B e e = ν := schurForm_constant_self hW
  have hba : B b a = 0 := by
    change ⟪shiftedOperator W m b, a⟫ = 0
    rw [S.operator_normalizedHead p, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant I hI
      (S.hfibers i.val i.property).2.1 p.val 0 hPI
  have hbz : B b z = 0 := by
    change ⟪shiftedOperator W m b, z⟫ = 0
    rw [S.operator_normalizedHead p, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner_of_constant K hK hk p.val 0 hPK
  have haz : B a z = k⁻¹ * (∫ x in K, (i.val : Ω → ℝ) x ∂μ) := by
    change ⟪shiftedOperator W m a, z⟫ = _
    rw [S.operator_normalizedHead i, real_inner_comm]
    exact KernelOperator.normalizedSetL2_inner K hK i.val
  have hzz : 0 ≤ B z z := by
    change 0 ≤ B ((μ.real K)⁻¹ • indicatorVector K hK)
      ((μ.real K)⁻¹ • indicatorVector K hK)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (mul_nonneg (inv_nonneg.mpr measureReal_nonneg)
        (schurForm_indicator_nonnegative K hK hW))
  have heb : B b e = ν := (hsym b e).trans hbe
  have hea : B e a = ν := S.schurForm_constant_head i hW
  have hae : B a e = ν := (hsym a e).trans hea
  have hez : B e z = ν := by
    rw [schurForm_constant hW, KernelOperator.normalizedSetL2_integral K hK hk]
    ring
  have hab : B a b = 0 := (hsym a b).trans hba
  have hzb : B z b = 0 := (hsym z b).trans hbz
  have hff : B f f = -ν := by
    simp only [f, map_sub, LinearMap.sub_apply]
    rw [hbb, heb, hbe, hee]
    ring
  have hfwI : B f wI = 0 := by
    simp only [f, wI, map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
    rw [hbb, hba, hbe, hea]
    ring
  have hfwK : B f wK = 0 := by
    simp only [f, wK, map_sub, map_smul, LinearMap.sub_apply, smul_eq_mul]
    rw [hbb, hbz, hbe, hez]
    ring
  have hwIwI : B wI wI = 0 := by
    simp only [wI, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbb, hba, hab, haa]
    ring
  have hwIwK : B wI wK = A * (∫ x in K, (i.val : Ω → ℝ) x ∂μ) := by
    simp only [wI, wK, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbb, hbz, hab, haz]
    field_simp [ne_of_gt hk']
    ring
  have hwKwK : B wK wK = k ^ 2 * B z z := by
    simp only [wK, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbb, hbz, hzb]
    ring
  have heA : ⟪e, a⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral I hI (S.hfibers i.val i.property).2.1
  have heB : ⟪e, b⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral _ _ (S.hfibers p.val p.property).2.1
  have heZ : ⟪e, z⟫ = 1 := by
    rw [KernelOperator.inner_constant_one]
    exact KernelOperator.normalizedSetL2_integral K hK hk
  have heeInner : ⟪e, e⟫ = 1 := by
    change ⟪Lp.const 2 μ (1 : ℝ), Lp.const 2 μ (1 : ℝ)⟫ = 1
    rw [real_inner_self_eq_norm_sq, KernelOperator.constant_one_norm]
    norm_num
  have hfbound : f ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      (KernelOperator.normalizedSetL2_bounded _ _)
      Variation.constant_one_bounded
  have hwIbound : wI ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).smul_mem A
      ((KernelOperator.boundedL2Submodule μ).sub_mem
        (KernelOperator.normalizedSetL2_bounded _ _)
        (KernelOperator.normalizedSetL2_bounded _ _))
  have hwKbound : wK ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).smul_mem k
      ((KernelOperator.boundedL2Submodule μ).sub_mem
        (KernelOperator.normalizedSetL2_bounded _ _)
        (KernelOperator.normalizedSetL2_bounded _ _))
  let t := DK / (A * k)
  let ucoef := 2 * DK / D
  let v := wK + t • wI - ucoef • f
  have ht : t * (A * k) = DK := by
    dsimp [t]
    field_simp [ne_of_gt hA, ne_of_gt hk']
  have hu : ucoef * D = 2 * DK := by
    dsimp [ucoef]
    field_simp [ne_of_gt hDpos]
  have hvmean : (∫ x, v x ∂μ) = 0 := by
    rw [← KernelOperator.inner_constant_one]
    simp only [v, wK, wI, f, inner_sub_right, inner_add_right,
      real_inner_smul_right]
    rw [heA, heB, heZ, heeInner]
    ring
  have hvbound : v ∈ KernelOperator.boundedL2Submodule μ :=
    (KernelOperator.boundedL2Submodule μ).sub_mem
      ((KernelOperator.boundedL2Submodule μ).add_mem hwKbound
        ((KernelOperator.boundedL2Submodule μ).smul_mem t hwIbound))
      ((KernelOperator.boundedL2Submodule μ).smul_mem ucoef hfbound)
  have hvdegree : ⟪g, v⟫ = 0 := by
    simp only [v, wK, wI, f, inner_sub_right, inner_add_right,
      real_inner_smul_right]
    have hD' := hD
    have hDI' := hDI
    have hDK' := hDK
    change D = ⟪g, e - b⟫ at hD'
    change ⟪g, a - b⟫ = k at hDI'
    change DK = k * ⟪g, z - b⟫ at hDK'
    rw [inner_sub_right] at hD' hDI' hDK'
    have h0 : k * (⟪g, b⟫ - ⟪g, z⟫) = -DK := by linarith only [hDK']
    have h1 : A * (⟪g, b⟫ - ⟪g, a⟫) = -(A * k) := by
      calc
        _ = -(A * (⟪g, a⟫ - ⟪g, b⟫)) := by ring
        _ = _ := by rw [hDI']
    have h2 : ⟪g, b⟫ - ⟪g, e⟫ = -D := by linarith only [hD']
    rw [h0, h1, h2]
    linarith only [ht, hu]
  have hQ : B v v ≤ 0 :=
    hW.bounded_tangent_nonpositive (hW.strict_gap_structure hd hgap).regular
      v hvbound hvmean hvdegree
  have hwKwI : B wK wI = B wI wK := hsym wK wI
  have hwIf : B wI f = 0 := (hsym wI f).trans hfwI
  have hwKf : B wK f = 0 := (hsym wK f).trans hfwK
  have hQexp : B v v = k ^ 2 * B z z +
      2 * t * A * (∫ x in K, (i.val : Ω → ℝ) x ∂μ) - ucoef ^ 2 * ν := by
    simp only [v, map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hwKwK, hwIwK, hwKwI, hwIwI, hfwI, hfwK, hwIf, hwKf, hff, hwIwK]
    ring
  have hQ0 : 0 ≤ k ^ 2 * B z z := mul_nonneg (sq_nonneg _) hzz
  have hneg : k ^ 2 * B z z +
      2 * (DK / (A * k)) * A * (∫ x in K, (i.val : Ω → ℝ) x ∂μ) -
        4 * ν * (DK / D) ^ 2 ≤ 0 := by
    calc
      _ = B v v := by
        rw [hQexp]
        dsimp only [t, ucoef]
        ring
      _ ≤ 0 := hQ
  have hscalar := covariance_scalar hA hk' hDpos hν hDKpos
    (show DK ≤ k * (A + k) from hDKupper) hE hQ0 hneg
  simpa only [A, k, ν, I] using hscalar

end Erdos1017.CappedModel.SelectedHighLowStructure
