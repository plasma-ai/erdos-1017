module

public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateStars
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2PrivateCovariance
public import Erdos1017.Exclusions.E2.Middle.SelectedMiddleE2Scalar
public import Erdos1017.Exclusions.Common.E2.FullE2ContactCurvature
public import Erdos1017.Exclusions.Common.E2.E2PrivateCurvatureCertificates
public import Erdos1017.Exclusions.Common.Private.SelectedPrivateBodyTrace
public import Erdos1017.Exclusions.Common.Private.SelectedPrivatePhysicalPrimal
public import Erdos1017.Exclusions.E2.Upper.SelectedE2AtomGuards
public import Erdos1017.SelectedModel.OriginalAtomicSquareReserve
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterSharedMass

/-!
# Exclusion of the large private sector

Scalar margins at a middle `E₂` contact (missing mass below `29/100`, trace,
inventory, two-neighbor and row margins) combine in a Schur comparison to show
that a common original peak missing exactly one whole atom satisfies
`3A + b ≤ 1` (`private_peak_large_sector`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Classical

namespace Erdos1017.MiddleE2PrivateScalar

open LowerE2Scalar

private theorem middle_facts {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    0 < q ∧ 0 < denominator q ∧ 0 < 2 + q :=
  ⟨by linarith [hq.1], denominator_pos (by linarith [hq.1]), by linarith [hq.1]⟩

/-- The middle-E2 missing mass is below `29/100`. -/
theorem missingMass_lt {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    missingMass q < 29 / 100 := by
  obtain ⟨hq0, hR, _⟩ := middle_facts hq
  have h2 : (1 / 10 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) hq.1.le 2
  have h3 : q ^ 3 ≤ q ^ 2 / 5 := by nlinarith [sq_nonneg q, hq.2]
  have h4 : q ^ 4 ≤ q ^ 2 / 25 := by nlinarith [sq_nonneg q, hq.2, h3]
  have hid : 232 * denominator q ^ 2 - 100 * ((q + 2) ^ 2 * (1 + 4 * q + 13 * q ^ 2)) =
      -168 + 1248 * q + 4932 * q ^ 2 - 2352 * q ^ 3 - 1068 * q ^ 4 := by
    unfold denominator
    ring
  unfold missingMass
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hq.1]

/-- The trace-side margin `8 δ² h < 27 g²`. -/
theorem trace_margin {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    8 * (1 - multiplier q) ^ 2 * missingMass q < 27 * gapFloor q ^ 2 := by
  obtain ⟨hq0, hR, hq2⟩ := middle_facts hq
  have hRne := hR.ne'
  have hq2ne := hq2.ne'
  have hid : 27 * gapFloor q ^ 2 - 8 * (1 - multiplier q) ^ 2 * missingMass q =
      q ^ 2 * (11 + 44 * q - 100 * q ^ 2) / (4 * denominator q ^ 2) := by
    unfold gapFloor multiplier missingMass
    field_simp
    ring
  have hpoly : 0 < 11 + 44 * q - 100 * q ^ 2 := by nlinarith [hq.2]
  have hpos : 0 < q ^ 2 * (11 + 44 * q - 100 * q ^ 2) / (4 * denominator q ^ 2) := by
    positivity
  linarith

/-- The inventory-side margin `4 δ² h < (3 + 2δ)² g²`. -/
theorem inventory_margin {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    4 * (1 - multiplier q) ^ 2 * missingMass q <
      (3 + 2 * (1 - multiplier q)) ^ 2 * gapFloor q ^ 2 := by
  obtain ⟨hq0, hR, hq2⟩ := middle_facts hq
  have hRne := hR.ne'
  have hq2ne := hq2.ne'
  have hid : (3 + 2 * (1 - multiplier q)) ^ 2 * gapFloor q ^ 2 -
      4 * (1 - multiplier q) ^ 2 * missingMass q =
      q ^ 2 * (4 + 68 * q - 23 * q ^ 2 + 84 * q ^ 3 + 92 * q ^ 4) /
        (4 * denominator q ^ 2 * (2 + q) ^ 2) := by
    unfold gapFloor multiplier missingMass
    field_simp
    ring
  have hpoly : 0 < 4 + 68 * q - 23 * q ^ 2 + 84 * q ^ 3 + 92 * q ^ 4 := by
    nlinarith [hq.2, pow_pos hq0 3, pow_pos hq0 4]
  have hpos : 0 < q ^ 2 * (4 + 68 * q - 23 * q ^ 2 + 84 * q ^ 3 + 92 * q ^ 4) /
      (4 * denominator q ^ 2 * (2 + q) ^ 2) := by
    positivity
  linarith

/-- The two-neighbor margin `(9/10) δ < 3g`. -/
theorem NN_margin {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    9 / 10 * (1 - multiplier q) < 3 * gapFloor q := by
  obtain ⟨hq0, hR, hq2⟩ := middle_facts hq
  have hRne := hR.ne'
  have hq2ne := hq2.ne'
  have hid : 3 * gapFloor q - 9 / 10 * (1 - multiplier q) =
      q * (12 - 51 * q + 12 * q ^ 2) / (10 * denominator q * (2 + q)) := by
    unfold gapFloor multiplier denominator
    field_simp
    ring
  have hpoly : 0 < 12 - 51 * q + 12 * q ^ 2 := by nlinarith [hq.2]
  have hpos : 0 < q * (12 - 51 * q + 12 * q ^ 2) / (10 * denominator q * (2 + q)) := by
    positivity
  linarith

/-- The flat second-root row margin `(19/40)(1 + ℓ) < g + ℓ`. -/
theorem row_margin {q : ℝ} (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5)) :
    19 / 40 * (1 + multiplier q) < gapFloor q + multiplier q := by
  obtain ⟨hq0, hR, hq2⟩ := middle_facts hq
  have hRne := hR.ne'
  have hq2ne := hq2.ne'
  have hid : gapFloor q + multiplier q - 19 / 40 * (1 + multiplier q) =
      (1 + 7 * q - 44 * q ^ 2) / (10 * denominator q * (2 + q)) := by
    unfold gapFloor multiplier denominator
    field_simp
    ring
  have hpoly : 0 < 1 + 7 * q - 44 * q ^ 2 := by nlinarith [hq.2]
  have hpos : 0 < (1 + 7 * q - 44 * q ^ 2) / (10 * denominator q * (2 + q)) := by
    positivity
  linarith

/-- The final Schur comparison. The exposed hole `k < z - 1/3`, the flat
second-root row `ν ≤ 2(1 - z)` and `z ≤ 21/40`, `h < 29/100` and
`0 < C < 6` contradict `(z - h)^2 < ν (2k(A+k) - 1/C)`. -/
theorem sector_false {z h k A ν C : ℝ}
    (hz : z ≤ 21 / 40) (hh : h < 29 / 100) (hk : 0 ≤ k) (hk1 : k < z - 1 / 3)
    (hAk : A + k ≤ z) (hν0 : 0 ≤ ν) (hν : ν ≤ 2 * (1 - z))
    (hC : 0 < C) (hC6 : C < 6)
    (hcov : (z - h) ^ 2 < ν * (2 * k * (A + k) - 1 / C)) : False := by
  have hz3 : 1 / 3 < z := by linarith
  have hX : 2 * k * (A + k) ≤ 2 * z * (z - 1 / 3) := by
    have h1 := mul_le_mul_of_nonneg_left hAk hk
    have h2 := mul_le_mul_of_nonneg_right hk1.le (show 0 ≤ z by linarith)
    nlinarith
  have hinv : 1 / 6 < 1 / C := one_div_lt_one_div_of_lt hC hC6
  by_cases hpos : 2 * k * (A + k) - 1 / C ≤ 0
  · have := mul_nonpos_of_nonneg_of_nonpos hν0 hpos
    nlinarith [sq_nonneg (z - h)]
  · have hXpos : 0 < 2 * k * (A + k) - 1 / C := lt_of_not_ge hpos
    have hhalf : 1 / 2 < z := by nlinarith
    have hν1 : ν ≤ 1 := by linarith
    have hXup : 2 * k * (A + k) - 1 / C ≤ 83 / 2400 := by
      nlinarith
    have hνX : ν * (2 * k * (A + k) - 1 / C) ≤ 2 * k * (A + k) - 1 / C := by
      nlinarith
    have hD : (21 / 100 : ℝ) ^ 2 ≤ (z - h) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    norm_num at hD
    linarith

/-- The whole private-sector scalar argument on one original state. Every
input is an actual model fact: inventory, trace, curvature covariance
(conditional on the two triangle margins it derives), the flat second-root
row and the middle-E2 parameter guards. -/
theorem sector_contradiction {A b k h ell g γ ν m C : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hk : 0 < k) (hsector : 1 < 3 * A + b)
    (hm : m = -ell) (hl : ell ∈ Ioo (9 / 11 : ℝ) (19 / 21))
    (hγ : γ = ν + m) (hg : 0 < g) (hgγ : g < γ) (hν0 : 0 ≤ ν)
    (hh : h < 29 / 100) (hinv : (A + b) ^ 2 ≤ h)
    (htrace : b ≤ γ → 2 * (A + b) ^ 2 + (A + γ - b) ^ 2 + 4 * b * k ≤ 2 * h)
    (htm : 8 * (1 - ell) ^ 2 * h < 27 * g ^ 2)
    (hinm : 4 * (1 - ell) ^ 2 * h < (3 + 2 * (1 - ell)) ^ 2 * g ^ 2)
    (hNN : 9 / 10 * (1 - ell) < 3 * g) (hrm : 19 / 40 * (1 + ell) < g + ell)
    (hrow : ν ≤ (1 - m) * (1 - A - b - k))
    (hC : 0 < C) (hC6 : C < 6)
    (hcov : 2 * (1 + m) * A < 3 * γ → (1 + m) * (1 - A) < 3 * γ →
      (A + b + k - h) ^ 2 < ν * (2 * k * (A + k) - 1 / C)) : False := by
  subst hm hγ
  have hδ : 0 < 1 - ell := by linarith [hl.2]
  have hα : A + b < 54 / 100 := by
    by_contra hge
    have h2 := pow_le_pow_left₀ (by norm_num) (le_of_not_gt hge) 2
    norm_num at h2
    linarith
  have hδm : 1 + -ell = 1 - ell := by ring
  have hmargin : 2 * (1 + -ell) * A < 3 * (ν + -ell) := by
    rw [hδm]
    by_cases hbg : b ≤ ν + -ell
    · have ht := htrace hbg
      have e1 : A ^ 2 ≤ (A + b) ^ 2 := pow_le_pow_left₀ hA (by linarith) 2
      have e2 : A ^ 2 ≤ (A + (ν + -ell) - b) ^ 2 := pow_le_pow_left₀ hA (by linarith) 2
      have e3 : 0 ≤ 4 * b * k := by positivity
      have hA2 : 3 * A ^ 2 ≤ 2 * h := by linarith
      have h1 : (2 * (1 - ell) * A) ^ 2 ≤ 8 / 3 * (1 - ell) ^ 2 * h := by
        have := mul_le_mul_of_nonneg_left hA2 (sq_nonneg (1 - ell))
        have heq : (2 * (1 - ell) * A) ^ 2 = 4 / 3 * ((1 - ell) ^ 2 * (3 * A ^ 2)) := by
          ring
        rw [heq]
        linarith
      have h2 : (3 * g) ^ 2 < (3 * (ν + -ell)) ^ 2 :=
        pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
      have hsq : (2 * (1 - ell) * A) ^ 2 < (3 * (ν + -ell)) ^ 2 := by linarith
      exact lt_of_pow_lt_pow_left₀ 2 (by linarith) hsq
    · have hbg' : ν + -ell < b := lt_of_not_ge hbg
      by_contra hge
      have hge' : 3 * (ν + -ell) ≤ 2 * (1 - ell) * A := le_of_not_gt hge
      have hδb := mul_le_mul_of_nonneg_left hbg'.le (show 0 ≤ 2 * (1 - ell) by linarith)
      have hlin : (3 + 2 * (1 - ell)) * (ν + -ell) ≤ 2 * (1 - ell) * (A + b) := by
        linarith
      have hsq1 : ((3 + 2 * (1 - ell)) * (ν + -ell)) ^ 2 ≤
          (2 * (1 - ell) * (A + b)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hlin 2
      have hsq2 : ((3 + 2 * (1 - ell)) * g) ^ 2 <
          ((3 + 2 * (1 - ell)) * (ν + -ell)) ^ 2 :=
        pow_lt_pow_left₀ (mul_lt_mul_of_pos_left hgγ (by linarith))
          (mul_nonneg (by linarith) hg.le) (by norm_num)
      have h3 : (2 * (1 - ell) * (A + b)) ^ 2 ≤ 4 * (1 - ell) ^ 2 * h := by
        have := mul_le_mul_of_nonneg_left hinv (sq_nonneg (1 - ell))
        have heq : (2 * (1 - ell) * (A + b)) ^ 2 = 4 * ((1 - ell) ^ 2 * (A + b) ^ 2) := by
          ring
        rw [heq]
        linarith
      have heq2 : ((3 + 2 * (1 - ell)) * g) ^ 2 = (3 + 2 * (1 - ell)) ^ 2 * g ^ 2 := by
        ring
      linarith
  have hNNmargin : (1 + -ell) * (1 - A) < 3 * (ν + -ell) := by
    rw [hδm]
    have h1 := mul_le_mul_of_nonneg_left (show 1 - A ≤ 9 / 10 by linarith) hδ.le
    linarith
  have hc := hcov hmargin hNNmargin
  have h1m : 1 - -ell = 1 + ell := by ring
  rw [h1m] at hrow
  have hz : A + b + k ≤ 21 / 40 := by
    by_contra hz
    have h2 : (1 + ell) * (1 - A - b - k) ≤ (1 + ell) * (19 / 40) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith [hl.1])
    linarith
  have hνz : ν ≤ 2 * (1 - (A + b + k)) := by
    have hnn : 0 ≤ 1 - A - b - k := by linarith
    have h2 := mul_le_mul_of_nonneg_right (show 1 + ell ≤ 2 by linarith [hl.2]) hnn
    linarith
  exact sector_false hz hh hk.le (by linarith) (by linarith) hν0 hνz hC hC6 hc

end Erdos1017.MiddleE2PrivateScalar

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
private theorem sector_whole_row_le (S : SelectedHighLowStructure W m) (r : S.I)
    (hm : m ≤ 1) : ∀ᵐ x ∂μ, r.val x ≤ 1 - m := by
  let Ir : Set Ω := {x | S.ρ x = r.val}
  have hpair : ∀ᵐ p ∂μ.prod μ, p.1 ∈ Ir → r.val p.2 ≤ 1 - m := by
    filter_upwards [S.ae_kernel_eq_fiber_row r.val r.property] with p hp hIr
    exact (hp hIr) ▸ shiftedKernel_le_one_sub hm p
  obtain ⟨x, hx, hsection⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers r.val r.property).2.1.ne'
    (ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair))
  exact hsection.mono (fun _ hy => hy hx)

private theorem sector_stationary_row_le_neighborhood
    (S : SelectedHighLowStructure W m) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (r : S.I) :
    2 * (c - m * d) ≤ (1 - m) * μ.real (S.rootNeighborhood r) := by
  let N := S.rootNeighborhood r
  have hN := S.measurableSet_rootNeighborhood r
  have hf : Integrable (r.val : Ω → ℝ) μ := (Lp.memLp r.val).integrable (by norm_num)
  have hoff : (r.val : Ω → ℝ) =ᵐ[μ.restrict Nᶜ] fun _ => 0 := by
    filter_upwards [ae_restrict_mem hN.compl, ae_restrict_of_ae (S.ae_rootNeighborhood_iff r),
      ae_restrict_of_ae (S.ae_whole_row_nonneg r hW)] with x hx hiff hnonneg
    exact le_antisymm (le_of_not_gt (fun h => hx (hiff.mpr h))) hnonneg
  have hoffint : (∫ x in Nᶜ, (r.val : Ω → ℝ) x ∂μ) = 0 := integral_eq_zero_of_ae hoff
  have hNint : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) = 2 * (c - m * d) := by
    have hpart := integral_add_compl hN hf
    rw [hoffint, add_zero, S.row_integral_of_stationary r hW] at hpart
    exact hpart
  have hm : m ≤ 1 := le_of_lt (lt_trans
    (hW.strict_gap_structure hd hgap).multiplier_neg (by norm_num))
  have hbound : (∫ x in N, (r.val : Ω → ℝ) x ∂μ) ≤
      (∫ x in N, (1 - m : ℝ) ∂μ) :=
    integral_mono_ae hf.integrableOn (integrable_const (1 - m)).integrableOn
      (ae_restrict_of_ae (sector_whole_row_le S r hm))
  rw [hNint, setIntegral_const, smul_eq_mul] at hbound
  simpa only [N, mul_comm] using hbound

/-- A common original peak with one distinct whole private hole is HIGH:
a neutral peak would have the universal original row, contradicting the
missing second fiber. -/
private theorem sector_private_peak_high
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    ∀ᵐ x ∂μ.restrict {x | S.ρ x = i.val}, x ∈ S.H := by
  obtain ⟨hΔ, j, _, hside, hj, _, _, _⟩ :=
    S.exists_original_atomic_square_reserve hW hd hgap
  have heq : j = i := (hj S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2.unique
    (hpeak S.forwardFlow S.forwardFlow_isFullForwardFlow).2.2 hΔ
  subst j
  rcases hside with hH | hN
  · exact hH
  · let I := {x | S.ρ x = i.val}
    let P := {x | S.ρ x = p.val}
    have hI : MeasurableSet I := (S.hfibers i.val i.property).1
    have hP : MeasurableSet P := (S.hfibers p.val p.property).1
    have hprob : 0 < (μ.restrict I).prod (μ.restrict P) Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      have hi : 0 < μ I := (S.hfibers i.val i.property).2.1
      have hp : 0 < μ P := (S.hfibers p.val p.property).2.1
      simpa only [Measure.restrict_apply_univ, show (⊥ : ENNReal) = 0 from rfl] using
        (mul_ne_zero hi.ne' hp.ne').bot_lt
    have hneutral := S.neutral_atom_adjacency i hW hd hgap hN
    have hboth : ∀ᵐ z ∂(μ.restrict I).prod (μ.restrict P), False := by
      filter_upwards [ae_mono (Measure.prod_mono Measure.restrict_le_self
          Measure.restrict_le_self) hprivate,
        ae_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
          hneutral,
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hI),
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hP)] with z hp hn hi hj
      have hzero := hp hi
      have hone := hn hi
      have hpi : S.ρ z.2 = p.val := hj
      have hneq : S.ρ z.2 ≠ i.val := by
        intro he
        exact hip (Subtype.ext (he.symm.trans hpi))
      simp only [hpi, or_true, ite_true] at hzero
      simp only [hneq, ite_false] at hone
      exact zero_ne_one (hzero.symm.trans hone)
    have hzero : (μ.restrict I).prod (μ.restrict P) Set.univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using hboth
    exact False.elim ((ne_of_gt hprob) hzero)

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The large private sector at a middle-E2 contact. A common original peak
whose literal row misses exactly one distinct whole atom satisfies
`3A + b ≤ 1`. The HIGH location, trace and inventory margins, exposed
private hole, original curvature covariance, flat second-root row and
every parameter guard are derived from the same original model. -/
theorem private_peak_large_sector
    (S : SelectedHighLowStructure W m) (i p : S.I) (hip : i ≠ p)
    {d c q : ℝ} (hW : FullStationaryClass d c W m)
    (hq : q ∈ Ioo (1 / 10 : ℝ) (1 / 5))
    (hdq : d = (1 - LowerE2Scalar.missingMass q) / 2)
    (hvalue : benchmark d = Benchmark.twoHeadValue ((q + 2) / 3))
    (hderiv : HasDerivAt benchmark (-LowerE2Scalar.multiplier q) d)
    (hgap : benchmark d < c)
    (hglobal : ∀ (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Model Ω ν),
      FullFeasible V → objective V - benchmark (density V) ≤
        objective W - benchmark (density W))
    (hpeak : S.IsCommonForwardPeak d c i)
    (hprivate : ∀ᵐ z ∂μ.prod μ, S.ρ z.1 = i.val →
      adjacencyKernel W z.1 z.2 =
        if S.ρ z.2 = i.val ∨ S.ρ z.2 = p.val then 0 else 1) :
    3 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val} ≤ 1 := by
  have hq' : q ∈ Ioc (0 : ℝ) (2 / 9) := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hq5 : q ∈ Ioc (0 : ℝ) (1 / 5) := ⟨by linarith [hq.1], hq.2.le⟩
  have hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdq ▸ LowerE2Scalar.contact_density_mem hq'
  obtain ⟨hm, hell, hgamma⟩ :=
    hW.e2_general_contact_parameters hq' hdq hvalue hderiv hgap hglobal
  have hcurv := (hW.e2_contact_curvature hq5 hdq hgap hglobal).2
  have hCq := E2PrivateCurvature.curvature_pos_lt_six ⟨hq5.1.le, hq5.2⟩
  have hhigh := S.sector_private_peak_high i p hip hW hd hgap hpeak hprivate
  by_contra hnot
  have hsector : 1 < 3 * μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val} :=
    lt_of_not_ge hnot
  have hk := S.private_hole_measure_pos i p hip hW hd hgap hprivate
  have hk0 : 0 < μ.real (({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val})ᶜ \
      S.rootNeighborhood p) :=
    ENNReal.toReal_pos hk.ne' (measure_ne_top μ _)
  have hmissing : LowerE2Scalar.missingMass q = 1 - 2 * d := by linarith [hdq]
  -- Exact inventory of the private model.
  have hinv := S.private_body_missing_inventory i p hip hW hd hgap hprivate
  dsimp only at hinv
  have hJ : 0 ≤ ∫ z : Ω × Ω, (IndependentAtomCopy.missingBody
      (PhysicalRepresentative.adjacency W m)
      ({x | S.ρ x = i.val} ∪ {x | S.ρ x = p.val}) z.1 z.2) ^ 2 ∂μ.prod μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hbk := mul_nonneg (measureReal_nonneg (μ := μ) (s := {x | S.ρ x = p.val}))
    hk0.le
  have hinv' : (μ.real {x | S.ρ x = i.val} + μ.real {x | S.ρ x = p.val}) ^ 2 ≤
      1 - 2 * d := by
    linarith [hinv, hJ, hbk]
  -- The same original physical primal and curvature covariance.
  obtain ⟨P⟩ := S.exists_private_physical_primal i p hip hW hd hgap hprivate
  have hrow := S.sector_stationary_row_le_neighborhood hW hd hgap p
  rw [(S.private_wholeRowDegrees_sector i p hip hW hd hgap hprivate).2] at hrow
  have hl := MiddleE2Parameter.multiplier_mem hq
  have htm := MiddleE2PrivateScalar.trace_margin hq
  have hinm := MiddleE2PrivateScalar.inventory_margin hq
  rw [hmissing] at htm hinm
  exact MiddleE2PrivateScalar.sector_contradiction measureReal_nonneg measureReal_nonneg
    hk0 hsector hm hl rfl (LowerE2Scalar.contact_gapFloor_pos hq'.1) hgamma
    (hW.strict_gap_structure hd hgap).stationary_pos.le
    (by rw [← hmissing]; exact MiddleE2PrivateScalar.missingMass_lt hq)
    hinv'
    (fun hbg => S.private_body_strong_trace i p hip hW hd hgap hprivate hbg)
    htm hinm (MiddleE2PrivateScalar.NN_margin hq) (MiddleE2PrivateScalar.row_margin hq)
    hrow hCq.1 hCq.2
    (fun hmargin hNN => S.private_curvature_covariance i p hip hW hd hgap hprivate hCq.1
      hcurv hk (P.private_hole_exposure_gt_mass_sector hW hd hgap hpeak hhigh hprivate
        hsector hell hmargin hNN))

end Erdos1017.CappedModel.SelectedHighLowStructure
