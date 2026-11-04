module

public import Erdos1017.Exclusions.Cusp.SelectedCuspSourceCredits
public import Erdos1017.Exclusions.Cusp.MultipartiteShiftedCubicBound

/-!
# Shifted energy of the whole source remainder

The original remainder, conditioned as a probability law, keeps a fully feasible
multipartite dual, so the collision bound controls its energy, and in the
reciprocal-cusp slope range the shifted remainder energy has the strict `1/50`
excess bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}

private theorem integral_cond_square (T : Set Ω) (f : Ω × Ω → ℝ) :
    (∫ p, f p ∂(cond μ T).prod (cond μ T)) =
      (∫ p in T ×ˢ T, f p ∂μ.prod μ) / (μ.real T) ^ 2 := by
  simp only [ProbabilityTheory.cond, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, Measure.prod_restrict, Measure.real]
  ring

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] [StandardBorelSpace Ω]
  [MeasurableEq Ω] [NullSingletonClass μ]

/-- The actual original remainder is conditioned as a genuine probability
law. Its unchanged dual remains fully feasible and multipartite, so the
collision bound controls its shifted energy without restricted stationarity. -/
theorem cuspRemainderEnergy_div_sq_le (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (i : S.I)
    (hpos : 0 < μ.real (R.cuspSourceRemainder i)) (hlo : 1 ≤ -m) (hhi : -m ≤ 2) :
    R.cuspRemainderEnergy i / (μ.real (R.cuspSourceRemainder i)) ^ 2 ≤
      -m + 64 * (2 + m) ^ 3 / 1323 := by
  let : Countable S.I := S.hI.to_subtype
  let J := R.cuspSourceRemainder i
  let ν := cond μ J
  have hJ0 : μ J ≠ 0 := by
    intro hz
    change 0 < (μ J).toReal at hpos
    simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure hJ0
  have hac : ν ≪ μ := cond_absolutelyContinuous
  let : NullSingletonClass ν := ⟨fun x => hac (measure_singleton x)⟩
  let V := W.changeMeasure hac
  have hfull : FullFeasible V := fun n => feasible_changeMeasure W hac (hW.full n)
  have hhalf := S.ae_collapsed_half_support hW hd hgap true
  rw [Measure.prod_restrict] at hhalf
  have hhalf' := (ae_restrict_iff' ((S.measurableSet_half true).prod
    (S.measurableSet_half true))).mp hhalf
  have hJ : ∀ᵐ x ∂ν, x ∈ J := ae_cond_mem (R.measurableSet_cuspSourceRemainder i)
  have hsupport : ∀ᵐ p ∂ν.prod ν, V.moment CappedColor.adjacency p =
      if S.collapsedPartLabel p.1 ≠ S.collapsedPartLabel p.2 ∨ S.collapsedPartLabel p.1 = none
      then 1 else 0 := by
    filter_upwards [(hac.prod hac).ae_le hhalf', Measure.quasiMeasurePreserving_fst.ae hJ,
      Measure.quasiMeasurePreserving_snd.ae hJ] with p hp hx hy
    exact hp ⟨Or.inl hx.1.1, Or.inl hy.1.1⟩
  have hb := MultipartiteClassMasses.shifted_objective_le_cubic V hfull
    S.collapsedPartLabel S.measurable_collapsedPartLabel (by
      filter_upwards [hsupport] with p hp
      split_ifs at hp ⊢ <;> exact hp) (-m) hlo hhi
  have he := integral_shiftedMoment V m
  have hnorm := integral_cond_square (μ := μ) J (fun p => shiftedKernel W m p.1 p.2)
  change (∫ p, shiftedMoment V m p ∂ν.prod ν) =
    R.cuspRemainderEnergy i / (μ.real (R.cuspSourceRemainder i)) ^ 2 at hnorm
  rw [hnorm] at he
  nlinarith

/-- In the reciprocal-cusp slope range, the actual whole-remainder
shifted energy has the strict 1/50 excess bound. -/
theorem cuspRemainderEnergy_div_sq_lt (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (i : S.I)
    (hpos : 0 < μ.real (R.cuspSourceRemainder i)) (hlo : 29 / 21 ≤ -m) (hhi : -m ≤ 2) :
    R.cuspRemainderEnergy i / (μ.real (R.cuspSourceRemainder i)) ^ 2 < -m + 1 / 50 := by
  have hb := R.cuspRemainderEnergy_div_sq_le hW hd hgap i hpos (by linarith) hhi
  have hc := MultipartiteClassMasses.shifted_cubic_excess_lt hlo hhi
  nlinarith

/-- The positive-edge source hypothesis itself supplies positive remainder
mass. Both displayed bounds therefore apply to its actual normalized law. -/
theorem cuspRemainderEnergy_bound_of_positive_source (R : S.ReverseRecovery) {d c : ℝ}
    (hW : FullStationaryClass d c W m) (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < c) (i : S.I)
    (hsourceEdge : 0 < ∫ p in R.cuspSource ×ˢ R.cuspSource,
      adjacencyKernel W p.1 p.2 ∂μ.prod μ)
    (hlo : 29 / 21 ≤ -m) (hhi : -m ≤ 2) :
    0 < μ.real (R.cuspSourceRemainder i) ∧
      R.cuspRemainderEnergy i / (μ.real (R.cuspSourceRemainder i)) ^ 2 ≤
        -m + 64 * (2 + m) ^ 3 / 1323 ∧
      -m + 64 * (2 + m) ^ 3 / 1323 < -m + 1 / 50 := by
  have hz := R.cuspSourceRemainder_mass_pos i hsourceEdge
  refine ⟨hz, R.cuspRemainderEnergy_div_sq_le hW hd hgap i hz (by linarith) hhi, ?_⟩
  have h := MultipartiteClassMasses.shifted_cubic_excess_lt hlo hhi
  nlinarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
