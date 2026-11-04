module

public import Erdos1017.Models.Capped.CappedSelectedLimit
public import Erdos1017.SelectedModel.Capped.CappedMaximizerSequences
public import Erdos1017.SelectedModel.Capped.CappedPositiveGap
public import Erdos1017.SelectedModel.Selection.FullStrictGapStructure
public import Erdos1017.SelectedModel.Capped.CappedRegularityConvergence

/-!
# Uniform gap bounds for admissible cap records

`SelectedCapData` records an admissible capped optimizer with its multiplier and
stationary value, and on compact sets of strict benchmark-gap densities all
sufficiently large admissible cap records have common positive gamma and
spectral gaps (`exists_uniform_cap_gap_bounds`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Admissible actual capped optimizer data retain their own recorded
multiplier and stationary value before any strict gap is established. -/
structure SelectedCapData (r : ℕ) (W : Model Ω μ) (m ν : ℝ) : Prop where
  maximal : IsMaximizer r W
  multiplier_mem : m ∈ Icc (-3 : ℝ) 1
  deterministic : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂W.kernel p, shiftedColor m z = shiftedMoment W m p
  moment_mem : ∀ᵐ p ∂μ.prod μ, shiftedMoment W m p ∈ Icc 0 4
  complementary : ∀ᵐ p ∂μ.prod μ,
    (1 - W.moment CappedColor.adjacency p) * shiftedMoment W m p = 0
  stationary : ∀ᵐ x ∂μ, (∫ y, shiftedKernel W m x y ∂μ) = ν
  stationary_value : ν = 2 * (objective W - m * density W)
  finite_positive : FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m))
  index_le_two : Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator W m)) ≤ 2

/-- Quantitative conclusions for the same recorded cap multiplier,
including an actual meanzero eigenvector and all positive eigenvalues. -/
structure CapGapBounds (W : Model Ω μ) (m ν g s : ℝ) : Prop where
  multiplier_neg : m < 0
  regular : Variation.weightFirstVariation (adjacencyOperator W) ≠ 0
  gamma_lower : g ≤ ν + m
  meanzero_eigenvector : ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧
    0 < σ ∧ s ≤ σ ∧ shiftedOperator W m w = σ • w
  positive_gap : ∀ (σ : ℝ), 0 < σ → ∀ w : Lp ℝ 2 μ,
    w ≠ 0 → shiftedOperator W m w = σ • w → s ≤ σ

/-- Lowering either quantitative lower bound preserves the recorded gaps. -/
theorem CapGapBounds.mono {W : Model Ω μ} {m ν g s g' s' : ℝ}
    (h : CapGapBounds W m ν g s) (hg : g' ≤ g) (hs : s' ≤ s) : CapGapBounds W m ν g' s' := by
  obtain ⟨w, σ, hw, hmean, hσ, hgap, heigen⟩ := h.meanzero_eigenvector
  exact ⟨h.multiplier_neg, h.regular, hg.trans h.gamma_lower,
    ⟨w, σ, hw, hmean, hσ, hs.trans hgap, heigen⟩,
    fun σ hσ w hw heigen => hs.trans (h.positive_gap σ hσ w hw heigen)⟩

/-- Actual positive eigenvalue lower bounds transfer back from an
invertible measure-preserving alignment to the original shifted operator. -/
theorem positive_eigenvalue_gap_of_pullback (W : Model Ω μ) (m s : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (hgap : ∀ (σ : ℝ), 0 < σ → ∀ w : Lp ℝ 2 μ, w ≠ 0 →
      shiftedOperator (W.pullback e he) m w = σ • w → s ≤ σ) :
    ∀ (σ : ℝ), 0 < σ → ∀ w : Lp ℝ 2 μ, w ≠ 0 → shiftedOperator W m w = σ • w → s ≤ σ := by
  intro σ hσ w hw heigen
  let U := KernelOperator.reindexL2 e he
  have hUw : U w ≠ 0 := by
    intro hz
    exact hw (U.injective (hz.trans U.map_zero.symm))
  have heigen' : shiftedOperator (W.pullback e he) m (U w) = σ • U w := by
    rw [shiftedOperator_pullback_intertwines, heigen, map_smul]
  exact hgap σ hσ (U w) hUw heigen'

/-- An actual meanzero eigenvector with a given eigenvalue gap transfers
back through the same exact alignment, including its original mean zero. -/
theorem positive_meanzero_eigenvector_of_pullback (W : Model Ω μ) (m s : ℝ)
    (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (hvector : ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧
      0 < σ ∧ s ≤ σ ∧ shiftedOperator (W.pullback e he) m w = σ • w) :
    ∃ (w : Lp ℝ 2 μ) (σ : ℝ), w ≠ 0 ∧ (∫ x, w x ∂μ) = 0 ∧
      0 < σ ∧ s ≤ σ ∧ shiftedOperator W m w = σ • w := by
  obtain ⟨w, σ, hw, hmean, hσ, hgap, heigen⟩ := hvector
  let U := KernelOperator.reindexL2 e he
  let u := U.symm w
  have hUu : U u = w := U.apply_symm_apply w
  have hu : u ≠ 0 := by
    intro hz
    exact hw (hUu.symm.trans (by rw [hz, map_zero]))
  have hcoef : ∀ᵐ x ∂μ, w x = u (e x) := by
    have h := KernelOperator.reindexL2_ae e he u
    change ∀ᵐ x ∂μ, U u x = u (e x) at h
    simpa only [hUu] using h
  have hmean' : (∫ x, u x ∂μ) = 0 := by
    have heq : (∫ x, w x ∂μ) = ∫ x, u x ∂μ :=
      (integral_congr_ae hcoef).trans (he.integral_comp' (fun x => u x))
    exact heq.symm.trans hmean
  refine ⟨u, σ, hu, hmean', hσ, hgap, ?_⟩
  apply U.injective
  calc
    U (shiftedOperator W m u) = shiftedOperator (W.pullback e he) m (U u) :=
      (shiftedOperator_pullback_intertwines W m e he u).symm
    _ = σ • U u := by rw [hUu, heigen]
    _ = U (σ • u) := (U.map_smul σ u).symm

/-- Actual capped maximality identifies the objective with the genuine
finite-cap supremum on the same probability carrier. -/
theorem objective_eq_capValue_of_isMaximizer (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W) :
    objective W = capValue Ω μ r (density W) := by
  let S : Set ℝ := {c | ∃ V : Model Ω μ, Feasible r V ∧ density V = density W ∧ objective V = c}
  have hmem : objective W ∈ S := ⟨W, hW.1, rfl, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨density W, ?_⟩
    rintro c ⟨V, _, hd, rfl⟩
    exact (objective_le_density V).trans_eq hd
  change objective W = sSup S
  apply le_antisymm (le_csSup hbdd hmem)
  apply csSup_le ⟨objective W, hmem⟩
  rintro c ⟨V, hV, hd, rfl⟩
  exact hW.2 μ Measure.absolutelyContinuous_rfl V hV hd

/-- The capped selection theorem populates the record
class without imposing any strict-gap or uniform-bound conclusion. -/
theorem exists_selected_cap_data [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
    (W : Model Ω μ) {r : ℕ} (hW : IsMaximizer r W)
    (hd0 : 0 < density W) (hdhalf : density W < 1 / 2) :
    ∃ (V : Model Ω μ) (m ν : ℝ), density V = density W ∧ objective V = objective W ∧
      SelectedCapData r V m ν := by
  obtain ⟨V, m, ν, hV, hdV, hcV, hm, hdet, hmem, hcomp, hrow, hν, hfinite, hindex⟩ :=
    exists_selected_capped_kernel W hW hd0 hdhalf
  exact ⟨V, m, ν, hdV, hcV, ⟨hV, hm, hdet, hmem, hcomp, hrow, hν, hfinite, hindex⟩⟩

variable [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω] [NullSingletonClass μ]

/-- Every supplied growing-cap maximizer sequence has genuine objective
convergence at its actual limiting density; no objective limit is assumed. -/
theorem objective_tendsto_of_growing_maximizers (W : ℕ → Model Ω μ) (r : ℕ → ℕ) (d : ℝ)
    (hr : Tendsto r atTop atTop) (hW : ∀ n, IsMaximizer (r n) (W n))
    (hd : Tendsto (fun n => density (W n)) atTop (𝓝 d)) :
    Tendsto (fun n => objective (W n)) atTop (𝓝 (FractionalGraph.densityLimit d)) := by
  have heq (n : ℕ) := objective_eq_capValue_of_isMaximizer (W n) (hW n)
  simp_rw [heq]
  exact capValue_tendsto_of_density_cutoff r _ d hr (fun n => density_mem (W n)) hd

variable [StandardBorelSpace Ω] [MeasurableEq Ω]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]

/-- Any supplied growing-cap record sequence at a strict benchmark-gap
limit density has an actual subsequence with uniform recorded gaps.
The supplied multipliers and stationary values are never reselected. -/
theorem exists_subseq_cap_gap_bounds (W : ℕ → Model Ω μ) (r : ℕ → ℕ) (m ν : ℕ → ℝ) (d : ℝ)
    (hr : Tendsto r atTop atTop) (hdata : ∀ n, SelectedCapData (r n) (W n) (m n) (ν n))
    (hd : Tendsto (fun n => density (W n)) atTop (𝓝 d))
    (hdomain : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < FractionalGraph.densityLimit d) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g s : ℝ, 0 < g ∧ 0 < s ∧
      ∀ᶠ n in atTop, CapGapBounds (W (φ n)) (m (φ n)) (ν (φ n)) g s := by
  have hc := objective_tendsto_of_growing_maximizers W r d hr (fun n => (hdata n).maximal) hd
  obtain ⟨V, φ, hφ, e, he, m₀, hm₀, hfull, hdV, hcV, hweak, hcut, hmult, hνlim, hop,
      _, hmemV, hrowV, hfiniteV, hindexV, hL2⟩ :=
    exists_selected_cap_limit W r m ν d (FractionalGraph.densityLimit d) hr
      (fun n => (hdata n).maximal) (fun n => (hdata n).multiplier_mem)
      (fun n => (hdata n).deterministic) (fun n => (hdata n).moment_mem)
      (fun n => (hdata n).stationary) (fun n => (hdata n).finite_positive)
      (fun n => (hdata n).index_le_two) hd hc
  let A := fun n => (W (φ n)).pullback (e n) (he n)
  let ν₀ := 2 * (objective V - m₀ * density V)
  have hdetA (n : ℕ) : ∀ᵐ p ∂μ.prod μ, ∀ᵐ z ∂(A n).kernel p,
      shiftedColor (m (φ n)) z = shiftedMoment (A n) (m (φ n)) p :=
    ((he n).prod (he n)).quasiMeasurePreserving.ae (hdata (φ n)).deterministic
  have hmemA (n : ℕ) : ∀ᵐ p ∂μ.prod μ, shiftedMoment (A n) (m (φ n)) p ∈ Icc 0 4 :=
    ((he n).prod (he n)).quasiMeasurePreserving.ae (hdata (φ n)).moment_mem
  have hdetV := shifted_deterministic_of_jointLaw_L2_limit A V (fun n => m (φ n)) m₀ hm₀
    hweak hmult hdetA hmemA hmemV (by simpa only [shiftedKernel] using hL2)
  have hcompV := shifted_complementary_of_deterministic V m₀ hdetV
  have hoptV : objective V = FractionalGraph.densityLimit (density V) := by rw [hdV, hcV]
  have hdomainV : density V ∈ Ioo (1 / 4 : ℝ) (1 / 2) := hdV ▸ hdomain
  have hgapV : benchmark (density V) < objective V := by rw [hdV, hcV]; exact hgap
  have hstructure := full_strict_gap_structure V hfull hoptV hdomainV hgapV m₀ ν₀ hm₀ hrowV
    (hmemV.mono (fun _ h => h.1)) hcompV hdetV hfiniteV hindexV
  have hAdj := adjacencyOperator_tendsto_of_moment_cut A V (hcut adjacencyCutTest adjacencyCutTest_mem)
  have hregular := eventually_adjacency_regular_original_of_aligned_operator_tendsto
    (fun n => W (φ n)) V e he hAdj hstructure.regular
  have hnegative : ∀ᶠ n in atTop, m (φ n) < 0 := hmult.eventually (gt_mem_nhds hstructure.multiplier_neg)
  let g := (ν₀ + m₀) / 2
  have hg : 0 < g := half_pos hstructure.gamma_pos
  have hgamma : ∀ᶠ n in atTop, g ≤ ν (φ n) + m (φ n) :=
    (hνlim.add hmult).eventually (le_mem_nhds (by dsimp [g]; linarith [hstructure.gamma_pos]))
  have hfiniteA (n : ℕ) : FiniteDimensional ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (A n) (m (φ n)))) := by
    let := (hdata (φ n)).finite_positive
    exact finiteDimensional_positive_shiftedOperator_pullback (W (φ n)) (m (φ n)) (e n) (he n)
  have hindexA (n : ℕ) : Module.finrank ℝ
      (KernelOperator.positiveSpectralSubspace (shiftedOperator (A n) (m (φ n)))) ≤ 2 := by
    rw [finrank_positive_shiftedOperator_pullback]
    exact (hdata (φ n)).index_le_two
  have hrowA (n : ℕ) : ∀ᵐ x ∂μ,
      (∫ y, shiftedKernel (A n) (m (φ n)) x y ∂μ) = ν (φ n) :=
    shifted_row_pullback (W (φ n)) (m (φ n)) (ν (φ n)) (hdata (φ n)).stationary (e n) (he n)
  have hlimit : ¬(FiniteDimensional ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ∧
      Module.finrank ℝ (KernelOperator.positiveSpectralSubspace (shiftedOperator V m₀)) ≤ 1) := by
    rintro ⟨_, hsmall⟩
    rw [hstructure.index_eq_two] at hsmall
    omega
  have hcompactV : IsCompactOperator (shiftedOperator V m₀) := KernelOperator.operator_isCompact _ _ _ _
  have hsymV : (shiftedOperator V m₀).toLinearMap.IsSymmetric := by
    apply KernelOperator.operator_symmetric _ _ _ _
    filter_upwards [shiftedMoment_symm V m₀] with p hp
    exact hp.symm
  obtain ⟨P, hfiniteP, hdim, s, hs, hplane⟩ :=
    KernelOperator.two_dimensional_positive_subspace_persists hop hcompactV hsymV hlimit
  let := hfiniteP
  refine ⟨φ, hφ, g, s, hg, hs, ?_⟩
  filter_upwards [hnegative, hregular, hgamma, hplane] with n hmn hregn hgn hpn
  let := hfiniteA n
  refine ⟨hmn, hregn, hgn, ?_, ?_⟩
  · exact positive_meanzero_eigenvector_of_pullback (W (φ n)) (m (φ n)) s (e n) (he n)
      (exists_meanzero_eigenvector_with_gap_of_coercive_plane (A n) (m (φ n)) (ν (φ n)) (hrowA n)
        (hindexA n) P hdim s hs hpn)
  · have hcompactA : IsCompactOperator (shiftedOperator (A n) (m (φ n))) :=
      KernelOperator.operator_isCompact _ _ _ _
    have hsymA : (shiftedOperator (A n) (m (φ n))).toLinearMap.IsSymmetric := by
      apply KernelOperator.operator_symmetric _ _ _ _
      filter_upwards [shiftedMoment_symm (A n) (m (φ n))] with p hp
      exact hp.symm
    apply positive_eigenvalue_gap_of_pullback (W (φ n)) (m (φ n)) s (e n) (he n)
    exact fun σ hσ w hw heigen => KernelOperator.positive_eigenvalue_ge_of_coercive_plane
      (shiftedOperator (A n) (m (φ n))) hcompactA hsymA (hindexA n) P hdim s hs hpn σ hσ w hw heigen

/-- Compact sets of genuine strict benchmark-gap densities admit uniform
eventual bounds for every admissible cap record, retaining its same
recorded multiplier and stationary value. -/
theorem exists_uniform_cap_gap_bounds (J : Set ℝ) (hJ : IsCompact J)
    (hdomain : J ⊆ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : ∀ d ∈ J, benchmark d < FractionalGraph.densityLimit d) :
    ∃ r₀ : ℕ, ∃ g s : ℝ, 0 < g ∧ 0 < s ∧
      ∀ r : ℕ, r₀ ≤ r → ∀ (W : Model Ω μ) (m ν : ℝ),
        SelectedCapData r W m ν → density W ∈ J → CapGapBounds W m ν g s := by
  classical
  by_contra hnot
  push Not at hnot
  have hbad (n : ℕ) : ∃ r : ℕ, n ≤ r ∧ ∃ (W : Model Ω μ) (m ν : ℝ),
      SelectedCapData r W m ν ∧ density W ∈ J ∧
        ¬CapGapBounds W m ν (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) :=
    hnot n _ _ (by positivity) (by positivity)
  choose r hr W m ν hdata hdens hfail using hbad
  have hrgrow : Tendsto r atTop atTop := tendsto_atTop_mono hr tendsto_id
  obtain ⟨d, hdJ, ψ, hψ, hdlim⟩ := hJ.tendsto_subseq hdens
  obtain ⟨φ, hφ, g, s, hg, hs, hgood⟩ := exists_subseq_cap_gap_bounds
    (W ∘ ψ) (r ∘ ψ) (m ∘ ψ) (ν ∘ ψ) d (hrgrow.comp hψ.tendsto_atTop)
    (fun n => hdata (ψ n)) hdlim (hdomain hdJ) (hgap d hdJ)
  have hsmall : Tendsto (fun n => 1 / ((ψ (φ n) : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (hψ.comp hφ).tendsto_atTop
  obtain ⟨n, hn, hgn, hsn⟩ :=
    (hgood.and ((hsmall.eventually (gt_mem_nhds hg)).and
      (hsmall.eventually (gt_mem_nhds hs)))).exists
  exact hfail (ψ (φ n)) (hn.mono hgn.le hsn.le)

/-- At any one genuine strict benchmark-gap density, all sufficiently
large admissible cap records have common positive gamma and spectral gaps. -/
theorem exists_uniform_cap_gap_bounds_at_density (d : ℝ)
    (hdomain : d ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hgap : benchmark d < FractionalGraph.densityLimit d) :
    ∃ r₀ : ℕ, ∃ g s : ℝ, 0 < g ∧ 0 < s ∧
      ∀ r : ℕ, r₀ ≤ r → ∀ (W : Model Ω μ) (m ν : ℝ),
        SelectedCapData r W m ν → density W = d → CapGapBounds W m ν g s := by
  obtain ⟨r₀, g, s, hg, hs, hbound⟩ := exists_uniform_cap_gap_bounds (μ := μ) ({d} : Set ℝ) isCompact_singleton
    (by intro x hx; simpa only [mem_singleton_iff.mp hx] using hdomain)
    (by intro x hx; simpa only [mem_singleton_iff.mp hx] using hgap)
  exact ⟨r₀, g, s, hg, hs, fun r hr W m ν hdata hd => hbound r hr W m ν hdata hd⟩

end Erdos1017.CappedModel
