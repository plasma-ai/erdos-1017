module

public import Erdos1017.Exclusions.Common.Flows.SmallFlowRecipientSets

/-!
# Simultaneous small disjoint flow recipients

Arbitrarily overlapping positive measurable regions have simultaneous disjoint
positive tiny subsets, and an integrable flow with possibly unbounded receipt
has simultaneous tiny disjoint receivers, using absolute continuity and product
Fubini.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical Function

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]

/-- Arbitrarily overlapping positive measurable regions have
simultaneous disjoint positive tiny subsets. Absolute continuity controls
the actual integral, without bounding the density. -/
theorem exists_disjoint_positive_small_subsets (n : ℕ) (B : Fin n → Set Ω)
    (hB : ∀ j, MeasurableSet (B j)) (hBpos : ∀ j, 0 < μ (B j))
    (f : Ω → ℝ) (hf : Integrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Fin n → Set Ω, (∀ j, C j ⊆ B j) ∧
      (∀ j, MeasurableSet (C j)) ∧ (∀ j, 0 < μ.real (C j)) ∧
      Pairwise (Disjoint on C) ∧
      ∀ j, μ.real (C j) + (∫ x in C j, ‖f x‖ ∂μ) < ε := by
  induction n with
  | zero =>
    exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
      fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨k, _, hk⟩ := Finset.univ.exists_min_image (fun j => μ.real (B j))
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 1))).Nonempty)
    have hkpos : 0 < μ.real (B k) :=
      ENNReal.toReal_pos (hBpos k).ne' (measure_ne_top _ _)
    obtain ⟨C₀, hC₀B, hC₀, hC₀pos, hC₀small⟩ := exists_positive_subset_mass_add_integral_lt
      (B 0) (hB 0) (hBpos 0) (fun x => ‖f x‖) hf.norm
      (min ε (μ.real (B k) / 2)) (lt_min hε (half_pos hkpos))
    have hmass : μ.real C₀ < μ.real (B k) := by
      have hn : 0 ≤ ∫ x in C₀, ‖f x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
      have hb := hC₀small.trans_le (min_le_right _ _)
      linarith
    have htailpos (j : Fin n) : 0 < μ (B j.succ \ C₀) := by
      have hlt : μ.real C₀ < μ.real (B j.succ) :=
        hmass.trans_le (hk j.succ (Finset.mem_univ _))
      have hdiff : 0 < μ.real (B j.succ \ C₀) :=
        (sub_pos.mpr hlt).trans_le (le_measureReal_sdiff (μ := μ))
      exact (ENNReal.toReal_pos_iff.mp hdiff).1
    obtain ⟨C', hsub, hmeas, hpos, hdis, hsmall⟩ := ih
      (fun j => B j.succ \ C₀) (fun j => (hB j.succ).diff hC₀) htailpos
    let C : Fin (n + 1) → Set Ω := Fin.cases C₀ C'
    refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.cases with
      | zero => exact hC₀B
      | succ j => exact (hsub j).trans sdiff_subset
    · intro j
      induction j using Fin.cases with
      | zero => exact hC₀
      | succ j => exact hmeas j
    · intro j
      induction j using Fin.cases with
      | zero => exact hC₀pos
      | succ j => exact hpos j
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact False.elim (hij rfl)
        | succ j =>
          exact Set.disjoint_left.mpr (fun x hx hy => (hsub j hy).2 hx)
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          exact Set.disjoint_left.mpr (fun x hx hy => (hsub i hx).2 hy)
        | succ j => exact hdis (fun he => hij (congrArg Fin.succ he))
    · intro j
      induction j using Fin.cases with
      | zero => exact hC₀small.trans_le (min_le_left _ _)
      | succ j => exact hsmall j

/-- Simultaneous tiny disjoint receivers for an actual integrable flow.
Its possibly unbounded receipt is integrable by actual product Fubini. -/
theorem exists_disjoint_positive_small_flow_recipients
    (q : Ω × Ω → ℝ) (hq : Integrable q (μ.prod μ))
    (n : ℕ) (B : Fin n → Set Ω)
    (hB : ∀ j, MeasurableSet (B j)) (hBpos : ∀ j, 0 < μ (B j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : Fin n → Set Ω, (∀ j, C j ⊆ B j) ∧
      (∀ j, MeasurableSet (C j)) ∧ (∀ j, 0 < μ.real (C j)) ∧
      Pairwise (Disjoint on C) ∧
      ∀ j, μ.real (C j) + (∫ x in C j, MissingFlow.receipt μ q x ∂μ) < ε := by
  have hf := (MissingFlow.integrable_marginals hq).1
  obtain ⟨C, hsub, hmeas, hpos, hdis, hsmall⟩ := exists_disjoint_positive_small_subsets
    n B hB hBpos (MissingFlow.receipt μ q) hf ε hε
  refine ⟨C, hsub, hmeas, hpos, hdis, ?_⟩
  intro j
  have hle : (∫ x in C j, MissingFlow.receipt μ q x ∂μ) ≤
      ∫ x in C j, ‖MissingFlow.receipt μ q x‖ ∂μ :=
    integral_mono hf.restrict hf.norm.restrict (fun x => by
      rw [Real.norm_eq_abs]
      exact le_abs_self _)
  linarith [hsmall j]

end Erdos1017.CappedModel
