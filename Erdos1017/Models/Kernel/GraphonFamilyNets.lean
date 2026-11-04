/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer

The finite-net construction below is adapted from
vendor/Graphon/Graphon/Compactness.lean.
-/
module

public import Erdos1017.Models.Kernel.GraphonFamilyRegularity
public import Erdos1017.Models.Kernel.GraphonFamilyRounding

/-!
# Finite nets for graphon families

Finite nets for finite graphon families use one relabeling for all coordinates
(`exists_finite_net`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Graphon
open scoped ENNReal

namespace Erdos1017.GraphonFamily

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [NullSingletonClass μ] [Fintype ι]

/-- Finite nets for finite graphon families use one relabeling for all coordinates. -/
theorem exists_finite_net (ε : ℝ) (hε : ε > 0) :
    ∃ (S : Finset (ι → Graphon Ω μ)), ∀ W : ι → Graphon Ω μ,
      ∃ V ∈ S, ∃ e : Ω ≃ᵐ Ω, ∃ he : MeasurePreserving e μ μ,
        ∀ i, Graphon.cutNormDiff (Graphon.pullback (W i) e he) (V i) ≤ ε := by
  -- Following Cameron Freer's scalar construction, fix a canonical equal-measure
  -- `q`-cell partition `E` and build a grid net of families on `E`.
  -- Simultaneous regularity and rerounding use shared partitions `P_W` and `Q`.
  -- Alignment of `Q` with `E` gives one map `e` for every coordinate.
  -- Each coordinate has cut-norm error at most ε/3 + ε/3 + ε/3.
  classical
  -- Parameters
  set ε₃ := ε / 3 with hε₃_def
  have hε₃ : ε₃ > 0 := by positivity
  set N := Nat.ceil (3 / ε) with hN_def
  have hN_pos : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have h1N_le : (1 : ℝ) / N ≤ ε₃ := by
    rw [hε₃_def]
    have hN_le : (3 / ε : ℝ) ≤ N := Nat.le_ceil (3 / ε)
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr hN_pos) (by norm_num : (0:ℝ) < 3), one_mul]
    calc (3 : ℝ) = ε * (3 / ε) := by field_simp
      _ ≤ ε * N := by apply mul_le_mul_of_nonneg_left hN_le hε.le
  set m₀ := 4 ^ (Nat.ceil ((Fintype.card ι : ℝ) / ε₃ ^ 2) + 1) with hm₀_def
  set q := Nat.ceil (6 * (m₀ : ℝ) / ε) + 1 with hq_def
  have hq : 0 < q := by omega
  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq
  -- q is large enough that 2 * m₀ / q ≤ ε/3
  have hεq : 6 * (m₀ : ℝ) ≤ ε * q := by
    have h1 : (6 * (m₀ : ℝ) / ε) ≤ q := by
      have hc := Nat.le_ceil (6 * (m₀ : ℝ) / ε)
      rw [hq_def]; push_cast; linarith
    calc 6 * (m₀ : ℝ) = ε * (6 * (m₀ : ℝ) / ε) := by field_simp
      _ ≤ ε * q := by apply mul_le_mul_of_nonneg_left h1 hε.le
  have h2m0q : 2 * (m₀ : ℝ) / q ≤ ε₃ := by
    rw [div_le_iff₀ hq_real, hε₃_def]; nlinarith [hεq]
  -- Fix a canonical equal-measure q-cell partition E (W-independent)
  obtain ⟨E, hEcard, hEmu, -⟩ :=
    exists_equipartition_almost_refining (trivialPartition (α := Ω) (μ := μ)) hq
  -- Injective enumeration of E's cells
  set eqE := (E.parts.equivFinOfCardEq hEcard).symm with heqE_def
  set ιE : Fin q → Set Ω := fun i => (eqE i : Set Ω) with hιE_def
  have hιE_mem : ∀ i, ιE i ∈ E.parts := fun i => (eqE i).2
  have hιE_inj : Function.Injective ιE := fun i j h => eqE.injective (Subtype.ext h)
  have hιE_mu : ∀ i, μ (ιE i) = (1 : ℝ≥0∞) / q := fun i => hEmu _ (hιE_mem i)
  -- Build finite net on E: all mkStepGraphon E with symmetrized grid coefficients
  let toCoeff : (ι → ↑E.parts → ↑E.parts → Fin (N + 1)) → ι → Set Ω → Set Ω → ℝ :=
    fun f i S T =>
      if hS : S ∈ E.parts then
        if hT : T ∈ E.parts then
          ((f i ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) + (f i ⟨T, hT⟩ ⟨S, hS⟩ : ℕ)) / (2 * N)
        else 0
      else 0
  have htoCoeff_symm : ∀ f, ∀ i, ∀ S ∈ E.parts, ∀ T ∈ E.parts,
      toCoeff f i S T = toCoeff f i T S := by
    intro f i S hS T hT
    simp only [toCoeff, hS, hT, dite_eq_left]
    ring
  have htoCoeff_mem : ∀ f, ∀ i, ∀ S ∈ E.parts, ∀ T ∈ E.parts,
      toCoeff f i S T ∈ Set.Icc 0 1 := by
    intro f i S hS T hT
    simp only [toCoeff, hS, hT, dite_eq_left, Set.mem_Icc]
    refine ⟨by positivity, ?_⟩
    have h1 : (f i ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) ≤ N := by omega
    have h2 : (f i ⟨T, hT⟩ ⟨S, hS⟩ : ℕ) ≤ N := by omega
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * N)]
    have h1' : (↑(f i ⟨S, hS⟩ ⟨T, hT⟩ : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h1
    have h2' : (↑(f i ⟨T, hT⟩ ⟨S, hS⟩ : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr h2
    linarith
  let netMap : (ι → ↑E.parts → ↑E.parts → Fin (N + 1)) → ι → Graphon Ω μ :=
    fun f i => mkStepGraphon E (toCoeff f i) (htoCoeff_symm f i) (htoCoeff_mem f i)
  let net : Finset (ι → Graphon Ω μ) := Finset.univ.image netMap
  use net
  -- For any W, find a close net element
  intro W
  obtain ⟨P_W, hP_W_card, hP_W_close⟩ := regularity W ε₃ hε₃
  -- Rectangular averages give step graphons on the common regularity partition.
  have hRA_symm : ∀ i, ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      rectAverage (W i) S T = rectAverage (W i) T S := by
    intro i S hS T hT
    exact rectAverage_symm (W i) S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
  have hRA_mem : ∀ i, ∀ S ∈ P_W.parts, ∀ T ∈ P_W.parts,
      rectAverage (W i) S T ∈ Set.Icc 0 1 := by
    intro i S hS T hT
    exact rectAverage_mem_Icc (W i) S T (P_W.measurableSet_part hS) (P_W.measurableSet_part hT)
  let V_avg : ι → Graphon Ω μ := fun i =>
    mkStepGraphon P_W (rectAverage (W i)) (hRA_symm i) (hRA_mem i)
  have h_cn_stepavg : ∀ i, cutNormDiff (stepify P_W (W i)) (V_avg i) = 0 := by
    intro i
    have h_stepify_eq_avg : ∀ᵐ p ∂(μ.prod μ),
        (stepify P_W (W i)).toAEEqFun p = (V_avg i).toAEEqFun p := by
      have h_fun_eq : stepifyFun P_W (W i) = mkStepFun P_W (rectAverage (W i)) := rfl
      have h1 := stepify_ae P_W (W i)
      have h2 : ∀ᵐ p ∂(μ.prod μ), (V_avg i).toAEEqFun p =
          mkStepFun P_W (rectAverage (W i)) p := AEEqFun.coeFn_mk _ _
      filter_upwards [h1, h2] with p hp1 hp2
      rw [hp1, h_fun_eq, hp2]
    unfold cutNormDiff rectIntegralDiff
    apply le_antisymm
    · apply Real.iSup_le _ le_rfl
      intro S'; apply Real.iSup_le _ le_rfl
      intro hS'; apply Real.iSup_le _ le_rfl
      intro T'; apply Real.iSup_le _ le_rfl
      intro hT'
      have h_ae : ∀ᵐ p ∂(μ.prod μ),
          (stepify P_W (W i)).toAEEqFun p - (V_avg i).toAEEqFun p = 0 := by
        filter_upwards [h_stepify_eq_avg] with p hp
        rw [hp, sub_self]
      have h_zero : ∫ p in S' ×ˢ T',
          ((stepify P_W (W i)).toAEEqFun p - (V_avg i).toAEEqFun p) ∂(μ.prod μ) = 0 := by
        rw [setIntegral_congr_ae (hS'.prod hT') (h_ae.mono (fun p hp _ => hp))]
        simp
      rw [h_zero]; simp
    · exact cutNormDiff_nonneg _ _
  -- Re-round every average on the same equal-measure partition Q.
  obtain ⟨Q, cQ, hcQ_symm, hcQ_mem, hQcard, hQmu, hbound⟩ :=
    reround_family_to_equipartition P_W (fun i => rectAverage (W i)) hRA_symm hRA_mem hq
  let V_Q : ι → Graphon Ω μ := fun i => mkStepGraphon Q (cQ i) (hcQ_symm i) (hcQ_mem i)
  have h_cn_reround : ∀ i, cutNormDiff (V_avg i) (V_Q i) ≤ ε₃ := by
    intro i
    calc cutNormDiff (V_avg i) (V_Q i)
        ≤ 2 * (P_W.parts.card : ℝ) / q := hbound i
      _ ≤ 2 * (m₀ : ℝ) / q := by gcongr
      _ ≤ ε₃ := h2m0q
  -- Grid-round the coefficients of Q
  let roundCQ : ι → Set Ω → Set Ω → ℝ := fun i S T =>
    if hS : S ∈ Q.parts then
      if hT : T ∈ Q.parts then
        (Nat.floor (cQ i S T * N) : ℝ) / N
      else 0
    else 0
  have hroundCQ_symm : ∀ i, ∀ S ∈ Q.parts, ∀ T ∈ Q.parts, roundCQ i S T = roundCQ i T S := by
    intro i S hS T hT
    simp only [roundCQ, hS, hT, dite_eq_left]
    rw [hcQ_symm i S hS T hT]
  have hroundCQ_mem : ∀ i, ∀ S ∈ Q.parts, ∀ T ∈ Q.parts, roundCQ i S T ∈ Set.Icc 0 1 := by
    intro i S hS T hT
    simp only [roundCQ, hS, hT, dite_eq_left, Set.mem_Icc]
    have hc := hcQ_mem i S hS T hT
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (Nat.cast_pos.mpr hN_pos)]
    have : cQ i S T * N ≤ N := by nlinarith [hc.2]
    exact_mod_cast Nat.floor_le_of_le (by exact_mod_cast this)
  have hroundCQ_close : ∀ i, ∀ S ∈ Q.parts, ∀ T ∈ Q.parts,
      |cQ i S T - roundCQ i S T| ≤ 1 / (N : ℝ) := by
    intro i S hS T hT
    simp only [roundCQ, hS, hT, dite_eq_left]
    have hc := hcQ_mem i S hS T hT
    have hN_pos' : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
    have h_nn : 0 ≤ cQ i S T * N := mul_nonneg hc.1 (Nat.cast_nonneg N)
    have h_floor_le : (Nat.floor (cQ i S T * N) : ℝ) ≤ cQ i S T * N := Nat.floor_le h_nn
    have h_lt : cQ i S T * ↑N < (Nat.floor (cQ i S T * ↑N) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h_sub_nn : 0 ≤ cQ i S T - (↑⌊cQ i S T * ↑N⌋₊ : ℝ) / N := by
        rw [sub_nonneg, div_le_iff₀ hN_pos']; linarith
      have h_inv_pos : (0 : ℝ) < 1 / N := div_pos one_pos hN_pos'
      linarith
    · rw [sub_le_iff_le_add,
        show 1 / (↑N : ℝ) + (↑⌊cQ i S T * ↑N⌋₊ : ℝ) / ↑N =
          (↑⌊cQ i S T * ↑N⌋₊ + 1) / ↑N from by ring, le_div_iff₀ hN_pos']
      linarith
  let V_QR : ι → Graphon Ω μ := fun i =>
    mkStepGraphon Q (roundCQ i) (hroundCQ_symm i) (hroundCQ_mem i)
  have h_cn_grid : ∀ i, cutNormDiff (V_Q i) (V_QR i) ≤ ε₃ := by
    intro i
    calc cutNormDiff (V_Q i) (V_QR i)
        ≤ 1 / (N : ℝ) := cutNormDiff_mkStepGraphon_le Q (cQ i) (roundCQ i)
            (hcQ_symm i) (hcQ_mem i) (hroundCQ_symm i) (hroundCQ_mem i)
            (1 / N) (hroundCQ_close i)
      _ ≤ ε₃ := h1N_le
  -- Align Q with E using one measurable equivalence.
  set eqQ := (Q.parts.equivFinOfCardEq hQcard).symm with heqQ_def
  set ιQ : Fin q → Set Ω := fun i => (eqQ i : Set Ω) with hιQ_def
  have hιQ_mem : ∀ i, ιQ i ∈ Q.parts := fun i => (eqQ i).2
  have hιQ_inj : Function.Injective ιQ := fun i j h => eqQ.injective (Subtype.ext h)
  have hιQ_mu : ∀ i, μ (ιQ i) = (1 : ℝ≥0∞) / q := fun i => hQmu _ (hιQ_mem i)
  have hμ_match : ∀ i, μ (ιE i) = μ (ιQ i) := fun i => by rw [hιE_mu, hιQ_mu]
  obtain ⟨e, he, h_align⟩ :=
    MeasurePreserving.exists_controlled_cell_alignment E Q ιE ιQ
      hιE_mem hιQ_mem hιE_inj hιQ_inj hμ_match
  -- Index each family member's rounded coefficients by the aligned E-cells.
  let f : ι → ↑E.parts → ↑E.parts → Fin (N + 1) := fun i S T =>
    ⟨Nat.floor (cQ i (ιQ (eqE.symm S)) (ιQ (eqE.symm T)) * N), by
      have hc := hcQ_mem i (ιQ (eqE.symm S)) (hιQ_mem _) (ιQ (eqE.symm T)) (hιQ_mem _)
      apply Nat.lt_succ_of_le
      exact Nat.floor_le_of_le
        (by exact_mod_cast (by nlinarith [hc.2] :
          cQ i (ιQ (eqE.symm S)) (ιQ (eqE.symm T)) * ↑N ≤ ↑N))⟩
  -- The net coefficients agree with those of the aligned Q-cells.
  have h_coeff_eq : ∀ i, ∀ S (hS : S ∈ E.parts) T (hT : T ∈ E.parts),
      toCoeff f i S T = roundCQ i (ιQ (eqE.symm ⟨S, hS⟩)) (ιQ (eqE.symm ⟨T, hT⟩)) := by
    intro i S hS T hT
    have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
    simp only [toCoeff, hS, hT, dite_eq_left, f, roundCQ,
      hιQ_mem (eqE.symm ⟨S, hS⟩), hιQ_mem (eqE.symm ⟨T, hT⟩)]
    have h_symm := hcQ_symm i (ιQ (eqE.symm ⟨T, hT⟩)) (hιQ_mem _)
      (ιQ (eqE.symm ⟨S, hS⟩)) (hιQ_mem _)
    rw [h_symm]
    field_simp
    ring
  have hf_mem : netMap f ∈ net := Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩
  -- Each rounded graphon agrees almost everywhere with its net member after pullback.
  have h_align_all : ∀ᵐ x ∂μ, ∀ i, x ∈ ιE i → e x ∈ ιQ i := (ae_all_iff).mpr h_align
  have h_e_fst : ∀ᵐ p ∂(μ.prod μ), ∀ i, p.1 ∈ ιE i → e p.1 ∈ ιQ i :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h_align_all
  have h_e_snd : ∀ᵐ p ∂(μ.prod μ), ∀ i, p.2 ∈ ιE i → e p.2 ∈ ιQ i :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h_align_all
  have h_fst : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ E.parts, p.1 ∈ S :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst E.ae_covers
  have h_snd : ∀ᵐ p ∂(μ.prod μ), ∃ S ∈ E.parts, p.2 ∈ S :=
    QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd E.ae_covers
  have h_pb_ae (i : ι) : ∀ᵐ p ∂(μ.prod μ),
      (pullback (V_QR i) e he).toAEEqFun p = (netMap f i).toAEEqFun p := by
    have h_pb := pullback_ae (V_QR i) (⇑e) he
    have h_net : ∀ᵐ p ∂(μ.prod μ),
        (netMap f i).toAEEqFun p = mkStepFun E (toCoeff f i) p := AEEqFun.coeFn_mk _ _
    have h_vr : ∀ᵐ p ∂(μ.prod μ),
        (V_QR i).toAEEqFun p = mkStepFun Q (roundCQ i) p := AEEqFun.coeFn_mk _ _
    have h_vr_image : ∀ᵐ p ∂(μ.prod μ),
        (V_QR i).toAEEqFun (e p.1, e p.2) =
          mkStepFun Q (roundCQ i) (e p.1, e p.2) :=
      (MeasurePreserving.prod he he).quasiMeasurePreserving.ae h_vr
    filter_upwards [h_pb, h_net, h_vr_image, h_fst, h_snd, h_e_fst, h_e_snd]
      with p h_pb h_net h_vr_image ⟨S₁, hS₁, hpS₁⟩ ⟨S₂, hS₂, hpS₂⟩ h_ef h_es
    rw [h_pb]
    have hpi₁ : p.1 ∈ ιE (eqE.symm ⟨S₁, hS₁⟩) := by
      show p.1 ∈ ((eqE (eqE.symm ⟨S₁, hS₁⟩)) : Set Ω)
      rw [Equiv.apply_symm_apply]; exact hpS₁
    have hpi₂ : p.2 ∈ ιE (eqE.symm ⟨S₂, hS₂⟩) := by
      show p.2 ∈ ((eqE (eqE.symm ⟨S₂, hS₂⟩)) : Set Ω)
      rw [Equiv.apply_symm_apply]; exact hpS₂
    have heQ₁ : e p.1 ∈ ιQ (eqE.symm ⟨S₁, hS₁⟩) := h_ef _ hpi₁
    have heQ₂ : e p.2 ∈ ιQ (eqE.symm ⟨S₂, hS₂⟩) := h_es _ hpi₂
    have h_vr_val : (V_QR i).toAEEqFun (e p.1, e p.2)
        = roundCQ i (ιQ (eqE.symm ⟨S₁, hS₁⟩)) (ιQ (eqE.symm ⟨S₂, hS₂⟩)) := by
      rw [h_vr_image]
      exact mkStepFun_eq_at Q (roundCQ i) (hιQ_mem _) (hιQ_mem _)
        (Set.mem_prod.mpr ⟨heQ₁, heQ₂⟩)
    rw [h_vr_val, h_net,
      mkStepFun_eq_at E (toCoeff f i) hS₁ hS₂ (Set.mem_prod.mpr ⟨hpS₁, hpS₂⟩),
      h_coeff_eq i S₁ hS₁ S₂ hS₂]
  have h_cn_pb (i : ι) : cutNormDiff (pullback (V_QR i) e he) (netMap f i) = 0 := by
    apply le_antisymm
    · unfold cutNormDiff rectIntegralDiff
      apply Real.iSup_le _ le_rfl; intro S'
      apply Real.iSup_le _ le_rfl; intro hS'
      apply Real.iSup_le _ le_rfl; intro T'
      apply Real.iSup_le _ le_rfl; intro hT'
      have h_zero_ae : ∀ᵐ p ∂(μ.prod μ),
          (pullback (V_QR i) e he).toAEEqFun p - (netMap f i).toAEEqFun p = 0 := by
        filter_upwards [h_pb_ae i] with p hp; rw [hp, sub_self]
      rw [setIntegral_congr_ae (hS'.prod hT') (h_zero_ae.mono (fun p hp _ => hp))]
      simp
    · exact cutNormDiff_nonneg _ _
  refine ⟨netMap f, hf_mem, e, he, ?_⟩
  intro i
  have h1 := cutNormDiff_triangle (pullback (W i) e he)
    (pullback (stepify P_W (W i)) e he) (netMap f i)
  have h2 := cutNormDiff_triangle (pullback (stepify P_W (W i)) e he)
    (pullback (V_avg i) e he) (netMap f i)
  have h3 := cutNormDiff_triangle (pullback (V_avg i) e he)
    (pullback (V_Q i) e he) (netMap f i)
  have h4 := cutNormDiff_triangle (pullback (V_Q i) e he)
    (pullback (V_QR i) e he) (netMap f i)
  have hstep := cutNormDiff_pullback_measurableEquiv (W i) (stepify P_W (W i)) e he
  have havg := cutNormDiff_pullback_measurableEquiv (stepify P_W (W i)) (V_avg i) e he
  have hreround := cutNormDiff_pullback_measurableEquiv (V_avg i) (V_Q i) e he
  have hgrid := cutNormDiff_pullback_measurableEquiv (V_Q i) (V_QR i) e he
  rw [hstep] at h1
  rw [havg] at h2
  rw [hreround] at h3
  rw [hgrid] at h4
  linarith [hP_W_close i, h_cn_stepavg i, h_cn_reround i, h_cn_grid i, h_cn_pb i,
    h1, h2, h3, h4]

end Erdos1017.GraphonFamily
