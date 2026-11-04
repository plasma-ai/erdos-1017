module

public import Erdos1017.Exclusions.Common.SelectedAtomicChargeBlocks
public import Erdos1017.Exclusions.Common.SelectedRepeatDiffuseContext

/-!
# Bare repeat witness in the zero-body case

In the zero-body case the two-copy witness reduces to the bare universal root,
and any two exterior atoms are mutually nonadjacent once the bare thresholds are
paid.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableEq Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ}

/-- The actual original two-copy witness reduces to the bare universal
root. Its possible last exterior point is removed using the genuine root
triangle and the original strict half-delta penalty on the same tuple. -/
theorem zero_body_bare_repeat (S : SelectedHighLowStructure W m) (r u : S.I)
    (hru : r ≠ u) {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    -m < 2 * S.coveredCountableBoundaryCoefficient (Sum.inl r) (Sum.inl u) - 1 := by
  let A := PhysicalRepresentative.adjacency W m
  let Y := PhysicalRepresentative.charge W m
  let t := S.coveredCountableBoundaryCoefficient (Sum.inl u) (Sum.inl r)
  have hs := hW.strict_gap_structure hd hgap
  have hpenalty : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val →
      A p.1 p.2 = true → Y p.1 p.2 < -(1 + m) / 2 := by
    filter_upwards [S.ae_body_penalty_gt_half_delta_of_zero_body r hW hd hgap hzero hratio,
      PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
      PhysicalRepresentative.charge_ae_eq W m hs.strict_support] with p hp hg hy hx hz ha
    have hG : adjacencyKernel W p.1 p.2 = 1 := by
      change W.moment CappedColor.adjacency p = 1
      change PhysicalRepresentative.adjacency W m p.1 p.2 = true at ha
      simpa only [ha, ite_true] using hg
    change Y p.1 p.2 = chargeKernel W p.1 p.2 at hy
    linarith [hp hx hz hG]
  let P : Ω × Ω → Prop := fun p =>
    (S.ρ p.1 = r.val → S.ρ p.2 = r.val → A p.1 p.2 = false) ∧
    (S.ρ p.1 = u.val → S.ρ p.2 = u.val → A p.1 p.2 = false) ∧
    (S.ρ p.1 = u.val → Y p.1 p.2 = S.rootChargeRow u p.2) ∧
    (S.ρ p.1 = r.val → Y p.1 p.2 = S.rootChargeRow r p.2) ∧
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → A p.1 p.2 = true →
      S.rootChargeRow r p.1 + S.rootChargeRow r p.2 + Y p.1 p.2 ≤ 1) ∧
    (S.ρ p.1 ≠ r.val → S.ρ p.2 ≠ r.val → A p.1 p.2 = true →
      Y p.1 p.2 < -(1 + m) / 2)
  have hP : ∀ᵐ p ∂μ.prod μ, P p :=
    (S.ae_root_fiber_physical_independent r hW hd hgap).and
      ((S.ae_root_fiber_physical_independent u hW hd hgap).and
        ((S.ae_root_charge u hW hd hgap).and ((S.ae_root_charge r hW hd hgap).and
          ((S.ae_universal_root_triangle r hW hd hgap
            (S.root_neutral_of_zero_body r hW hd hgap hzero)).and hpenalty))))
  let Vx := fun x : Ω =>
    (S.ρ x = r.val → S.rootChargeRow u x = t) ∧
    (S.ρ x = u.val → S.rootChargeRow r x = t)
  have hVx : ∀ᵐ x ∂μ, Vx x := by
    have h₁ := (ae_restrict_iff' (S.hfibers r.val r.property).1).mp
      (S.ae_atomic_rootChargeRow u r hW hd hgap)
    have h₂ := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
      (S.ae_atomic_rootChargeRow r u hW hd hgap)
    filter_upwards [h₁, h₂] with x h₁ h₂
    exact ⟨h₁, fun hx => (h₂ hx).trans
      (S.coveredCountableBoundaryCoefficient_symm (Sum.inl r) (Sum.inl u))⟩
  let Good : ∀ n, (Fin n → Ω) → Prop := fun _ cfg =>
    (∀ i j, i ≠ j → P (cfg i, cfg j)) ∧ ∀ i, Vx (cfg i)
  have hGood (n : ℕ) : ∀ᵐ cfg ∂Measure.pi (fun _ : Fin n => μ), Good n cfg := by
    have hv : ∀ᵐ cfg ∂Measure.pi (fun _ : Fin n => μ), ∀ i, Vx (cfg i) := by
      apply ae_all_iff.mpr
      intro i
      exact (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae hVx
    exact (FiniteArity.ae_all_pairs μ n P hP).and hv
  obtain ⟨n, _, cfg, hclique, hgood, T, hTC, hcard, hbad, hinc, ⟨b, hb, hbR⟩, hsmall, _⟩ :=
    S.exists_root_diffuse_completion_witness r u hru hW hd hgap hell hzero hratio Good hGood
  let E := Finset.univ.filter (fun i : Fin n => cfg i ∉ {x | S.ρ x = u.val})
  let Z := fun i j : Fin n => if i = j then 0 else
    FiniteArity.completeCharge A Y {x | S.ρ x = u.val} (-m) (cfg i) (cfg j)
  have hE (i : Fin n) (hi : i ∈ E) : S.ρ (cfg i) ≠ u.val := (Finset.mem_filter.mp hi).2
  have hT (i : Fin n) (hi : i ∈ T) : S.ρ (cfg i) = u.val := (Finset.mem_filter.mp (hTC hi)).2
  have hrootUnique {i : Fin n} (hi : i ∈ E) (hiR : S.ρ (cfg i) = r.val) : i = b := by
    by_contra hib
    have hz := (hgood.1 i b hib).1 hiR hbR
    have hDD : ¬(cfg i ∈ {x | S.ρ x = u.val} ∧ cfg b ∈ {x | S.ρ x = u.val}) :=
      fun h => hE i hi h.1
    have hc : A (cfg i) (cfg b) = true := by
      simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique i b hib
    rw [hc] at hz
    contradiction
  have hdiag (i : Fin n) : Z i i = 0 := by simp [Z]
  have hsym (i j : Fin n) : Z i j = Z j i := by
    by_cases hij : i = j
    · simp [Z, hij]
    · simp only [Z, hij, Ne.symm hij, ite_false, FiniteArity.completeCharge,
        PhysicalRepresentative.adjacency_symm W m (cfg i) (cfg j),
        PhysicalRepresentative.charge_symm W m (cfg i) (cfg j), A, Y]
      congr 1
      exact propext (by tauto)
  have hdisj : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    exact fun i hi he => hE i he (hT i hi)
  have hcell (i : Fin n) (hi : i ∈ T) (j : Fin n) (hj : j ∈ T) (hij : i ≠ j) :
      Z i j = -(-m) := by
    have hz := (hgood.1 i j hij).2.1 (hT i hi) (hT j hj)
    simp [Z, hij, FiniteArity.completeCharge, hT i hi, hT j hj, hz]
  have hrow (i : Fin n) (hi : i ∈ T) (j : Fin n) (hj : j ∈ E) :
      Z i j = S.rootChargeRow u (cfg j) := by
    have hij : i ≠ j := fun he => hE j hj (he ▸ hT i hi)
    simp only [Z, hij, ite_false, FiniteArity.completeCharge, Set.mem_ofPred_eq,
      hE j hj, and_false, false_and, ite_false]
    exact (hgood.1 i j hij).2.2.1 (hT i hi)
  have hformula := FiniteArity.pairCharge_homogeneous_cell T E hdisj Z hdiag hsym (-m)
    (fun i => S.rootChargeRow u (cfg i)) hcell hrow
  change 1 < FiniteArity.pairCharge (T ∪ E) Z at hbad
  rw [hformula, hcard] at hbad
  norm_num only [Nat.cast_ofNat] at hbad
  have hwb : S.rootChargeRow u (cfg b) = t := (hgood.2 b).1 hbR
  have hbare : -m < 2 * t - 1 := by
    by_cases hex : ∃ j ∈ E, S.ρ (cfg j) ≠ r.val
    · obtain ⟨j, hj, hjR⟩ := hex
      have hjb : j ≠ b := fun he => hjR (he ▸ hbR)
      have hEeq : E = {b, j} := by
        ext i
        constructor
        · intro hi
          by_cases hiR : S.ρ (cfg i) = r.val
          · simp [hrootUnique hi hiR]
          · have he := Finset.card_le_one.mp hsmall i (Finset.mem_filter.mpr ⟨hi, hiR⟩)
              j (Finset.mem_filter.mpr ⟨hj, hjR⟩)
            simp [he]
        · intro hi
          rcases Finset.mem_insert.mp hi with he | he
          · exact he ▸ hb
          · exact (Finset.mem_singleton.mp he) ▸ hj
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
      have haU := hT a ha
      have haR : S.ρ (cfg a) ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans haU))
      have haj : a ≠ j := fun he => hE j hj (he ▸ haU)
      have hDD : ¬(cfg a ∈ {x | S.ρ x = u.val} ∧ cfg j ∈ {x | S.ρ x = u.val}) :=
        fun h => hE j hj h.2
      have hA : A (cfg a) (cfg j) = true := by
        simpa only [FiniteArity.completeAdjacency, ite_eq_right hDD] using hclique a j haj
      have htriangle := (hgood.1 a j haj).2.2.2.2.1 haR hjR hA
      have hpen := (hgood.1 a j haj).2.2.2.2.2 haR hjR hA
      have hY := (hgood.1 a j haj).2.2.1 haU
      rw [(hgood.2 a).2 haU, hY] at htriangle
      rw [hY] at hpen
      have hZj : Z b j = S.rootChargeRow r (cfg j) := by
        simp only [Z, Ne.symm hjb, ite_false, FiniteArity.completeCharge,
          Set.mem_ofPred_eq, hE b hb, false_and]
        exact (hgood.1 b j (Ne.symm hjb)).2.2.2.1 hbR
      have hpair : FiniteArity.pairCharge {b, j} Z = S.rootChargeRow r (cfg j) := by
        simp [FiniteArity.pairCharge, FiniteArity.crossSum, hdiag, hsym j b,
          Ne.symm hjb, hZj]
      rw [hEeq, hpair] at hbad
      change -m < ∑ i ∈ E, S.rootChargeRow u (cfg i) at hinc
      rw [hEeq] at hinc
      simp only [Finset.sum_pair (Ne.symm hjb), hwb] at hbad hinc
      linarith
    · have hEeq : E = {b} := by
        ext i
        constructor
        · intro hi
          exact Finset.mem_singleton.mpr (hrootUnique hi (by
            by_contra hn
            exact hex ⟨i, hi, hn⟩))
        · intro hi
          exact (Finset.mem_singleton.mp hi) ▸ hb
      have hpair : FiniteArity.pairCharge {b} Z = 0 := by
        simp [FiniteArity.pairCharge, FiniteArity.crossSum, hdiag]
      rw [hEeq, hpair] at hbad
      simp only [Finset.sum_singleton, hwb] at hbad
      linarith
  simpa only [t, S.coveredCountableBoundaryCoefficient_symm (Sum.inl u) (Sum.inl r)] using hbare

/-- Every two original exterior atoms are mutually nonadjacent once the
actual bare thresholds are paid. The original rooted triangle and strict
support are retained on one product event, with no diagonal evaluations. -/
theorem ae_exterior_atomic_blocks_missing_of_zero_body
    (S : SelectedHighLowStructure W m) (r u v : S.I) (hru : r ≠ u) (hrv : r ≠ v)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hell : 1 / 2 < -m)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0)
    (hratio : μ.real {x | S.ρ x = r.val} * (1 + m) < 2 * (2 * (c - m * d) + m)) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → S.ρ p.2 = v.val →
      adjacencyKernel W p.1 p.2 = 0 := by
  have hu := S.zero_body_bare_repeat r u hru hW hd hgap hell hzero hratio
  have hv := S.zero_body_bare_repeat r v hrv hW hd hgap hell hzero hratio
  have hU := (ae_restrict_iff' (S.hfibers u.val u.property).1).mp
    (S.ae_atomic_rootChargeRow r u hW hd hgap)
  have hV := (ae_restrict_iff' (S.hfibers v.val v.property).1).mp
    (S.ae_atomic_rootChargeRow r v hW hd hgap)
  have hs := hW.strict_gap_structure hd hgap
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hU,
    Measure.quasiMeasurePreserving_snd.ae hV,
    S.ae_universal_root_triangle r hW hd hgap
      (S.root_neutral_of_zero_body r hW hd hgap hzero), hs.strict_support,
    PhysicalRepresentative.adjacency_moment_ae_eq W m hs.strict_support,
    PhysicalRepresentative.charge_ae_eq W m hs.strict_support]
    with p hU hV htri hstrict hphys hY hx hy
  have hxR : S.ρ p.1 ≠ r.val := fun he => hru (Subtype.ext (he.symm.trans hx))
  have hyR : S.ρ p.2 ≠ r.val := fun he => hrv (Subtype.ext (he.symm.trans hy))
  by_cases hpos : 0 < shiftedMoment W m p
  · have hG : W.moment CappedColor.adjacency p = 1 := by simpa only [hpos, ite_true] using hstrict
    have hA : PhysicalRepresentative.adjacency W m p.1 p.2 = true := by
      rw [hG] at hphys
      cases he : PhysicalRepresentative.adjacency W m p.1 p.2
      · simp only [he, Bool.false_eq_true, ite_false] at hphys
        norm_num at hphys
      · rfl
    have ht := htri hxR hyR hA
    rw [hU hx, hV hy, hY] at ht
    rw [shiftedMoment_eq, hG] at hpos
    change 0 < chargeKernel W p.1 p.2 - m * 1 at hpos
    linarith
  · change W.moment CappedColor.adjacency p = 0
    simpa only [hpos, ite_false] using hstrict

end Erdos1017.CappedModel.SelectedHighLowStructure
