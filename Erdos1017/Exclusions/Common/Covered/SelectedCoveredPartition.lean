module

public import Erdos1017.Exclusions.Common.Covered.SelectedCoveredTopology
public import Erdos1017.Exclusions.Common.ZeroBody.SelectedZeroBodyUniversal
public import Erdos1017.SelectedModel.Structure.HalfGraphMultipartiteSupport

/-!
# The covered label partition

This module defines `coveredLabel`, keeping every independent atom and splitting
the diffuse part into the saturated head's neighborhood and complement, and the
label graph `coveredGraph`, and shows on one product-law event that this graph
describes the original adjacency on all atom and atom-diffuse blocks.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- All original independent atoms retain their labels. Only the diffuse
part is split into the saturated head's neighborhood and its complement. -/
def coveredLabel (S : SelectedHighLowStructure W m) (a : S.I) (x : Ω) : S.I ⊕ Bool :=
  if h : S.ρ x ∈ S.I then Sum.inl ⟨S.ρ x, h⟩
  else Sum.inr (decide (x ∈ S.rootNeighborhood a))

/-- The literal label graph retains every exterior independent atom. -/
def coveredGraph (S : SelectedHighLowStructure W m) (r a : S.I) :
    S.I ⊕ Bool → S.I ⊕ Bool → Bool
  | Sum.inl u, Sum.inl v => decide (u ≠ v ∧ (u ≠ a ∨ v = r) ∧ (v ≠ a ∨ u = r))
  | Sum.inl u, Sum.inr b => decide (u ≠ a ∨ b = true)
  | Sum.inr b, Sum.inl u => decide (u ≠ a ∨ b = true)
  | Sum.inr _, Sum.inr _ => true

theorem coveredGraph_symm (S : SelectedHighLowStructure W m) (r a : S.I)
    (i j : S.I ⊕ Bool) : S.coveredGraph r a i j = S.coveredGraph r a j i := by
  cases i with
  | inl u =>
    cases j with
    | inl v => simp only [coveredGraph]; congr 1; exact propext (by simp only [ne_comm, and_comm])
    | inr b => rfl
  | inr b => cases j <;> rfl

theorem coveredLabel_eq_inl_iff (S : SelectedHighLowStructure W m) (a u : S.I) (x : Ω) :
    S.coveredLabel a x = Sum.inl u ↔ S.ρ x = u.val := by
  by_cases hx : S.ρ x ∈ S.I
  · simp only [coveredLabel, hx, ↓reduceDIte, Sum.inl.injEq, Subtype.ext_iff]
  · simp only [coveredLabel, hx, ↓reduceDIte, reduceCtorEq, false_iff]
    exact fun he => hx (he.symm ▸ u.property)

theorem coveredLabel_eq_inr_iff (S : SelectedHighLowStructure W m) (a : S.I)
    (x : Ω) (b : Bool) : S.coveredLabel a x = Sum.inr b ↔
      x ∈ S.D ∧ decide (x ∈ S.rootNeighborhood a) = b := by
  have hD : x ∈ S.D ↔ S.ρ x ∉ S.I := by
    rw [S.hDeq]
    simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro h hi; exact h ⟨S.ρ x, hi, rfl⟩
    · rintro h ⟨u, hu, he⟩; exact h (he ▸ hu)
  by_cases hx : S.ρ x ∈ S.I <;> simp [coveredLabel, hx, hD]

theorem coveredLabel_fiber_inl (S : SelectedHighLowStructure W m) (a u : S.I) :
    (S.coveredLabel a) ⁻¹' {Sum.inl u} = {x | S.ρ x = u.val} := by
  ext x
  exact S.coveredLabel_eq_inl_iff a u x

theorem coveredLabel_fiber_true (S : SelectedHighLowStructure W m) (a : S.I) :
    (S.coveredLabel a) ⁻¹' {Sum.inr true} = S.D ∩ S.rootNeighborhood a := by
  ext x
  simpa only [mem_preimage, mem_singleton_iff, decide_eq_true_eq, mem_inter_iff] using
    S.coveredLabel_eq_inr_iff a x true

theorem coveredLabel_fiber_false (S : SelectedHighLowStructure W m) (a : S.I) :
    (S.coveredLabel a) ⁻¹' {Sum.inr false} = S.D \ S.rootNeighborhood a := by
  ext x
  simpa only [mem_preimage, mem_singleton_iff, decide_eq_false_iff_not, Set.mem_sdiff] using
    S.coveredLabel_eq_inr_iff a x false

theorem measurable_coveredLabel (S : SelectedHighLowStructure W m) (a : S.I) :
    @Measurable Ω (S.I ⊕ Bool) _ ⊤ (S.coveredLabel a) := by
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  let : MeasurableSpace (S.I ⊕ Bool) := ⊤
  let : Countable S.I := S.hI.to_subtype
  let s := {x | S.ρ x ∈ S.I}
  have hs : MeasurableSet s := S.hρ.measurable S.hI.measurableSet
  have hr : Measurable (fun x : s => (Sum.inl (⟨S.ρ x, x.property⟩ : S.I) : S.I ⊕ Bool)) :=
    (measurable_of_countable (Sum.inl : S.I → S.I ⊕ Bool)).comp
      ((S.hρ.measurable.comp measurable_subtype_coe).subtype_mk)
  have hb : Measurable (fun x : Ω => decide (x ∈ S.rootNeighborhood a)) :=
    measurable_to_bool (by
      convert S.measurableSet_rootNeighborhood a using 1
      ext x
      simp)
  have hd : Measurable (fun x : (sᶜ : Set Ω) =>
      (Sum.inr (decide ((x : Ω) ∈ S.rootNeighborhood a)) : S.I ⊕ Bool)) :=
    (measurable_of_countable (Sum.inr : Bool → S.I ⊕ Bool)).comp (hb.comp measurable_subtype_coe)
  convert hr.dite hd hs using 1
  funext x
  by_cases hx : S.ρ x ∈ S.I <;> simp [coveredLabel, s, hx]

/-- Positivity is required only for the two diffuse regions; every
original atom's positive mass is already part of the selected structure. -/
theorem coveredLabel_fibers_positive (S : SelectedHighLowStructure W m) (a : S.I)
    (hR : 0 < μ (S.D ∩ S.rootNeighborhood a))
    (hE : 0 < μ (S.D \ S.rootNeighborhood a)) (i : S.I ⊕ Bool) :
    0 < μ ((S.coveredLabel a) ⁻¹' {i}) := by
  cases i with
  | inl u => rw [S.coveredLabel_fiber_inl]; exact (S.hfibers u.val u.property).2.1
  | inr b =>
    cases b
    · rwa [S.coveredLabel_fiber_false]
    · rwa [S.coveredLabel_fiber_true]

variable [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [MetricSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

/-- The covered graph describes the actual original adjacency on every
pair of original independent atoms, including a countably infinite family. -/
theorem ae_covered_atom_blocks (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, ∀ u v : S.I, S.ρ p.1 = u.val → S.ρ p.2 = v.val →
      adjacencyKernel W p.1 p.2 =
        if S.coveredGraph r a (Sum.inl u) (Sum.inl v) = true then 1 else 0 := by
  let : Countable S.I := S.hI.to_subtype
  let : MeasurableSpace (Lp ℝ 2 μ) := borel _
  let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  have hsame := HalfGraphMultipartite.ae_sameAtom_adjacency_zero
    (adjacencyKernel W) S.ρ S.hρ.measurable S.I S.hI
    (fun u hu => (S.hfibers u hu).2.2.1)
  have hroot : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = r.val → S.ρ p.2 ≠ r.val →
      adjacencyKernel W p.1 p.2 = 1 := by
    filter_upwards [S.ae_root_universal_of_zero_body r hW hd hgap hzero,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hr hg hx hy
    simpa [adjacencyKernel, (hr hx).mpr hy] using hg
  have hroots := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hroot
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro v
  by_cases huv : u = v
  · filter_upwards [hsame] with p hp hx hy
    have hz := hp ⟨u.val, u.property, hx, huv ▸ hy⟩
    simpa [coveredGraph, huv] using hz
  by_cases hur : u = r
  · filter_upwards [hroot] with p hp hx hy
    have hn : S.ρ p.2 ≠ r.val := fun he => huv (hur.trans (Subtype.ext (he.symm.trans hy)))
    have he := hp (hx.trans (congrArg Subtype.val hur)) hn
    simpa [coveredGraph, hur, hpair.1, Ne.symm hpair.1, show r ≠ v from hur ▸ huv] using he
  by_cases hvr : v = r
  · filter_upwards [hroots, adjacencyKernel_symm W] with p hp hs hx hy
    have hn : S.ρ p.1 ≠ r.val := fun he => hur (Subtype.ext (hx.symm.trans he))
    have he := hs.trans (hp (hy.trans (congrArg Subtype.val hvr)) hn)
    simpa [coveredGraph, hvr, hpair.1, Ne.symm hpair.1, hur] using he
  by_cases hua : u = a
  · have hz := S.ae_saturated_head_atom_adjacency_zero_of_zero_body
      r a v (Ne.symm hvr) hW hd hgap hN hpair hzero
    filter_upwards [hz] with p hp hx hy
    have he := hp (hx.trans (congrArg Subtype.val hua)) hy
    simpa [coveredGraph, hua, hvr] using he
  by_cases hva : v = a
  · have hz := S.ae_saturated_head_atom_adjacency_zero_of_zero_body
      r a u (Ne.symm hur) hW hd hgap hN hpair hzero
    have hzs := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hz
    filter_upwards [hzs, adjacencyKernel_symm W] with p hp hs hx hy
    have he := hs.trans (hp (hy.trans (congrArg Subtype.val hva)) hx)
    simpa [coveredGraph, hva, hur] using he
  filter_upwards [S.ae_exterior_atoms_adjacent_of_zero_body r a u v
    (Ne.symm hur) (Ne.symm hua) (Ne.symm hvr) (Ne.symm hva) huv hW hd hgap hN hpair hzero]
    with p hp hx hy
  simpa [coveredGraph, huv, hua, hva] using hp hx hy

/-- The original diffuse blocks also have the literal covered graph
pattern; the head's split is by its actual measurable neighborhood. -/
theorem ae_covered_atom_diffuse_blocks (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, ∀ u : S.I, S.ρ p.1 = u.val → p.2 ∈ S.D →
      adjacencyKernel W p.1 p.2 = if u ≠ a ∨ p.2 ∈ S.rootNeighborhood a then 1 else 0 := by
  let : Countable S.I := S.hI.to_subtype
  have hN := S.root_neutral_of_zero_body r hW hd hgap hzero
  apply ae_all_iff.mpr
  intro u
  by_cases hua : u = a
  · filter_upwards [S.ae_original_root_adjacency a hW hd hgap] with p hp hx _
    simpa [hua] using hp (hx.trans (congrArg Subtype.val hua))
  by_cases hur : u = r
  · filter_upwards [S.ae_root_universal_of_zero_body r hW hd hgap hzero,
      PhysicalRepresentative.adjacency_moment_ae_eq W m
        (hW.strict_gap_structure hd hgap).strict_support] with p hp hg hx hy
    have he := (hp (hx.trans (congrArg Subtype.val hur))).mpr
      (S.row_ne_atom_of_mem_diffuse p.2 hy r)
    simpa [adjacencyKernel, hua, he] using hg
  filter_upwards [S.ae_exterior_atom_sees_diffuse_of_zero_body
    r a u (Ne.symm hur) (Ne.symm hua) hW hd hgap hN hpair hzero] with p hp hx hy
  simpa [hua] using hp hx hy

/-- One original product-law event identifies the complete countable
covered graph. No exterior atom is removed or assumed absent. -/
theorem ae_covered_graph (S : SelectedHighLowStructure W m) (r a : S.I)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hpair : S.IsSaturatedAtomPair r a)
    (hzero : PhysicalPrimal.bodyPositiveEnergy μ (Function.uncurry (chargeKernel W))
      {x | S.ρ x = r.val} = 0) :
    ∀ᵐ p ∂μ.prod μ, adjacencyKernel W p.1 p.2 =
      if S.coveredGraph r a (S.coveredLabel a p.1) (S.coveredLabel a p.2) = true then 1 else 0 := by
  have had := S.ae_covered_atom_diffuse_blocks r a hW hd hgap hpair hzero
  have hda := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae had
  filter_upwards [S.ae_covered_atom_blocks r a hW hd hgap hpair hzero,
    had, hda, S.hDcomplete, adjacencyKernel_symm W] with p haa had hda hdd hsym
  generalize hqx : S.coveredLabel a p.1 = i
  generalize hqy : S.coveredLabel a p.2 = j
  cases i with
  | inl u =>
    have hx := (S.coveredLabel_eq_inl_iff a u p.1).mp hqx
    cases j with
    | inl v => exact haa u v hx ((S.coveredLabel_eq_inl_iff a v p.2).mp hqy)
    | inr b =>
      obtain ⟨hy, hb⟩ := (S.coveredLabel_eq_inr_iff a p.2 b).mp hqy
      have he := had u hx hy
      simpa only [coveredGraph, decide_eq_true_eq, ← hb, decide_eq_true_eq, Prod.swap] using he
  | inr b =>
    obtain ⟨hx, hb⟩ := (S.coveredLabel_eq_inr_iff a p.1 b).mp hqx
    cases j with
    | inl v =>
      have hy := (S.coveredLabel_eq_inl_iff a v p.2).mp hqy
      have he := hsym.trans (hda v hy hx)
      simpa only [coveredGraph, decide_eq_true_eq, ← hb, decide_eq_true_eq, Prod.swap] using he
    | inr e =>
      have hy := ((S.coveredLabel_eq_inr_iff a p.2 e).mp hqy).1
      simpa only [coveredGraph, ↓reduceIte, adjacencyKernel] using hdd hx hy

end Erdos1017.CappedModel.SelectedHighLowStructure
