module

public import Erdos1017.Exclusions.Common.CliqueStarVariation
public import Erdos1017.Exclusions.Common.TwoCenter.SelectedTwoCenterAtomLocation

/-!
# Geometry of a private peak cover

The cover `privatePeakCover` is the private pattern outside a chosen atom
together with the outside region; a private atom is neither recovered head,
misses the first head and sees the second, its second-head common neighbors lie
in the cover, and the cover mass is bounded.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  {W : Model Ω μ} {m : ℝ} {S : SelectedHighLowStructure W m}
  (R : S.ReverseRecovery)

/-- The private pattern outside the chosen original atom, together with
the entire original outside region. All masses use the original law. -/
def privatePeakCover (k r u : S.I) : Set Ω :=
  (S.twoCenterPrivate r u \ {x | S.ρ x = k.val}) ∪ R.outsidePlateauSource

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ] in
theorem measurableSet_privatePeakCover (k r u : S.I) (hp : R.plateau = {r, u}) :
    MeasurableSet (R.privatePeakCover k r u) :=
  (((R.measurableSet_twoCenter_patterns r u hp).1).diff
    (S.hfibers k.val k.property).1).union R.measurableSet_outsidePlateauSource

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- A positive original atom in the private HIGH source is neither of the
recovered original heads, which lie outside HIGH almost everywhere. -/
theorem private_atom_ne_heads (k r u : S.I) (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) :
    k ≠ r ∧ k ≠ u := by
  obtain ⟨x, _, hc, hx, hn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (S.hfibers k.val k.property).2.1.ne'
    (hprivate.and ((ae_restrict_mem (S.hfibers k.val k.property).1).and
      (ae_restrict_of_ae R.ae_plateau_not_high)))
  have hnot : x ∉ R.plateauRegion := fun h => hn h hc.1.1.1
  constructor
  · intro hkr
    apply hnot
    rw [R.plateauRegion_eq_pair r u hp]
    exact Or.inl (hx.trans (congrArg Subtype.val hkr))
  · intro hku
    apply hnot
    rw [R.plateauRegion_eq_pair r u hp]
    exact Or.inr (hx.trans (congrArg Subtype.val hku))

/-- A private original atom misses the first head and sees the second.
These are original product-AE blocks derived from the entire source. -/
theorem private_atom_head_blocks (k r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) :
    (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = r.val →
      adjacencyKernel W p.1 p.2 = 0) ∧
    (∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val → S.ρ p.2 = u.val →
      adjacencyKernel W p.1 p.2 = 1) := by
  have hg := R.twoCenter_retained_geometry r u hru hW hd hgap hp
  have hf := (ae_restrict_iff' (S.hfibers k.val k.property).1).mp hprivate
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving
  have he : ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = k.val →
      (S.ρ p.2 = r.val → adjacencyKernel W p.1 p.2 = 0) ∧
      (S.ρ p.2 = u.val → adjacencyKernel W p.1 p.2 = 1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hf,
      hs.ae hg.first_head_source, hs.ae hg.second_head_source,
      adjacencyKernel_symm W] with p hf hr hu hsym hk
    have hc := hf hk
    constructor
    · intro hpr
      have he := hr hpr hc.1.1
      change adjacencyKernel W p.2 p.1 =
        (if p.1 ∈ KernelOperator.wholeFiberMissingSet S.ρ r.val then 0 else 1) at he
      exact hsym.trans (by simpa only [hc.1.2, ite_true] using he)
    · intro hpu
      have he := hu hpu hc.1.1
      change adjacencyKernel W p.2 p.1 =
        (if p.1 ∈ KernelOperator.wholeFiberMissingSet S.ρ u.val then 0 else 1) at he
      exact hsym.trans (by simpa only [hc.2, ite_false] using he)
  exact ⟨he.mono (fun _ h hk => (h hk).1), he.mono (fun _ h hk => (h hk).2)⟩

/-- Every original second-head common neighbor of a private atom lies
in its private-pattern remainder or the original outside region. -/
theorem privatePeakCover_common_neighbors (k r u : S.I) (hru : r ≠ u) {d c : ℝ}
    (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) :
    ∀ᵐ p ∂μ.prod μ, S.ρ p.1 = u.val → p.2 ∈ S.rootNeighborhood k →
      p.2 ∉ R.privatePeakCover k r u → adjacencyKernel W p.1 p.2 = 0 := by
  have hg := R.twoCenter_retained_geometry r u hru hW hd hgap hp
  have hb := R.private_atom_head_blocks k r u hru hW hd hgap hp hprivate
  have hn := S.ae_rootNeighborhood_on_constant_block k r hW hd hgap false hb.1
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hn,
    hg.zero_second_head, hg.second_head_source] with p hn huu hus hu hk hout
  have hnot : p.2 ∉ S.twoCenterPrivate r u \ {x | S.ρ x = k.val} :=
    fun h => hout (Or.inl h)
  have ho : p.2 ∉ R.outsidePlateauSource := fun h => hout (Or.inr h)
  have hinside : p.2 ∈ R.plateauRegion ∪ S.reverseCompulsorySource R.plateau := by
    by_contra h
    exact ho h
  rcases hinside with hhead | hsource
  · rw [R.plateauRegion_eq_pair r u hp] at hhead
    rcases hhead with hr | hr
    · have hfalse := (hn hr).mp hk
      simp at hfalse
    · exact huu hu hr
  · rw [hp, S.twoCenter_source_partition r u] at hsource
    rcases hsource with (hfirst | hsecond) | hshared
    · by_cases hi : S.ρ p.2 = k.val
      · exact False.elim ((S.rootNeighborhood_disjoint k).le_bot ⟨hi, hk⟩)
      · exact False.elim (hnot ⟨hfirst, hi⟩)
    · have hc : p.2 ∈ S.reverseCompulsorySource {r, u} := by
        simpa only [Finset.pair_comm] using hsecond.1.1
      rw [hus hu hc]
      simp only [hsecond.1.2, ite_true]
    · rw [hus hu hshared.1.1]
      simp only [hshared.2, ite_true]

omit [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]
  [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] in
/-- The cover's mass is bounded using original pattern subtraction and
the exact original outside mass; retained endpoint weights are absent. -/
theorem privatePeakCover_mass_le (k r u : S.I) (hru : r ≠ u)
    (hp : R.plateau = {r, u})
    (hprivate : ∀ᵐ x ∂μ.restrict {x | S.ρ x = k.val}, x ∈ S.twoCenterPrivate r u) :
    μ.real (R.privatePeakCover k r u) ≤ μ.real (S.twoCenterPrivate r u) -
      μ.real {x | S.ρ x = k.val} + (1 - 2 * R.height) := by
  have hi := (S.hfibers k.val k.property).1
  have hsub := (ae_restrict_iff' hi).mp hprivate
  have hinter : μ.real (S.twoCenterPrivate r u ∩ {x | S.ρ x = k.val}) =
      μ.real {x | S.ρ x = k.val} := by
    apply measureReal_congr
    filter_upwards [hsub] with x hx
    exact propext ⟨fun h => h.2, fun h => ⟨hx h, h⟩⟩
  have hsplit := measureReal_sdiff_add_inter (μ := μ) (s := S.twoCenterPrivate r u) hi
  rw [hinter] at hsplit
  have hle := measureReal_union_le (μ := μ)
    (s₁ := S.twoCenterPrivate r u \ {x | S.ρ x = k.val}) (s₂ := R.outsidePlateauSource)
  rw [R.outsidePlateauSource_mass r u hru hp] at hle
  change μ.real ((S.twoCenterPrivate r u \ {x | S.ρ x = k.val}) ∪ R.outsidePlateauSource) ≤ _
  linarith

end Erdos1017.CappedModel.SelectedHighLowStructure.ReverseRecovery
