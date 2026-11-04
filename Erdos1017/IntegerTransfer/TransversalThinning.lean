module

public import Erdos1017.IntegerTransfer.BernoulliFamily
public import Erdos1017.IntegerTransfer.SharedBaseProducts
public import Mathlib.Data.Fintype.BigOperators

/-!
# Covariance of independently thinned transversal extensions

Thinning coordinates are increasing pairs of labeled vertices, each extension
has a support of required sampled edges with base edges omitted, at most
`u n^(u-1)` extensions share a coordinate with a fixed one, and this gives a
concrete covariance estimate (`variance_le`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u : ℕ}

/-- Independent thinning coordinates are increasing pairs of labelled vertices. -/
abbrev Coordinate (k : ℕ) (A : Type*) := (Fin k × A) × (Fin k × A)

/-- The graph-edge coordinate used by one pair of roles in an assignment. -/
def coordinate (X : Fin (t + u) → A) (e : Fin (t + u) × Fin (t + u)) :
    Coordinate (t + u) A := ((e.1, X e.1), (e.2, X e.2))

/-- Required sampled edges touching the extension, with base edges omitted. -/
def support (x : Fin t → A) (y : Fin u → A) : Finset (Coordinate (t + u) A) :=
  (SharedBasePattern.extensionEdges t u).image (coordinate (Fin.addCases x y))

omit [Fintype A] [DecidableEq A] in
theorem coordinate_injective (X : Fin (t + u) → A) : Function.Injective (coordinate X) := by
  intro e f h
  exact Prod.ext (congrArg (fun z => z.1.1) h) (congrArg (fun z => z.2.1) h)

omit [Fintype A] in
/-- Every assignment has one distinct coordinate for each extension edge. -/
theorem support_card (x : Fin t → A) (y : Fin u → A) :
    (support x y).card = (SharedBasePattern.extensionEdges t u).card := by
  exact Finset.card_image_of_injective _ (coordinate_injective _)

omit [Fintype A] in
/-- Shared sampled edges force agreement in at least one extension role.
The common base alone cannot create covariance because its edges were omitted. -/
theorem agreement_of_not_disjoint (x : Fin t → A) (y z : Fin u → A)
    (h : ¬Disjoint (support x y) (support x z)) : ∃ i, y i = z i := by
  obtain ⟨v, hvy, hvz⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨e, he, hey⟩ := Finset.mem_image.mp hvy
  obtain ⟨f, _, hfz⟩ := Finset.mem_image.mp hvz
  have hef : e = f := by
    apply Prod.ext
    · exact (congrArg (fun q => q.1.1) hey).trans (congrArg (fun q => q.1.1) hfz).symm
    · exact (congrArg (fun q => q.2.1) hey).trans (congrArg (fun q => q.2.1) hfz).symm
  subst f
  have hedge := (Finset.mem_filter.mp he).2
  have hvalue := (congrArg (fun q => q.2.2) hey).trans (congrArg (fun q => q.2.2) hfz).symm
  have hext : t ≤ e.2.val := by
    have horder := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
    omega
  let i : Fin u := ⟨e.2.val - t, by omega⟩
  have hi : Fin.natAdd t i = e.2 := by apply Fin.ext; dsimp [i]; omega
  refine ⟨i, ?_⟩
  change (Fin.addCases x y : Fin (t + u) → A) e.2 =
    (Fin.addCases x z : Fin (t + u) → A) e.2 at hvalue
  simp only [← hi, Fin.addCases_right] at hvalue
  exact hvalue

/-- Fixing one extension coordinate leaves exactly n^(u−1) assignments. -/
theorem agreement_fibre_card (i : Fin u) (a : A) :
    (Finset.univ.filter (fun z : Fin u → A => z i = a)).card = Fintype.card A ^ (u - 1) := by
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin] using
    Fintype.card_filter_piFinset_const_eq_of_mem (ι := Fin u) Finset.univ i (Finset.mem_univ a)

/-- At most u n^(u−1) extensions share a coordinate with a fixed extension. -/
theorem overlap_card_le (F : Finset (Fin u → A)) (x : Fin t → A) (y : Fin u → A) :
    (F.filter (fun z => ¬Disjoint (support x y) (support x z))).card ≤
      u * Fintype.card A ^ (u - 1) := by
  have hsub : F.filter (fun z => ¬Disjoint (support x y) (support x z)) ⊆
      Finset.univ.biUnion (fun i : Fin u => Finset.univ.filter (fun z : Fin u → A => z i = y i)) := by
    intro z hz
    obtain ⟨i, hi⟩ := agreement_of_not_disjoint x y z (Finset.mem_filter.mp hz).2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.symm⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin u, (Finset.univ.filter (fun z : Fin u → A => z i = y i)).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [agreement_fibre_card, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]

/-- Concrete covariance estimate for independently thinned transversal extensions. -/
theorem variance_le (F : Finset (Fin u → A)) (x : Fin t → A)
    (p : Coordinate (t + u) A → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) :
    (∑ X, CliqueSampling.weight p X *
      (((BernoulliFamily.retained F (support x) X).card : ℝ) - BernoulliFamily.mean F (support x) p) ^ 2) ≤
      F.card * ((u : ℝ) * (Fintype.card A : ℝ) ^ (u - 1)) := by
  apply BernoulliFamily.variance_le F (support x) p hp
  intro y _
  exact_mod_cast overlap_card_le F x y

end Erdos1017.TransversalThinning
