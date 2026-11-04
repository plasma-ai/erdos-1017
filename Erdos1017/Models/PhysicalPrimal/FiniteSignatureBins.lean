module

public import Erdos1017.Models.PhysicalPrimal.FiniteChargePartition

/-!
# Signature bins of a hub tuple

Vertices are grouped by their adjacency signature to a finite hub tuple; bins
below the retained cutoff are discarded, and the retained signatures form a
finite index type whose bins are disjoint, of bounded capacity, and together
with the discarded vertices cover everything.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Erdos1017.FiniteArity

variable {α σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Vertices sharing one adjacency signature to the finite hub tuple. -/
def signatureBin (U : Finset α) (signature : α → σ) (s : σ) : Finset α :=
  U.filter (fun a => signature a = s)

/-- Vertices lying in bins below the retained-bin cutoff. -/
def discarded (U : Finset α) (signature : α → σ) (B : ℕ) : Finset α :=
  U.filter (fun a => (signatureBin U signature (signature a)).card < B)

omit [Fintype σ] in
theorem signatureBin_disjoint (U : Finset α) (signature : α → σ) {s t : σ} (hst : s ≠ t) :
    Disjoint (signatureBin U signature s) (signatureBin U signature t) := by
  apply Finset.disjoint_left.mpr
  intro a ha ht
  exact hst ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp ht).2)

/-- At most B−1 vertices are discarded for each possible hub signature. -/
theorem discarded_card_le (U : Finset α) (signature : α → σ) (B : ℕ) :
    (discarded U signature B).card ≤ Fintype.card σ * (B - 1) := by
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := discarded U signature B) (t := Finset.univ) (f := signature)
    (fun a _ => Finset.mem_univ (signature a))
  rw [hcard]
  calc
    _ ≤ ∑ _ : σ, (B - 1) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : (signatureBin U signature s).card < B
      · have hsub : (discarded U signature B).filter (fun a => signature a = s) ⊆
            signatureBin U signature s := by
          intro a ha
          rcases Finset.mem_filter.mp ha with ⟨ha, has⟩
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, has⟩
        have hh := Finset.card_le_card hsub
        omega
      · have he : (discarded U signature B).filter (fun a => signature a = s) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          rcases Finset.mem_filter.mp ha with ⟨ha, has⟩
          have hsmall := (Finset.mem_filter.mp ha).2
          rw [has] at hsmall
          exact hs hsmall
        rw [he, Finset.card_empty]
        exact Nat.zero_le _
    _ = Fintype.card σ * (B - 1) := by simp

/-- The retained signatures form a finite index type without empty small-bin placeholders. -/
def RetainedIndex (U : Finset α) (signature : α → σ) (B : ℕ) :=
  {s : σ // B ≤ (signatureBin U signature s).card}

instance (U : Finset α) (signature : α → σ) (B : ℕ) : Fintype (RetainedIndex U signature B) :=
  inferInstanceAs (Fintype {s : σ // B ≤ (signatureBin U signature s).card})

def retainedBins (U : Finset α) (signature : α → σ) (B : ℕ)
    (i : Fin (Fintype.card (RetainedIndex U signature B))) : Finset α :=
  signatureBin U signature ((Fintype.equivFin (RetainedIndex U signature B)).symm i).val

theorem retainedBins_capacity (U : Finset α) (signature : α → σ) (B : ℕ)
    (i : Fin (Fintype.card (RetainedIndex U signature B))) :
    B ≤ (retainedBins U signature B i).card :=
  ((Fintype.equivFin (RetainedIndex U signature B)).symm i).property

theorem retainedIndex_card_le (U : Finset α) (signature : α → σ) (B : ℕ) :
    Fintype.card (RetainedIndex U signature B) ≤ Fintype.card σ :=
  Fintype.card_subtype_le _

theorem retainedBins_disjoint (U : Finset α) (signature : α → σ) (B : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin (Fintype.card (RetainedIndex U signature B)))))
      (retainedBins U signature B) := by
  intro i _ j _ hij
  apply signatureBin_disjoint
  intro hv
  have heq := Subtype.ext hv
  exact hij ((Fintype.equivFin (RetainedIndex U signature B)).symm.injective heq)

variable [DecidableEq α]

theorem retainedBins_union (U : Finset α) (signature : α → σ) (B : ℕ) :
    Finset.univ.biUnion (retainedBins U signature B) = U \ discarded U signature B := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi⟩
    have hh := Finset.mem_filter.mp hi
    refine ⟨hh.1, ?_⟩
    intro hd
    have hsmall := (Finset.mem_filter.mp hd).2
    rw [hh.2] at hsmall
    exact (Nat.not_lt_of_ge (retainedBins_capacity U signature B i)) hsmall
  · rintro ⟨ha, hd⟩
    have hlarge : B ≤ (signatureBin U signature (signature a)).card := by
      apply Nat.le_of_not_gt
      intro hsmall
      exact hd (Finset.mem_filter.mpr ⟨ha, hsmall⟩)
    let s : RetainedIndex U signature B := ⟨signature a, hlarge⟩
    refine ⟨Fintype.equivFin (RetainedIndex U signature B) s, ?_⟩
    change a ∈ signatureBin U signature
      ((Fintype.equivFin (RetainedIndex U signature B)).symm
        (Fintype.equivFin (RetainedIndex U signature B) s)).val
    rw [Equiv.symm_apply_apply]
    exact Finset.mem_filter.mpr ⟨ha, rfl⟩

theorem discarded_retained_disjoint (U : Finset α) (signature : α → σ) (B : ℕ) :
    Disjoint (discarded U signature B) (Finset.univ.biUnion (retainedBins U signature B)) := by
  rw [retainedBins_union]
  exact Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp hb).2 ha)

theorem discarded_union_retained (U : Finset α) (signature : α → σ) (B : ℕ) :
    discarded U signature B ∪ Finset.univ.biUnion (retainedBins U signature B) = U := by
  rw [retainedBins_union]
  exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

end Erdos1017.FiniteArity
