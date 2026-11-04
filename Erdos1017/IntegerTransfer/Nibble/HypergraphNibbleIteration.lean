module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleActive

/-!
# Accumulating matchings over nibble rounds

This module defines the accumulated matching, active vertex set and total waste
after a finite sequence of sampling rounds, shows that matchings retained in
different rounds remain vertex-disjoint, and proves the exact accounting in
which uncovered active vertices and waste are the only vertices left uncovered
(`matchingRounds_accounting`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Accumulate the actual retained matchings from a finite sequence of sampling rounds. -/
def matchingRounds (H : Finset (Finset V)) : List (Finset V → Bool) → Finset (Finset V)
  | [] => ∅
  | X :: xs => retained H X ∪ matchingRounds (residual H X) xs

/-- The active vertex set after the specified sequence of rounds. -/
def activeRounds (H : Finset (Finset V)) (U : Finset V) : List (Finset V → Bool) → Finset V
  | [] => U
  | X :: xs => activeRounds (residual H X) (survivors H X U) xs

/-- Total actual discarded waste over the rounds. -/
def wasteRounds (H : Finset (Finset V)) (U : Finset V) : List (Finset V → Bool) → ℕ
  | [] => 0
  | X :: xs => (wasted H X U).card + wasteRounds (residual H X) (survivors H X U) xs

theorem matchingRounds_subset (H : Finset (Finset V)) (xs : List (Finset V → Bool)) :
    matchingRounds H xs ⊆ H := by
  induction xs generalizing H with
  | nil => simp [matchingRounds]
  | cons X xs ih =>
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (Finset.mem_filter.mp he).1
    · exact (Finset.mem_filter.mp (ih (residual H X) he)).1

/-- Matchings retained in different rounds remain vertex-disjoint, not merely edge-disjoint. -/
theorem matchingRounds_pairwise_disjoint (H : Finset (Finset V)) (xs : List (Finset V → Bool)) :
    (matchingRounds H xs : Set (Finset V)).PairwiseDisjoint id := by
  induction xs generalizing H with
  | nil => simp [matchingRounds]
  | cons X xs ih =>
    intro e he f hf hef
    rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
    · exact retained_pairwise_disjoint H X he hf hef
    · exact retained_disjoint_residual H X e f he (matchingRounds_subset (residual H X) xs hf)
    · exact (retained_disjoint_residual H X f e hf (matchingRounds_subset (residual H X) xs he)).symm
    · exact ih (residual H X) he hf hef

/-- Exact finite-round accounting: uncovered active vertices and actual discarded waste
are the only vertices not covered by the accumulated matching. -/
theorem matchingRounds_accounting (H : Finset (Finset V)) (U : Finset V)
    (xs : List (Finset V → Bool)) (r : ℕ) (hr : 0 < r)
    (hsupport : ∀ e ∈ H, e ⊆ U) (huniform : ∀ e ∈ H, e.card = r) :
    r * (matchingRounds H xs).card + (activeRounds H U xs).card + wasteRounds H U xs = U.card := by
  induction xs generalizing H U with
  | nil => simp [matchingRounds, activeRounds, wasteRounds]
  | cons X xs ih =>
    have hsupport' := residual_supported_on_survivors H X U hsupport
    have huniform' : ∀ e ∈ residual H X, e.card = r :=
      fun e he => huniform e (Finset.mem_filter.mp he).1
    have hrest := ih (residual H X) (survivors H X U) hsupport' huniform'
    have hround := round_vertex_accounting H X U r hsupport huniform
    have hdisjoint : Disjoint (retained H X) (matchingRounds (residual H X) xs) := by
      apply Finset.disjoint_left.mpr
      intro e he hrest
      have hself := retained_disjoint_residual H X e e he
        (matchingRounds_subset (residual H X) xs hrest)
      have hempty : e = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun v hv => Finset.disjoint_left.mp hself hv hv)
      have hcard := huniform e (Finset.mem_filter.mp he).1
      simp [hempty] at hcard
      omega
    simp only [matchingRounds, activeRounds, wasteRounds, Finset.card_union_of_disjoint hdisjoint,
      Nat.mul_add]
    omega

end Erdos1017.HypergraphNibble
