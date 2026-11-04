module

public import Erdos1017.IntegerTransfer.GraphRelabelRegularity
public import Erdos1017.IntegerTransfer.ThinnedGraph

/-!
# Coordinate permutations induced by role relabeling

A role permutation induces a permutation of all edge coordinates
(`roleCoordinateEquiv`) that preserves whether a coordinate is written in
increasing or decreasing role order, and the identity relabeling fixes every
coordinate.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

variable {k : ℕ} {A : Type*}

/-- Relabel edge endpoints while preserving whether the coordinate was written
in increasing or decreasing role order. This is a permutation of all coordinates. -/
def roleCoordinate (σ : Equiv.Perm (Fin k)) (v : Coordinate k A) : Coordinate k A :=
  if (v.1.1 < v.2.1 ↔ σ v.1.1 < σ v.2.1) then
    ((σ v.1.1, v.1.2), (σ v.2.1, v.2.2))
  else ((σ v.2.1, v.2.2), (σ v.1.1, v.1.2))

/-- Relabeling back recovers even unused decreasing and within-part coordinates. -/
theorem roleCoordinate_leftInverse (σ : Equiv.Perm (Fin k)) :
    Function.LeftInverse (roleCoordinate (A := A) σ.symm) (roleCoordinate σ) := by
  rintro ⟨⟨i, a⟩, ⟨j, b⟩⟩
  by_cases hij : i < j
  · by_cases hσ : σ i < σ j
    · simp [roleCoordinate, hij, hσ]
    · have hσ' : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hσ) (σ.injective.ne hij.ne).symm
      have hji : ¬j < i := not_lt_of_ge hij.le
      simp [roleCoordinate, hij, hσ, hσ', hji]
  · by_cases hσ : σ i < σ j
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (fun h => hσ.ne (by rw [h]))
      have hσ' : ¬σ j < σ i := not_lt_of_ge hσ.le
      simp [roleCoordinate, hij, hσ, hσ', hji]
    · simp [roleCoordinate, hij, hσ]

/-- The full coordinate permutation induced by a role permutation. -/
def roleCoordinateEquiv (σ : Equiv.Perm (Fin k)) : Coordinate k A ≃ Coordinate k A where
  toFun := roleCoordinate σ
  invFun := roleCoordinate σ.symm
  left_inv := roleCoordinate_leftInverse σ
  right_inv := by
    intro v
    simpa only [Equiv.symm_symm] using roleCoordinate_leftInverse (A := A) σ.symm v

/-- Identity role relabeling keeps every physical coordinate fixed. -/
theorem roleCoordinateEquiv_refl (v : Coordinate k A) :
    roleCoordinateEquiv (Equiv.refl (Fin k)) v = v := by
  simp [roleCoordinateEquiv, roleCoordinate]

/-- An increasing coordinate maps to the unique increasing coordinate of its
relabelled unordered graph edge. -/
theorem roleCoordinate_of_lt (σ : Equiv.Perm (Fin k)) (v : Coordinate k A) (hv : v.1.1 < v.2.1) :
    roleCoordinate σ v = if σ v.1.1 < σ v.2.1 then
      ((σ v.1.1, v.1.2), (σ v.2.1, v.2.2))
    else ((σ v.2.1, v.2.2), (σ v.1.1, v.1.2)) := by
  simp only [roleCoordinate, hv, true_iff]

end Erdos1017.TransversalThinning
