module

public import Erdos1017.IntegerTransfer.ThinningRoleEquiv
public import Erdos1017.IntegerTransfer.BernoulliReindex

/-!
# Role relabeling of a sampled graph

The role permutation of a sampled graph uses the same physical edge-retention
bits, including pairs whose increasing order is reversed (`thinned_role_comap`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

variable {k : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
/-- The role permutation of an actual sampled graph uses the same physical
edge-retention bits, including pairs whose increasing order is reversed. -/
theorem thinned_role_comap (G : SimpleGraph (Fin k × A))
    (σ : Equiv.Perm (Fin k)) (X : Coordinate k A → Bool) :
    (thinned G X).comap (MultipartiteCounting.roleEquiv σ) =
      thinned (G.comap (MultipartiteCounting.roleEquiv σ))
        (fun v => X (roleCoordinateEquiv σ v)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i < j
  · by_cases hσ : σ i < σ j
    · simp [thinned, MultipartiteCounting.roleEquiv, roleCoordinateEquiv, roleCoordinate,
        hij, hσ, not_lt_of_ge hij.le, not_lt_of_ge hσ.le]
    · have hσ' : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hσ) (σ.injective.ne hij.ne).symm
      simp [thinned, MultipartiteCounting.roleEquiv, roleCoordinateEquiv, roleCoordinate,
        hij, hσ, hσ', not_lt_of_ge hij.le]
  · by_cases hji : j < i
    · by_cases hσ : σ i < σ j
      · simp [thinned, MultipartiteCounting.roleEquiv, roleCoordinateEquiv, roleCoordinate,
          hij, hji, hσ, not_lt_of_ge hσ.le]
      · have hσ' : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hσ) (σ.injective.ne hji.ne.symm).symm
        simp [thinned, MultipartiteCounting.roleEquiv, roleCoordinateEquiv, roleCoordinate,
          hij, hji, hσ, hσ']
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [thinned, MultipartiteCounting.roleEquiv]

end Erdos1017.TransversalThinning
