module

public import Erdos1017.Models.Kernel.CompactEigenbasis

/-!
# Eigenbasis containing a prescribed eigenvector

A compact symmetric operator admits a complete eigenbasis containing a
prescribed unit eigenvector, including when that eigenvalue is repeated
(`exists_eigen_hilbertBasis_containing`).
-/

@[expose] public section

noncomputable section

open Module
open scoped RealInnerProductSpace

namespace Erdos1017.KernelOperator

universe u

/-- A compact symmetric operator admits a complete eigenbasis containing a
prescribed unit eigenvector, including when that eigenvalue is repeated. -/
theorem exists_eigen_hilbertBasis_containing
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric)
    (v : E) (hv : ‖v‖ = 1) (ν : ℝ) (heigen : T v = ν • v) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (t : ι → ℝ) (j : ι),
      (∀ i, T (b i) = t i • b i) ∧ b j = v ∧ t j = ν := by
  classical
  let V := fun t : ℝ => End.eigenspace T.toLinearMap t
  let hcomplete (t : ℝ) : CompleteSpace (V t) :=
    (ContinuousLinearMap.isClosed_eigenspace T t).completeSpace_coe
  let S (t : ℝ) : Set (V t) := {x | (x : E) = v}
  have honS (t : ℝ) : Orthonormal ℝ ((↑) : S t → V t) := by
    have : Subsingleton (S t) := ⟨by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      exact x.property.trans y.property.symm⟩
    apply orthonormal_subsingleton_iff.mpr
    intro x
    change ‖(x.val : E)‖ = 1
    rw [x.property, hv]
  choose I b hsub hb using fun t : ℝ => (honS t).exists_hilbertBasis_extension
  let e : (Σ t, I t) → E := fun i => (b i.1 i.2 : E)
  have hon : Orthonormal ℝ e := by
    constructor
    · intro i
      exact (b i.1).orthonormal.norm_eq_one i.2
    · rintro ⟨t, i⟩ ⟨s, j⟩ hij
      by_cases hts : t = s
      · subst s
        have hij' : i ≠ j := fun h => hij (by cases h; rfl)
        exact (b t).orthonormal.inner_eq_zero hij'
      · exact hs.orthogonalFamily_eigenspaces hts (b t i) (b s j)
  have htotal : (Submodule.span ℝ (Set.range e))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have he (i : Σ t, I t) : ⟪e i, v⟫ = 0 :=
      (Submodule.mem_orthogonal _ _).mp hv (e i) (Submodule.subset_span (Set.mem_range_self i))
    have hrow (t : ℝ) (u : V t) : ⟪(u : E), v⟫ = 0 := by
      let L : V t →L[ℝ] ℝ := (innerSL ℝ v).comp (V t).subtypeL
      have hspan : Submodule.span ℝ (Set.range (b t)) ≤ L.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        change ⟪v, (b t i : E)⟫ = 0
        rw [real_inner_comm]
        exact he ⟨t, i⟩
      have htop : (⊤ : Submodule ℝ (V t)) ≤ L.ker := by
        rw [← (b t).dense_span]
        exact (Submodule.span ℝ (Set.range (b t))).topologicalClosure_minimal hspan L.isClosed_ker
      have hz := htop (Submodule.mem_top : u ∈ (⊤ : Submodule ℝ (V t)))
      change ⟪v, (u : E)⟫ = 0 at hz
      rwa [real_inner_comm] at hz
    have hv' : v ∈ (⨆ t : ℝ, V t)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      apply (Submodule.mem_iInf _).mpr
      intro t
      apply (Submodule.mem_orthogonal _ _).mpr
      intro u hu
      exact hrow t ⟨u, hu⟩
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at hv'
    exact hv'
  let bfull := HilbertBasis.mkOfOrthogonalEqBot hon htotal
  let j : Σ t, I t := ⟨ν, ⟨⟨v, End.mem_eigenspace_iff.mpr heigen⟩, hsub ν rfl⟩⟩
  refine ⟨Σ t, I t, bfull, Sigma.fst, j, ?_, ?_, rfl⟩
  · intro i
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact End.mem_eigenspace_iff.mp (b i.1 i.2).property
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    change (b ν j.2 : E) = v
    rw [hb]

end Erdos1017.KernelOperator
