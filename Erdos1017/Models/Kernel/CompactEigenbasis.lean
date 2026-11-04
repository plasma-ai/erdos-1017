module

public import Erdos1017.Models.Kernel.KernelSpectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# Hilbert eigenbases of compact symmetric operators

A compact symmetric operator has a Hilbert basis of eigenvectors, countable in
the separable case; its quadratic form is the convergent spectral sum, and
removing a finite spectral part containing every positive eigenvalue leaves a
nonpositive quadratic form.
-/

@[expose] public section

noncomputable section

open Module
open scoped RealInnerProductSpace BigOperators

namespace Erdos1017.KernelOperator

universe u

/-- A compact symmetric operator on a real Hilbert space admits a Hilbert
basis of eigenvectors, including a basis of its possibly infinite kernel. -/
theorem exists_eigen_hilbertBasis {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (t : ι → ℝ),
      ∀ i, T (b i) = t i • b i := by
  classical
  let V := fun t : ℝ => End.eigenspace T.toLinearMap t
  let hcomplete (t : ℝ) : CompleteSpace (V t) :=
    (ContinuousLinearMap.isClosed_eigenspace T t).completeSpace_coe
  choose I b hb using fun t : ℝ => exists_hilbertBasis ℝ (V t)
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
  refine ⟨Σ t, I t, HilbertBasis.mkOfOrthogonalEqBot hon htotal, Sigma.fst, ?_⟩
  intro i
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact (End.mem_eigenspace_iff.mp (b i.1 i.2).property)

/-- The quadratic form of a symmetric operator is the convergent spectral
sum with respect to any Hilbert eigenbasis. -/
theorem hasSum_eigen_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} (b : HilbertBasis ι ℝ E)
    (T : E →L[ℝ] E) (hs : T.toLinearMap.IsSymmetric) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (x : E) :
    HasSum (fun i => t i * ⟪b i, x⟫ ^ 2) ⟪T x, x⟫ := by
  convert b.hasSum_inner_mul_inner (T x) x using 1
  funext i
  rw [show ⟪T x, b i⟫ = ⟪x, T (b i)⟫ from hs x (b i), heigen i,
    inner_smul_right, real_inner_comm x (b i)]
  ring

/-- Removing all positive eigenvalues leaves a nonpositive quadratic form.
The finite set must contain every positive eigenvalue in the supplied basis. -/
theorem eigen_quadratic_le_finite_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} (b : HilbertBasis ι ℝ E)
    (T : E →L[ℝ] E) (hs : T.toLinearMap.IsSymmetric) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (s : Finset ι)
    (houtside : ∀ i ∉ s, t i ≤ 0) (x : E) :
    ⟪T x, x⟫ ≤ ∑ i ∈ s, t i * ⟪b i, x⟫ ^ 2 := by
  classical
  let q : ι → ℝ := fun i => if i ∈ s then t i * ⟪b i, x⟫ ^ 2 else 0
  have hzero : ∀ i ∉ s, q i = 0 := fun i hi => by simp [q, hi]
  have hle (i : ι) : t i * ⟪b i, x⟫ ^ 2 ≤ q i := by
    by_cases hi : i ∈ s
    · simp [q, hi]
    · simpa [q, hi] using mul_nonpos_of_nonpos_of_nonneg (houtside i hi) (sq_nonneg _)
  have h := (hasSum_eigen_quadratic b T hs t heigen x)
  rw [← h.tsum_eq]
  calc
    ∑' i, t i * ⟪b i, x⟫ ^ 2 ≤ ∑' i, q i :=
      Summable.tsum_le_tsum hle h.summable (summable_of_ne_finset_zero hzero)
    _ = ∑ i ∈ s, t i * ⟪b i, x⟫ ^ 2 := by rw [tsum_eq_sum hzero]; simp [q]

/-- An orthonormal family in a separable real Hilbert space is countable. -/
theorem orthonormal_countable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E]
    {ι : Type*} {b : ι → E} (hb : Orthonormal ℝ b) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1 / 2))
      (Metric.ball (b j) (1 / 2))) := by
    intro i j hij
    have hdist : 1 ≤ dist (b i) (b j) := by
      have hs := norm_sub_sq_real (b i) (b j)
      rw [hb.norm_eq_one i, hb.norm_eq_one j, hb.inner_eq_zero hij] at hs
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (b i - b j)]
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have htri := dist_triangle (b i) x (b j)
    rw [Metric.mem_ball, dist_comm x (b i)] at hxi
    rw [Metric.mem_ball] at hxj
    linarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)

/-- In the separable case the spectral basis can be taken with a countable
index, permitting simultaneous almost-everywhere representative choices. -/
theorem exists_countable_eigen_hilbertBasis {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.toLinearMap.IsSymmetric) :
    ∃ (ι : Type u) (_ : Countable ι) (b : HilbertBasis ι ℝ E) (t : ι → ℝ),
      ∀ i, T (b i) = t i • b i := by
  obtain ⟨ι, b, t, heigen⟩ := exists_eigen_hilbertBasis T hc hs
  exact ⟨ι, orthonormal_countable b.orthonormal, b, t, heigen⟩

/-- The finite spectral operator on a chosen set of basis indices. -/
def finiteSpectralOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} (b : ι → E) (t : ι → ℝ) (s : Finset ι) : E →L[ℝ] E :=
  ∑ i ∈ s, t i • InnerProductSpace.rankOne ℝ (b i) (b i)

theorem finiteSpectralOperator_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} (b : ι → E) (t : ι → ℝ) (s : Finset ι) (x : E) :
    ⟪finiteSpectralOperator b t s x, x⟫ = ∑ i ∈ s, t i * ⟪b i, x⟫ ^ 2 := by
  simp only [finiteSpectralOperator, sum_apply,
    smul_apply, sum_inner, real_inner_smul_left,
    InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The negative spectral remainder is positive semidefinite once the finite
spectral part contains every positive basis eigenvalue. -/
theorem finiteSpectralOperator_sub_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} (b : HilbertBasis ι ℝ E)
    (T : E →L[ℝ] E) (hs : T.toLinearMap.IsSymmetric) (t : ι → ℝ)
    (heigen : ∀ i, T (b i) = t i • b i) (s : Finset ι)
    (houtside : ∀ i ∉ s, t i ≤ 0) (x : E) :
    0 ≤ ⟪(finiteSpectralOperator b t s - T) x, x⟫ := by
  rw [sub_apply, inner_sub_left, finiteSpectralOperator_quadratic]
  exact sub_nonneg.mpr (eigen_quadratic_le_finite_sum b T hs t heigen s houtside x)

end Erdos1017.KernelOperator
