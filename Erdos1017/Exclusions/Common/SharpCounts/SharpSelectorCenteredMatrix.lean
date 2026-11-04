module

public import Erdos1017.Exclusions.Common.SharpCounts.SharpSelectorTripleCertificate

/-!
# Centered Hessian matrix of the sharp selector

This module defines the Hessian row and unhalved quadratic form at a finite load
vector, the negative half-Hessian centered at a vector of total mass two, and
the zero-mass basis directions, with identities for the diagonal, the
off-diagonal coefficients and the quadratic expansion.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical

namespace Erdos1017.Selector.Sharp

variable {ι : Type*} [Fintype ι]

/-- The Hessian row at a finite load vector. -/
def matrixRow (C : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ := ∑ j, C i j * p j

/-- The finite quadratic form, with no factor one half. -/
def matrixQuadratic (C : ι → ι → ℝ) (p : ι → ℝ) : ℝ := ∑ i, p i * matrixRow C p i

/-- The negative half-Hessian after centering at a vector of total mass two. -/
def centeredMatrix (C : ι → ι → ℝ) (p : ι → ℝ) (i j : ι) : ℝ :=
  -C i j / 2 + (matrixRow C p i + matrixRow C p j) / 4 - matrixQuadratic C p / 8

/-- Each basis direction is corrected to have zero total mass. -/
def centeredDirection (p : ι → ℝ) (i k : ι) : ℝ := (if k = i then 1 else 0) - p k / 2

theorem centeredMatrix_symm (C : ι → ι → ℝ) (hsym : ∀ i j, C i j = C j i)
    (p : ι → ℝ) (i j : ι) : centeredMatrix C p i j = centeredMatrix C p j i := by
  unfold centeredMatrix
  rw [hsym i j]
  ring

theorem centeredMatrix_rows (C : ι → ι → ℝ) (p : ι → ℝ) (hs : ∑ i, p i = 2)
    (i : ι) : ∑ j, p j * centeredMatrix C p i j = 0 := by
  have ht (j : ι) : p j * centeredMatrix C p i j =
      -(C i j * p j) / 2 + (matrixRow C p i / 4 - matrixQuadratic C p / 8) * p j +
        (p j * matrixRow C p j) / 4 := by unfold centeredMatrix; ring
  simp only [ht, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  rw [hs]
  change -(matrixRow C p i) / 2 + (matrixRow C p i / 4 - matrixQuadratic C p / 8) * 2 +
    matrixQuadratic C p / 4 = 0
  ring

theorem centeredDirection_sum (p : ι → ℝ) (hs : ∑ i, p i = 2) (i : ι) :
    ∑ k, centeredDirection p i k = 0 := by
  simp [centeredDirection, Finset.sum_sub_distrib, ← Finset.sum_div, hs]

private theorem centeredDirection_row (C : ι → ι → ℝ) (p : ι → ℝ) (i k : ι) :
    matrixRow C (centeredDirection p i) k = C k i - matrixRow C p k / 2 := by
  simp [matrixRow, centeredDirection, mul_sub, mul_ite, mul_div, Finset.sum_sub_distrib,
    ← Finset.sum_div]

/-- The actual centered diagonal is the negative half of the actual
Hessian energy of its corresponding mass-preserving basis direction. -/
theorem centeredMatrix_diagonal (C : ι → ι → ℝ) (hsym : ∀ i j, C i j = C j i)
    (p : ι → ℝ) (i : ι) :
    centeredMatrix C p i i = -matrixQuadratic C (centeredDirection p i) / 2 := by
  have ht (k : ι) : centeredDirection p i k * matrixRow C (centeredDirection p i) k =
      (if k = i then C i i - matrixRow C p i / 2 else 0) -
        C i k * p k / 2 + (p k * matrixRow C p k) / 4 := by
    rw [centeredDirection_row]
    unfold centeredDirection
    by_cases hk : k = i
    · subst k
      simp only [ite_true]
      ring
    · simp only [hk, ite_false]
      rw [hsym k i]
      ring
  have he : matrixQuadratic C (centeredDirection p i) =
      C i i - matrixRow C p i + matrixQuadratic C p / 4 := by
    unfold matrixQuadratic
    simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change C i i - matrixRow C p i / 2 - matrixRow C p i / 2 +
      (∑ k, p k * matrixRow C p k) / 4 = _
    ring
  rw [he]
  unfold centeredMatrix
  ring

/-- The off-diagonal coefficient is recovered from centered squared distances. -/
theorem centeredMatrix_distance (C : ι → ι → ℝ)
    (hdiag : ∀ i, C i i = -(2 / 3 : ℝ)) (p : ι → ℝ) (i j : ι) :
    C i j = centeredMatrix C p i i + centeredMatrix C p j j -
      2 * centeredMatrix C p i j - 2 / 3 := by
  unfold centeredMatrix
  rw [hdiag i, hdiag j]
  ring

/-- The exact unhalved quadratic expansion uses symmetry of the original
finite Hessian, with both mixed terms identified explicitly. -/
theorem matrixQuadratic_add_smul (C : ι → ι → ℝ)
    (hsym : ∀ i j, C i j = C j i) (p z : ι → ℝ) (t : ℝ) :
    matrixQuadratic C (fun i => p i + t * z i) = matrixQuadratic C p +
      2 * t * (∑ i, z i * matrixRow C p i) + t ^ 2 * matrixQuadratic C z := by
  have hcross : (∑ i, ∑ j, p i * (C i j * z j)) = ∑ i, ∑ j, z i * (C i j * p j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have ht (i j : ι) : (p i + t * z i) * (C i j * (p j + t * z j)) =
      p i * (C i j * p j) + t * (p i * (C i j * z j)) +
        t * (z i * (C i j * p j)) + t ^ 2 * (z i * (C i j * z j)) := by ring
  simp only [matrixQuadratic, matrixRow, Finset.mul_sum]
  simp_rw [ht, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [← Finset.mul_sum] at hcross
  rw [hcross]
  ring

end Erdos1017.Selector.Sharp
