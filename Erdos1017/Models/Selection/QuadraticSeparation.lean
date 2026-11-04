module

public import Erdos1017.Models.Selection.QuadraticJointRange
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Separating multiplier for two quadratic forms

Two quadratic forms admit a bounded separating multiplier, using convexity of
their joint range from Dines's theorem and the ordering of the lower and upper
multiplier slopes; no closedness or finite-dimensional hypothesis is needed.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Variation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The lower and upper multiplier slopes are ordered, using the actual
joint quadratic image and the zero-density consequence of domination. -/
theorem quadratic_multiplier_slopes_le (A B : LinearMap.BilinForm ℝ E)
    (L : ℝ) (hbound : ∀ x, B x x ≤ L * |A x x|)
    (u v : E) (hu : A u u < 0) (hv : 0 < A v v) :
    B u u / (-A u u) ≤ (-B v v) / A v v := by
  have hqu : jointQuadratic A B u ∈ Set.range (jointQuadratic A B) := ⟨u, rfl⟩
  have hqv : jointQuadratic A B v ∈ Set.range (jointQuadratic A B) := ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := jointQuadratic_nonneg_smul_mem_range A B (A v v) hv.le hqu
  obtain ⟨z, hz⟩ := jointQuadratic_nonneg_smul_mem_range A B (-A u u) (by linarith) hqv
  obtain ⟨x, hx⟩ := jointQuadratic_add_mem_range A B w z
  rw [hw, hz] at hx
  have hAx := congrArg Prod.fst hx
  have hBx := congrArg Prod.snd hx
  change A x x = A v v * A u u + (-A u u) * A v v at hAx
  change B x x = A v v * B u u + (-A u u) * B v v at hBx
  have hzero : A x x = 0 := by nlinarith [hAx]
  have h := hbound x
  rw [hzero, abs_zero, mul_zero] at h
  apply (div_le_div_iff₀ (by linarith : 0 < -A u u) hv).mpr
  nlinarith [hBx]

/-- A bounded separating multiplier for two quadratic forms. The actual
joint range is convex by Dines's theorem; no closedness or finite-dimensional
hypothesis is needed. The Lipschitz constant bounds the multiplier. -/
theorem exists_bounded_quadratic_multiplier (A B : LinearMap.BilinForm ℝ E)
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ x, B x x ≤ L * |A x x|) :
    ∃ m : ℝ, -L ≤ m ∧ m ≤ L ∧ ∀ x, B x x + m * A x x ≤ 0 := by
  let S : Set ℝ := {-L} ∪ {r | ∃ x : E, A x x < 0 ∧ r = B x x / (-A x x)}
  have hbase : -L ∈ S := Or.inl rfl
  have hne : S.Nonempty := ⟨-L, hbase⟩
  have hupper : ∀ r ∈ S, r ≤ L := by
    intro r hr
    rcases hr with hr | ⟨x, hx, rfl⟩
    · have he : r = -L := hr
      rw [he]
      linarith
    · apply (div_le_iff₀ (by linarith : 0 < -A x x)).mpr
      simpa only [abs_of_neg hx] using hbound x
  have hbdd : BddAbove S := ⟨L, hupper⟩
  refine ⟨sSup S, le_csSup hbdd hbase, csSup_le hne hupper, ?_⟩
  intro x
  rcases lt_trichotomy (A x x) 0 with hx | hx | hx
  · have hmem : B x x / (-A x x) ∈ S := Or.inr ⟨x, hx, rfl⟩
    have h := (div_le_iff₀ (by linarith : 0 < -A x x)).mp (le_csSup hbdd hmem)
    nlinarith
  · have h := hbound x
    simpa [hx] using h
  · have hsup : sSup S ≤ (-B x x) / A x x := by
      apply csSup_le hne
      intro r hr
      rcases hr with hr | ⟨u, hu, rfl⟩
      · have he : r = -L := hr
        rw [he]
        apply (le_div_iff₀ hx).mpr
        have h := hbound x
        rw [abs_of_pos hx] at h
        nlinarith
      · exact quadratic_multiplier_slopes_le A B L hbound u x hu hx
    have h := (le_div_iff₀ hx).mp hsup
    linarith

end Erdos1017.Variation
