module

public import Erdos1017.Models.PhysicalPrimal.FiniteHubCertificate
public import Erdos1017.Models.PhysicalPrimal.HubSampling

/-!
# Explicit constants for the finite-arity argument

The explicit finite constants of the bounded-feature arity argument (`hubCount`,
`binCount`, `hubGap` and others) are defined with their positivity and size
properties; the hub count yields a half-gap row cover, and the constants certify
every larger finite clique once the hub and small-subclique tests hold.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.FiniteArity.Certificate

/-- The explicit finite constants from the bounded-feature arity argument. -/
def hubCount (R g : ℝ) : ℕ := ⌈8 * R ^ 4 / g ^ 2⌉₊
def binCount (R g : ℝ) : ℕ := 2 ^ hubCount R g
def hubGap (g : ℝ) : ℝ := g / 2
def testOrder (g : ℝ) : ℕ := max 2 ⌈2 / hubGap g⌉₊
def penalty (g : ℝ) : ℝ := 2 * (hubGap g - 1 / testOrder g) / (testOrder g - 1)
def roundingCount (R g : ℝ) : ℕ := ⌈((2 * binCount R g + 4 : ℕ) : ℝ) / penalty g⌉₊
def binCutoff (R g : ℝ) : ℕ := max (testOrder g + 1) (roundingCount R g)
def coercivity (R g : ℝ) : ℝ := penalty g / (2 * roundingCount R g)
def discardedBound (R g : ℝ) : ℕ := binCount R g * (binCutoff R g - 1)
def largeCutoff (R g : ℝ) : ℕ := max 2 ⌈4 * ((discardedBound R g : ℝ) + 4) / coercivity R g⌉₊
def testBudget (R g : ℝ) : ℕ :=
  max (testOrder g + 1) (max (roundingCount R g + binCount R g)
    (discardedBound R g + largeCutoff R g))

theorem hubCount_pos (R g : ℝ) (hR : 0 < R) (hg : 0 < g) : 0 < hubCount R g := by
  apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
  apply Nat.one_le_ceil_iff.mpr
  positivity

theorem testOrder_ge_two (g : ℝ) : 2 ≤ testOrder g := le_max_left _ _

theorem hubGap_pos (g : ℝ) (hg : 0 < g) : 0 < hubGap g := div_pos hg (by norm_num)

theorem inverse_testOrder_le (g : ℝ) (hg : 0 < g) : 1 / (testOrder g : ℝ) ≤ hubGap g / 2 := by
  have hgap := hubGap_pos g hg
  have hk : (0 : ℝ) < testOrder g := by exact_mod_cast (show 0 < testOrder g by
    have := testOrder_ge_two g
    omega)
  have hceil : 2 / hubGap g ≤ (testOrder g : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈2 / hubGap g⌉₊))
  have hprod := (div_le_iff₀ hgap).mp hceil
  apply (div_le_iff₀ hk).mpr
  nlinarith

theorem penalty_pos (g : ℝ) (hg : 0 < g) : 0 < penalty g := by
  have hgap := hubGap_pos g hg
  have hinv := inverse_testOrder_le g hg
  have hk : (1 : ℝ) < testOrder g := by exact_mod_cast (show 1 < testOrder g by
    have := testOrder_ge_two g
    omega)
  unfold penalty
  apply div_pos
  · nlinarith
  · linarith

theorem roundingCount_pos (R g : ℝ) (hg : 0 < g) : 0 < roundingCount R g := by
  apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
  apply Nat.one_le_ceil_iff.mpr
  have hp := penalty_pos g hg
  positivity

theorem rounding_size (R g : ℝ) (hg : 0 < g) :
    3 * (binCount R g : ℝ) / 2 + 4 ≤ (roundingCount R g : ℝ) * penalty g := by
  have hp := penalty_pos g hg
  have hceil := Nat.le_ceil (((2 * binCount R g + 4 : ℕ) : ℝ) / penalty g)
  have hprod := (div_le_iff₀ hp).mp hceil
  change (((2 * binCount R g + 4 : ℕ) : ℝ)) ≤ (roundingCount R g : ℝ) * penalty g at hprod
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hprod
  nlinarith [show (0 : ℝ) ≤ binCount R g from Nat.cast_nonneg _]

theorem coercivity_pos (R g : ℝ) (hg : 0 < g) : 0 < coercivity R g := by
  apply div_pos (penalty_pos g hg)
  exact mul_pos (by norm_num) (by exact_mod_cast roundingCount_pos R g hg)

theorem large_cutoff_bound (R g : ℝ) (hg : 0 < g) :
    4 * ((discardedBound R g : ℝ) + 4) ≤ coercivity R g * largeCutoff R g := by
  have hδ := coercivity_pos R g hg
  have hceil : 4 * ((discardedBound R g : ℝ) + 4) / coercivity R g ≤ largeCutoff R g :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (show
      ⌈4 * ((discardedBound R g : ℝ) + 4) / coercivity R g⌉₊ ≤ largeCutoff R g from le_max_right _ _))
  have h := (div_le_iff₀ hδ).mp hceil
  simpa [mul_comm] using h

theorem hub_sample_size (R g : ℝ) (hR : 0 < R) (hg : 0 < g) :
    R ^ 2 < (hubCount R g : ℝ) * (g / (2 * R)) ^ 2 := by
  have hceil := Nat.le_ceil (8 * R ^ 4 / g ^ 2)
  have hprod : 8 * R ^ 4 ≤ (hubCount R g : ℝ) * g ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hg)).mp hceil
  have heq : (hubCount R g : ℝ) * (g / (2 * R)) ^ 2 =
      ((hubCount R g : ℝ) * g ^ 2) / (4 * R ^ 2) := by ring
  rw [heq]
  apply (lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hR))).mpr
  nlinarith [pow_pos hR 4]

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

/-- The explicit hub count yields the half-gap row cover. -/
theorem exists_hub_cover_at_gap {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : Ω → E) (hf : AEStronglyMeasurable f μ) (J : E →ₗᵢ[ℝ] E) (Y : Ω → Ω → ℝ)
    (R g ν ℓ : ℝ) (hR : 0 < R) (hg : 0 < g) (hgap : g ≤ ν - ℓ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    (hrow : ∀ᵐ x ∂μ, ⟪J (∫ y, f y ∂μ), f x⟫ = ν)
    (hpair : ∀ᵐ h ∂μ, ∀ᵐ x ∂μ, ⟪J (f h), f x⟫ - ℓ ≤ Y h x)
    (Good : (Fin (hubCount R g) → Ω) → Prop)
    (hGood : ∀ᵐ ω ∂Measure.pi (fun _ : Fin (hubCount R g) => μ), Good ω) :
    ∃ ω : Fin (hubCount R g) → Ω, Good ω ∧
      ∀ᵐ x ∂μ, hubGap g ≤ (hubCount R g : ℝ)⁻¹ * ∑ i, Y (ω i) x := by
  obtain ⟨ω, hω, hc⟩ := exists_hub_cover (μ := μ) (hubCount R g) (hubCount_pos R g hR hg)
    f hf J Y ν ℓ R (g / (2 * R)) (div_pos hg (mul_pos (by norm_num) hR))
    hbound (hub_sample_size R g hR hg) hrow hpair Good hGood
  refine ⟨ω, hω, hc.mono ?_⟩
  intro x hx
  have heq : g / (2 * R) * R = g / 2 := by field_simp
  rw [heq] at hx
  dsimp [hubGap]
  linarith

/-- The explicit constants certify every larger finite clique once the
actual hub and small-subclique tests have been licensed. -/
theorem finite_omitted_negative {α : Type*} [Fintype α] [DecidableEq α]
    (R g : ℝ) (hR : 0 < R) (hg : 0 < g) (U : Finset α)
    (signature : α → (Fin (hubCount R g) → Bool)) (H : Fin (hubCount R g) → α → ℝ)
    (y : α → α → ℝ) (hy : ∀ a, y a a = 0) (hupper : ∀ a b, y a b ≤ 1)
    (hlower : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → -3 ≤ y a b)
    (hcover : ∀ a ∈ U, hubGap g ≤ (hubCount R g : ℝ)⁻¹ * ∑ i, H i a)
    (hmissing : ∀ a ∈ U, ∀ i, signature a i = false → H i a = 0)
    (hhub : ∀ i (S : Finset α), S ⊆ U → S.card = testOrder g →
      (∀ a ∈ S, signature a i = true) → (∑ a ∈ S, H i a) + pairCharge S y ≤ 1)
    (hsmall : ∀ S : Finset α, S ⊆ U → S.card ≤ testBudget R g → pairCharge S y ≤ 1)
    (hlarge : testBudget R g < U.card) : pairCharge U y < 0 := by
  apply omitted_clique_negative U (hubCount R g) (testOrder g) (binCutoff R g)
    (roundingCount R g) (largeCutoff R g) (testBudget R g)
    (hubCount_pos R g hR hg) (testOrder_ge_two g)
    ((Nat.le_succ _).trans (le_max_left _ _)) (le_max_right _ _) (roundingCount_pos R g hg)
    (le_max_left _ _) _ _ signature H y hy hupper hlower (hubGap g) (penalty g)
    (hubGap_pos g hg) (penalty_pos g hg) rfl (rounding_size R g hg)
    (large_cutoff_bound R g hg) hcover hmissing hhub hsmall hlarge
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

end Erdos1017.FiniteArity.Certificate
