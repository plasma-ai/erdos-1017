module

public import Erdos1017.IntegerTransfer.RegularPairDegrees
public import Mathlib.Tactic.FieldSimp

/-!
# Rectangle discrepancy of a regular pair

Regularity controls the discrepancy of every rectangle, even when either side is
below the regularity threshold (`rectangle_discrepancy`), and the discrepancy
can be written as a bilinear sum of adjacency minus density.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.RegularPair

open Finset

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Density times the number of possible pairs is the actual edge count,
including empty vertex sets. -/
theorem density_mul_cards (a b : Finset V) :
    (G.edgeDensity a b : ℝ) * a.card * b.card = (G.interedges a b).card := by
  by_cases ha : a = ∅
  · subst a
    simp [SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def]
  by_cases hb : b = ∅
  · subst b
    simp [SimpleGraph.edgeDensity_def, SimpleGraph.interedges_def]
  have hapos : (a.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ha)
  have hbpos : (b.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hb)
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  field_simp

/-- Regularity controls the discrepancy of every rectangle, even when either
side is below the regularity threshold. This supports edge-by-edge counting. -/
theorem rectangle_discrepancy {s t a b : Finset V} {ε : ℝ}
    (h : G.IsUniform ε s t) (ha : a ⊆ s) (hb : b ⊆ t) :
    |((G.interedges a b).card : ℝ) - (G.edgeDensity s t : ℝ) * a.card * b.card|
      ≤ ε * s.card * t.card := by
  have ha0 : 0 ≤ (a.card : ℝ) := Nat.cast_nonneg _
  have hb0 : 0 ≤ (b.card : ℝ) := Nat.cast_nonneg _
  have hs0 : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have ht0 : 0 ≤ (t.card : ℝ) := Nat.cast_nonneg _
  have has : (a.card : ℝ) ≤ s.card := by exact_mod_cast Finset.card_le_card ha
  have hbt : (b.card : ℝ) ≤ t.card := by exact_mod_cast Finset.card_le_card hb
  have he0 : 0 ≤ ε := h.pos.le
  have hfactor :
      |((G.interedges a b).card : ℝ) - (G.edgeDensity s t : ℝ) * a.card * b.card| =
        |(G.edgeDensity a b : ℝ) - G.edgeDensity s t| * a.card * b.card := by
    rw [← density_mul_cards G a b]
    rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0]
  have hunit : |(G.edgeDensity a b : ℝ) - G.edgeDensity s t| ≤ 1 := by
    have ha1 : (G.edgeDensity a b : ℝ) ≤ 1 := by exact_mod_cast G.edgeDensity_le_one a b
    have hs1 : (G.edgeDensity s t : ℝ) ≤ 1 := by exact_mod_cast G.edgeDensity_le_one s t
    have ha2 : 0 ≤ (G.edgeDensity a b : ℝ) := by exact_mod_cast G.edgeDensity_nonneg a b
    have hs2 : 0 ≤ (G.edgeDensity s t : ℝ) := by exact_mod_cast G.edgeDensity_nonneg s t
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hfactor]
  by_cases hsa : (s.card : ℝ) * ε ≤ a.card
  · by_cases htb : (t.card : ℝ) * ε ≤ b.card
    · have hclose := (h ha hb hsa htb).le
      calc
        _ ≤ ε * a.card * b.card := by gcongr
        _ ≤ ε * s.card * t.card := by gcongr
    · have hsmall : (b.card : ℝ) ≤ ε * t.card := by linarith
      calc
        _ ≤ (1 : ℝ) * a.card * b.card := by gcongr
        _ ≤ s.card * (ε * t.card) := by simpa only [one_mul] using mul_le_mul has hsmall hb0 hs0
        _ = _ := by ring
  · have hsmall : (a.card : ℝ) ≤ ε * s.card := by linarith
    calc
      _ ≤ (1 : ℝ) * a.card * b.card := by gcongr
      _ ≤ (ε * s.card) * t.card := by
        simpa only [one_mul] using mul_le_mul hsmall hbt hb0 (mul_nonneg h.pos.le hs0)
      _ = _ := by ring

/-- The discrepancy written as a bilinear sum of adjacency minus density. -/
theorem rectangle_sum_discrepancy {s t a b : Finset V} {ε : ℝ}
    (h : G.IsUniform ε s t) (ha : a ⊆ s) (hb : b ⊆ t) :
    |∑ x ∈ a, ∑ y ∈ b, ((if G.Adj x y then (1 : ℝ) else 0) - G.edgeDensity s t)|
      ≤ ε * s.card * t.card := by
  have heq : (∑ x ∈ a, ∑ y ∈ b,
      ((if G.Adj x y then (1 : ℝ) else 0) - G.edgeDensity s t)) =
      ((G.interedges a b).card : ℝ) - (G.edgeDensity s t : ℝ) * a.card * b.card := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [interedges_card_eq_sum, Nat.cast_sum]
    have hc : ∀ x, (∑ y ∈ b, if G.Adj x y then (1 : ℝ) else 0) =
        ((b.filter (G.Adj x)).card : ℝ) := by
      intro x
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simp only [hc]
    ring
  rw [heq]
  exact rectangle_discrepancy G h ha hb

end Erdos1017.RegularPair
