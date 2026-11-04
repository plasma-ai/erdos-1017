module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Slicing regular pairs

Restricting both sides of a regular pair to large subsets keeps it regular, with
explicit size and error parameters (`slice`, `slice_sqrt`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.RegularPair

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Restricting both sides of a regular pair preserves regularity, with explicit
size and error parameters. This is the slicing step used in clique counting. -/
theorem slice {s t s' t' : Finset V} {ε α δ : ℝ}
    (h : G.IsUniform ε s t) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hεα : ε ≤ α) (hδ : 0 ≤ δ) (hεδ : 2 * ε ≤ δ) (hscale : ε ≤ α * δ)
    (hscard : (s.card : ℝ) * α ≤ s'.card)
    (htcard : (t.card : ℝ) * α ≤ t'.card) :
    G.IsUniform δ s' t' ∧
      |(G.edgeDensity s' t' : ℝ) - G.edgeDensity s t| < ε := by
  have hbase := h hs ht
    ((mul_le_mul_of_nonneg_left hεα (Nat.cast_nonneg _)).trans hscard)
    ((mul_le_mul_of_nonneg_left hεα (Nat.cast_nonneg _)).trans htcard)
  refine ⟨?_, hbase⟩
  intro a ha b hb hca hcb
  have hsa : (s.card : ℝ) * ε ≤ a.card := calc
    _ ≤ s.card * (α * δ) := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
    _ = (s.card * α) * δ := by ring
    _ ≤ s'.card * δ := mul_le_mul_of_nonneg_right hscard hδ
    _ ≤ _ := hca
  have htb : (t.card : ℝ) * ε ≤ b.card := calc
    _ ≤ t.card * (α * δ) := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg _)
    _ = (t.card * α) * δ := by ring
    _ ≤ t'.card * δ := mul_le_mul_of_nonneg_right htcard hδ
    _ ≤ _ := hcb
  have hab := h (ha.trans hs) (hb.trans ht) hsa htb
  calc
    |(G.edgeDensity a b : ℝ) - G.edgeDensity s' t'| ≤
        |(G.edgeDensity a b : ℝ) - G.edgeDensity s t| +
        |(G.edgeDensity s t : ℝ) - G.edgeDensity s' t'| := abs_sub_le _ _ _
    _ < ε + ε := add_lt_add hab (by rwa [abs_sub_comm])
    _ ≤ δ := by linarith

/-- For `ε ≤ 1/4`, subsets of at least a `√ε` fraction of each side of an
`ε`-regular pair form a `√ε`-regular pair whose density differs by less than `ε`. -/
theorem slice_sqrt {s t s' t' : Finset V} {ε : ℝ}
    (h : G.IsUniform ε s t) (hε : ε ≤ 1 / 4)
    (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hscard : (s.card : ℝ) * Real.sqrt ε ≤ s'.card)
    (htcard : (t.card : ℝ) * Real.sqrt ε ≤ t'.card) :
    G.IsUniform (Real.sqrt ε) s' t' ∧
      |(G.edgeDensity s' t' : ℝ) - G.edgeDensity s t| < ε := by
  have he : 0 ≤ ε := h.pos.le
  have hsqrt := Real.sq_sqrt he
  have hroot : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have htwo : 2 * ε ≤ Real.sqrt ε := by nlinarith
  exact slice G h hs ht (by linarith) hroot htwo (by nlinarith) hscard htcard

end Erdos1017.RegularPair
