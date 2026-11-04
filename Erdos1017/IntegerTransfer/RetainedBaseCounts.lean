module

public import Erdos1017.IntegerTransfer.TransversalBaseDegree
public import Erdos1017.IntegerTransfer.NormalizedThinningMean

/-!
# Counting retained edge bases

Edge-base assignments biject to the interedges between the two base parts, so
their number is the pair density times `n²`, normalized thinning retains exactly
`αn²` of them in expectation (`normalized_retainedBases_expectation`), and the
retained count has variance at most the family size.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators
open TransversalClique

variable {u : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] in
/-- Different edge bases have disjoint singleton retention supports. -/
theorem baseSupport_two_disjoint (x y : Fin 2 → A) (hxy : x ≠ y) :
    Disjoint (baseSupport (u := u) x) (baseSupport y) := by
  rw [baseSupport_two, baseSupport_two, Finset.disjoint_singleton]
  exact (baseEdge_injective (u := u)).ne hxy

/-- Every deterministic family of graph-edge bases has variance at most its size. -/
theorem retainedBases_variance_le (B : Finset (Fin 2 → A))
    (p : Coordinate (2 + u) A → ℝ) (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) :
    (∑ X, CliqueSampling.weight p X *
      (((retainedBases B X).card : ℝ) - BernoulliFamily.mean B (baseSupport (u := u)) p) ^ 2) ≤ B.card := by
  apply (BernoulliFamily.variance_le B (baseSupport (u := u)) p hp 1 ?_).trans (by simp)
  intro x _
  have hsub : B.filter (fun y => ¬Disjoint (baseSupport (u := u) x) (baseSupport y)) ⊆ {x} := by
    intro y hy
    apply Finset.mem_singleton.mpr
    by_contra hxy
    exact (Finset.mem_filter.mp hy).2 (baseSupport_two_disjoint x y (fun h => hxy h.symm))
  exact_mod_cast (Finset.card_le_card hsub).trans (by simp)

omit [DecidableEq A] in
/-- Membership in a labelled part is exactly the prescribed role label. -/
theorem mem_part_iff {k : ℕ} (i : Fin k) (v : Fin k × A) :
    v ∈ MultipartiteCounting.part i ↔ v.1 = i := by
  rcases v with ⟨j, a⟩
  simp [MultipartiteCounting.part, eq_comm]

omit [DecidableEq A] in
/-- Edge-base assignments biject to actual interedges between the two base parts. -/
theorem bases_two_card (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj] :
    (MultipartiteExtension.bases (t := 2) G).card =
      (G.interedges (MultipartiteCounting.part (Fin.castAdd u 0))
        (MultipartiteCounting.part (Fin.castAdd u 1))).card := by
  apply Finset.card_bij (fun x _ => baseEdge (u := u) x)
  · intro x hx
    have hbase := (Finset.mem_filter.mp hx).2
    rw [SimpleGraph.mem_interedges_iff]
    exact ⟨(mem_part_iff _ _).mpr rfl, (mem_part_iff _ _).mpr rfl, hbase 0 1 (by decide)⟩
  · intro x _ y _ h
    exact baseEdge_injective h
  · intro v hv
    obtain ⟨hleft, hright, hadj⟩ := (G.mem_interedges_iff).mp hv
    have hleft := (mem_part_iff _ _).mp hleft
    have hright := (mem_part_iff _ _).mp hright
    let x : Fin 2 → A := fun i => if i = 0 then v.1.2 else v.2.2
    have heq : baseEdge (u := u) x = v := by
      apply Prod.ext
      · exact Prod.ext hleft.symm (by simp [baseEdge, x])
      · exact Prod.ext hright.symm (by simp [baseEdge, x])
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    have hAdj : G.Adj (Fin.castAdd u 0, x 0) (Fin.castAdd u 1, x 1) := by
      change G.Adj (Fin.castAdd u 0, v.1.2) (Fin.castAdd u 1, v.2.2)
      convert hadj using 1
      · exact Prod.ext hleft.symm rfl
      · exact Prod.ext hright.symm rfl
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact hAdj | (simp only [Fin.lt_def] at hij; omega)

omit [DecidableEq A] in
/-- The actual number of edge bases is exactly the pair density times n². -/
theorem bases_two_card_density [Nonempty A]
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj] :
    ((MultipartiteExtension.bases (t := 2) G).card : ℝ) =
      (Fintype.card A : ℝ) ^ 2 * pairDensity G (Fin.castAdd u 0, Fin.castAdd u 1) := by
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hdensity : pairDensity G (Fin.castAdd u 0, Fin.castAdd u 1) =
      ((MultipartiteExtension.bases (t := 2) G).card : ℝ) / (Fintype.card A : ℝ) ^ 2 := by
    rw [bases_two_card]
    simp only [pairDensity, SimpleGraph.edgeDensity, Rel.edgeDensity, MultipartiteCounting.part,
      Finset.card_map, Finset.card_univ, Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, pow_two,
      SimpleGraph.interedges]
  rw [hdensity]
  field_simp

/-- Normalized thinning gives exactly αn² expected retained edge bases. -/
theorem normalized_retainedBases_expectation [Nonempty A]
    (G : SimpleGraph (Fin (2 + u) × A)) [DecidableRel G.Adj] (α : ℝ)
    (hdensity : 0 < pairDensity G (Fin.castAdd u 0, Fin.castAdd u 1)) :
    (∑ X, CliqueSampling.weight (partProbability (normalizedProbability G α)) X *
      ((retainedBases (MultipartiteExtension.bases (t := 2) G) X).card : ℝ)) =
      α * (Fintype.card A : ℝ) ^ 2 := by
  rw [retainedBases_expectation, bases_two_card_density]
  have hcomplete : MultipartiteExtension.completeEdges 2 = {(0, 1)} := by decide
  simp only [baseProbability, hcomplete, Finset.prod_singleton, normalizedProbability]
  rw [ite_eq_right (by intro h; have hval := congrArg Fin.val h; change (0 : ℕ) = 1 at hval; omega)]
  field_simp [hdensity.ne']

end Erdos1017.TransversalThinning
