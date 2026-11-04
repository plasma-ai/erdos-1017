module

public import Erdos1017.Multipartite.Countable.CountableTwoHeadChord

/-!
# Endpoints of a two-head completion

If the cross penalty dominates the least repeat penalty of one head, one of the
two physical retained-head endpoints preserves the objective
(`exists_head_endpoint`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

open scoped BigOperators

/-- If the cross penalty dominates the least repeat penalty of one head,
one of the two physical retained-head endpoints preserves its objective.
The completed mass is mixed with all old dust by an explicit probability law. -/
theorem exists_head_endpoint {D : Coefficients} (hD : D ∈ feasible)
    (i j : ℕ) (hij : i ≠ j) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (hpi : p i = 0) (hpj : p j = 0)
    (u v x s : ℝ) (hu : 0 < u) (hv : 0 < v) (hx : 0 ≤ x)
    (hx2 : x ^ 2 = u ^ 2 + v ^ 2) (hs : 0 ≤ s)
    (hpair : repeatPenalty D i ≤
      -MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j))) :
    ∃ E ∈ feasible,
      objective (replaceTwo p i j u v) s D ≤
        objective (replaceTwo p i j x 0) (s + u + v - x) E ∨
      objective (replaceTwo p i j u v) s D ≤
        objective (replaceTwo p i j 0 x) (s + u + v - x) E := by
  have hvx : v < x := by nlinarith [sq_pos_of_pos hu]
  have hδ : 0 < u + v - x := by nlinarith [mul_pos hu hv]
  let S := s + u + v - x
  have hS : 0 < S := by dsimp [S]; linarith
  let q : Fin 2 → ℝ := fun k => if k = 0 then (u + v - x) / S else s / S
  have hq₀ (k : Fin 2) : 0 ≤ q k := by
    dsimp only [q]
    split_ifs <;> positivity
  have hq : ∑ k, q k = 1 := by
    rw [Fin.sum_univ_two]
    change (u + v - x) / S + s / S = 1
    rw [← add_div, show (u + v - x) + s = S by dsimp [S]; ring, div_self hS.ne']
  have hq0 : S * q 0 = u + v - x := by
    simp only [q, ↓reduceIte]
    field_simp
  have hq1 : S * q 1 = s := by
    norm_num [q]
    field_simp
  let E := completeType D i (repeatPenalty D i) q
  have hE : E ∈ feasible := completeType_feasible hD i q hq₀ hq
  have hloss := completeType_loss hD i q hq₀ hq
    (Function.update p j v) (fun k => by
      by_cases hk : k = j
      · subst k; simpa using hv.le
      · simpa [Function.update_of_ne, hk] using hp k)
    (hsum.update j v) (by simp [hij, hpi]) (x - v) S (by linarith) hS.le
  rw [hq0, hq1] at hloss
  have hold : Function.update (Function.update p j v) i (x - v + (u + v - x)) =
      replaceTwo p i j u v := by
    rw [show x - v + (u + v - x) = u by ring, Function.update_comm (Ne.symm hij)]
    rfl
  have hvirtual : Function.update (Function.update p j v) i (x - v) =
      replaceTwo p i j (x - v) v := Function.update_comm (Ne.symm hij) _ _ _
  rw [hold, hvirtual] at hloss
  have hchord := two_head_chord hE i j hij p hp hsum hpi hpj x v S hx hv.le hvx.le
  have hkernel : MultipartiteCountableMeasure.kernel E (.inl (some i)) (.inl (some j)) =
      MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) := by
    simp only [MultipartiteCountableMeasure.kernel, pair, E, completeType]
  rw [hkernel] at hchord
  have hgeom : (x - v) * (u + v - x) + (u + v - x) ^ 2 / 2 = v * (x - v) := by
    nlinarith
  rw [hgeom] at hloss
  have hgap : 0 ≤ (-MultipartiteCountableMeasure.kernel D
      (.inl (some i)) (.inl (some j)) - repeatPenalty D i) * x * v * (x - v) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hpair) hx) hv.le) (by linarith)
  refine ⟨E, hE, ?_⟩
  by_contra h
  push Not at h
  have h₀ := mul_lt_mul_of_pos_left h.1 (show 0 < x - v by linarith)
  have h₁ := mul_lt_mul_of_pos_left h.2 hv
  have hsumlt := add_lt_add h₀ h₁
  have heq : (x - v) * objective (replaceTwo p i j x 0) S E +
      v * objective (replaceTwo p i j 0 x) S E -
      x * objective (replaceTwo p i j u v) s D =
        (-MultipartiteCountableMeasure.kernel D (.inl (some i)) (.inl (some j)) -
          repeatPenalty D i) * x * v * (x - v) := by
    nlinarith [hloss]
  nlinarith [heq]

end Erdos1017.MultipartiteCountableDual
