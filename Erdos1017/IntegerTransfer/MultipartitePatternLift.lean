module

public import Erdos1017.IntegerTransfer.MultipartiteCounting

/-!
# Pattern counting with repeated original parts

Pattern roles may use the same original part, provided every required pair is
regular, which permits two independent copies of the extension coordinates over
a shared base (`labelled_pattern_error`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCounting

open scoped BigOperators

variable {k m : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Pattern roles may use the same original part, provided every required pair
is regular. This permits two independent copies of the extension coordinates
with shared base coordinates in the second-moment argument. -/
theorem labelled_pattern_error (G : SimpleGraph (Fin k × A)) [DecidableRel G.Adj]
    (label : Fin m → Fin k) (E : Finset (Fin m × Fin m)) {ε : ℝ} (hε : 0 ≤ ε)
    (horder : ∀ e ∈ E, e.1 < e.2)
    (hreg : ∀ e ∈ E, G.IsUniform ε (part (label e.1)) (part (label e.2))) :
    |(∑ X : Fin m → A, ∏ e ∈ E,
        if G.Adj (label e.1, X e.1) (label e.2, X e.2) then (1 : ℝ) else 0) -
      (Fintype.card A : ℝ) ^ m * ∏ e ∈ E,
        (G.edgeDensity (part (label e.1)) (part (label e.2)) : ℝ)| ≤
      E.card * ε * (Fintype.card A : ℝ) ^ m := by
  have h := CliqueCounting.pattern_discrepancy E
    (fun e a b => if G.Adj (label e.1, a) (label e.2, b) then 1 else 0)
    (fun e => (G.edgeDensity (part (label e.1)) (part (label e.2)) : ℝ))
    (ε * (Fintype.card A : ℝ) ^ 2) (by positivity) horder
    (by intro e _ a b; split_ifs <;> constructor <;> norm_num)
    (by
      intro e _
      constructor
      · exact_mod_cast G.edgeDensity_nonneg (part (label e.1)) (part (label e.2))
      · exact_mod_cast G.edgeDensity_le_one (part (label e.1)) (part (label e.2)))
    (fun e he X Y => part_discrepancy G (hreg e he) X Y)
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  apply le_of_mul_le_mul_left (a := (Fintype.card A : ℝ) ^ 2) ?_ (sq_pos_of_pos hn)
  calc
    _ ≤ _ := h
    _ = _ := by ring

end Erdos1017.MultipartiteCounting
