module

public import Erdos1017.IntegerTransfer.MultipartiteExtensionConcentration

/-!
# Typical extension counts with uniform tolerance

Positive pair densities give the predicted extension count a uniform lower
bound, and a small regularity error forces almost every base clique to have the
predicted count within relative tolerance `γ`, with the regularity tolerance
chosen before the part size and the graph (`exists_extension_tolerance`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteExtension

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] {t u : ℕ}

/-- The finite combinatorial coefficient in the extension variance bound. -/
def errorCoefficient (t u : ℕ) : ℝ :=
  (SharedBasePattern.edges t u).card + 2 * (completeEdges (t + u)).card +
    3 * (completeEdges t).card

omit [DecidableEq A] in
/-- Positive original pair densities give the predicted extension count its
uniform lower bound at the correct scale. -/
theorem prediction_lower (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ i j : Fin (t + u), i < j →
      δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j)) :
    (Fintype.card A : ℝ) ^ u * δ ^ (SharedBasePattern.extensionEdges t u).card ≤ prediction G := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := Finset.prod_le_prod₀
    (s := SharedBasePattern.extensionEdges t u) (f := fun _ => δ)
    (g := fun e => (G.edgeDensity (MultipartiteCounting.part e.1) (MultipartiteCounting.part e.2) : ℝ))
    (fun _ _ => hδ) (by
      intro e he
      exact hd _ _ (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2)
  simpa only [Finset.prod_const, extensionDensity] using h

/-- Explicit small regularity error forces almost every actual base clique to
have the predicted extension count, with relative tolerance γ. -/
theorem relative_exception_bound (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    {ε δ γ ζ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hγ : 0 < γ)
    (htolerance : ε * errorCoefficient t u ≤
      ζ * γ ^ 2 * (δ ^ (SharedBasePattern.extensionEdges t u).card) ^ 2)
    (hreg : ∀ i j : Fin (t + u), i < j →
      G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j))
    (hd : ∀ i j : Fin (t + u), i < j →
      δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j)) :
    (((bases G).filter (fun x => γ * prediction G ≤
      |CliqueExtension.count (extensionRelation G) x - prediction G|)).card : ℝ) ≤
      ζ * (Fintype.card A : ℝ) ^ t := by
  let n : ℝ := Fintype.card A
  let D := δ ^ (SharedBasePattern.extensionEdges t u).card
  let M := ((bases G).filter (fun x => γ * prediction G ≤
    |CliqueExtension.count (extensionRelation G) x - prediction G|)).card
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
  have hD : 0 < D := pow_pos hδ _
  have hμ := prediction_bounds G
  have hlower : n ^ u * D ≤ prediction G := prediction_lower G hδ.le hd
  have hraw := exceptional_extension_bound G hε (mul_nonneg hγ.le hμ.1) hreg
  have hscale : (γ * n ^ u * D) ^ 2 ≤ (γ * prediction G) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlower hγ.le
    have hpos : 0 ≤ γ * n ^ u * D := by positivity
    nlinarith
  have hscale' := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg M)
  have htol := mul_le_mul_of_nonneg_right htolerance (pow_nonneg hn.le (t + u + u))
  apply le_of_mul_le_mul_left (a := (γ * n ^ u * D) ^ 2) ?_ (by positivity)
  calc
    _ ≤ (γ * prediction G) ^ 2 * M := hscale'
    _ ≤ ε * n ^ (t + u + u) * errorCoefficient t u := hraw
    _ ≤ (ζ * γ ^ 2 * D ^ 2) * n ^ (t + u + u) := by nlinarith [htol]
    _ = _ := by simp only [pow_add, pow_two]; ring

/-- Uniform quantifier form: the regularity tolerance is chosen before the
part size and the graph. It controls exceptional actual base cliques. -/
theorem exists_extension_tolerance (t u : ℕ) (δ γ ζ : ℝ)
    (hδ : 0 < δ) (hγ : 0 < γ) (hζ : 0 < ζ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (n : ℕ), 0 < n →
      ∀ (G : SimpleGraph (Fin (t + u) × Fin n)) [DecidableRel G.Adj]
        (ε : ℝ), 0 ≤ ε → ε < ε₀ →
        (∀ i j : Fin (t + u), i < j →
          G.IsUniform ε (MultipartiteCounting.part i) (MultipartiteCounting.part j)) →
        (∀ i j : Fin (t + u), i < j →
          δ ≤ G.edgeDensity (MultipartiteCounting.part i) (MultipartiteCounting.part j)) →
        (((bases G).filter (fun x => γ * prediction G ≤
          |CliqueExtension.count (extensionRelation G) x - prediction G|)).card : ℝ) ≤
            ζ * (n : ℝ) ^ t := by
  let C := errorCoefficient t u
  let D := δ ^ (SharedBasePattern.extensionEdges t u).card
  let ε₀ := ζ * γ ^ 2 * D ^ 2 / (C + 1)
  have hC : 0 ≤ C := by dsimp [C, errorCoefficient]; positivity
  have hD : 0 < D := pow_pos hδ _
  have hden : 0 < C + 1 := by linarith
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro n hn G _ ε hε hsmall hreg hd
  let : NeZero n := ⟨by omega⟩
  have htol : ε * C ≤ ζ * γ ^ 2 * D ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hsmall hden
    have heq : ε₀ * (C + 1) = ζ * γ ^ 2 * D ^ 2 := by
      dsimp [ε₀]
      exact div_mul_cancel₀ _ (ne_of_gt hden)
    rw [heq] at hmul
    nlinarith
  simpa only [Fintype.card_fin] using relative_exception_bound G hε hδ hγ htol hreg hd

end Erdos1017.MultipartiteExtension
