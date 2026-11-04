module

public import Erdos1017.IntegerTransfer.ThinnedGraphMatching
public import Erdos1017.IntegerTransfer.ThinningBudget
public import Erdos1017.IntegerTransfer.CategoricalThinning
public import Erdos1017.IntegerTransfer.CenteredThinningBudget

/-!
# Coupled matchings of several embedded clique types

Any finite number of embedded clique types can be matched in one positive
categorical outcome, with the regularity tolerance chosen before the number of
types (`exists_coupled_clique_matchings`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalClique

open scoped BigOperators
open TransversalThinning

/-- Any finite number of embedded clique types can be matched in one positive
categorical outcome. The regularity tolerance precedes both the number of
types and the allocation floor; those affect only the part-size threshold.
One additional nonnegative cost observable can be controlled in the same sample. -/
theorem exists_coupled_clique_matchings (r : ℕ) (hr : 0 < r) (δ ρ : ℝ)
    (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (M : ℕ) (α₀ : ℝ), 0 < α₀ →
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
        ∀ (I : Type*) [Fintype I], Fintype.card I ≤ M →
          ∀ (rank : I → Fin r)
            (G : ∀ i, SimpleGraph (Fin (2 + ((rank i).val + 1)) × Fin n))
            [∀ i, DecidableRel (G i).Adj] (ε : ℝ), 0 ≤ ε → ε < ε₀ →
            (∀ i j k, j < k → (G i).IsUniform ε (MultipartiteCounting.part j) (MultipartiteCounting.part k)) →
            (∀ i j k, j < k → δ ≤ pairDensity (G i) (j, k)) →
            ∀ (W J : Type*) [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
              (q : W → J → ℝ), (∀ v j, 0 ≤ q v j) → (∀ v, ∑ j, q v j = 1) →
              ∀ (Z : (W → J) → ℝ), (∀ X, 0 ≤ Z X) →
                (∑ X, CategoricalSampling.weight q X * Z X) ≤ 1 - min ρ (1 / 2) →
              ∀ (label : I → J)
                (e : ∀ i, Coordinate (2 + ((rank i).val + 1)) (Fin n) ↪ W)
                (α : I → ℝ), (∀ i, α₀ ≤ α i) → (∀ i, α i ≤ δ) →
                (∀ i v, q (e i v) (label i) = partProbability (normalizedProbability (G i) (α i)) v) →
                ∃ X : W → J, 0 < CategoricalSampling.weight q X ∧ Z X < 1 ∧ ∀ i,
                  let Y := fun v => CategoricalSampling.projection (label i) X (e i v)
                  ∃ T : Finset (Fin (2 + ((rank i).val + 1)) → Fin n),
                    T ⊆ assignments (thinned (G i) Y) ∧
                    (T : Set (Fin (2 + ((rank i).val + 1)) → Fin n)).PairwiseDisjoint edges ∧
                    (1 - ρ) * (graphEdges (thinned (G i) Y)).card /
                      (2 + ((rank i).val + 1)).choose 2 ≤ (T.card : ℝ) ∧
                    ∀ σ : Equiv.Perm (Fin (2 + ((rank i).val + 1))),
                      let H := (G i).comap (MultipartiteCounting.roleEquiv σ)
                      |((retainedBases (MultipartiteExtension.bases (t := 2) H)
                          (fun v => Y (roleCoordinateEquiv σ v))).card : ℝ) - α i * (n : ℝ) ^ 2| <
                        ρ * α i * (n : ℝ) ^ 2 := by
  classical
  have hparameters : ∀ j : Fin r, ∃ η D₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < D₀ ∧
      ∀ (n : ℕ), 0 < n →
        ∀ (G : SimpleGraph (Fin (2 + (j.val + 1)) × Fin n)) [DecidableRel G.Adj] (α : ℝ),
          0 < α → (∀ i k, i < k → δ ≤ pairDensity G (i, k)) →
          let D := degreeScale n (j.val + 1) (SharedBasePattern.extensionEdges 2 (j.val + 1)).card α
          let L : ℝ := Fintype.card (Equiv.Perm (Fin (2 + (j.val + 1))))
          D₀ ≤ D → (n : ℝ) ^ (j.val + 1 - 1) ≤ η * D →
          ∀ X : Coordinate (2 + (j.val + 1)) (Fin n) → Bool,
            (∀ σ : Equiv.Perm (Fin (2 + (j.val + 1))),
              let H := G.comap (MultipartiteCounting.roleEquiv σ)
              let Y := fun v => X (roleCoordinateEquiv σ v)
              |((retainedBases (MultipartiteExtension.bases (t := 2) H) Y).card : ℝ) - α * (n : ℝ) ^ 2| < α * (n : ℝ) ^ 2 / 2 ∧
              ((retainedBases ((MultipartiteExtension.bases (t := 2) H) \ typicalBases H (η / 4)) Y).card : ℝ) <
                η * α * (n : ℝ) ^ 2 / (16 * L) ∧
              retainedSquaredError (extensions H) (partProbability (normalizedProbability H α)) Y <
                η ^ 3 * α * (n : ℝ) ^ 2 * D ^ 2 / (128 * L)) →
            ∃ T : Finset (Fin (2 + (j.val + 1)) → Fin n), T ⊆ assignments (thinned G X) ∧
              (T : Set (Fin (2 + (j.val + 1)) → Fin n)).PairwiseDisjoint edges ∧
              (1 - ρ) * (graphEdges (thinned G X)).card / (2 + (j.val + 1)).choose 2 ≤ (T.card : ℝ) := by
    intro j
    exact packing_of_role_control (j.val + 1) (by omega) δ ρ hδ hρ
  choose η D₀ hη hη1 hD₀ hpack using hparameters
  let L (j : Fin r) : ℝ := Fintype.card (Equiv.Perm (Fin (2 + (j.val + 1))))
  have hL (j : Fin r) : 0 < L j := by
    dsimp only [L]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin (2 + (j.val + 1)))))
  let ζ (j : Fin r) := η j * δ / (32 * L j)
  have hζ (j : Fin r) : 0 < ζ j := by
    have hηj := hη j
    have hLj := hL j
    dsimp only [ζ]
    positivity
  have htolerances := fun j : Fin r => MultipartiteExtension.exists_extension_tolerance 2 (j.val + 1)
    δ (η j / 4) (ζ j) hδ (div_pos (hη j) (by norm_num)) (hζ j)
  choose ε₁ hε₁ hconcentration using htolerances
  let E := Finset.univ.image ε₁
  have hE : E.Nonempty := ⟨ε₁ ⟨0, hr⟩, Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, rfl⟩⟩
  let ε₀ := E.min' hE
  have hε₀ : 0 < ε₀ := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.min'_mem E hE)
    change 0 < E.min' hE
    rw [← hj]
    exact hε₁ j
  have hεsmall (j : Fin r) : ε₀ ≤ ε₁ j := Finset.min'_le E (ε₁ j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  let θ := min ρ (1 / 2)
  have hθ : 0 < θ := lt_min hρ (by norm_num)
  have hθρ : θ ≤ ρ := min_le_left _ _
  have hθhalf : θ ≤ 1 / 2 := min_le_right _ _
  refine ⟨ε₀, hε₀, ?_⟩
  intro M α₀ hα₀
  have hsizes := fun j : Fin r => exists_thinning_size_threshold (j.val + 1)
    (SharedBasePattern.extensionEdges 2 (j.val + 1)).card (by omega) δ (η j) (L j) (D₀ j) α₀ θ
    hδ (hη j) (hL j) (hD₀ j) hα₀ hθ
  choose N hN hsize using hsizes
  let K (j : Fin r) := centeredBudgetCoefficient (j.val + 1) (SharedBasePattern.extensionEdges 2 (j.val + 1)).card δ (η j) (L j) θ α₀
  have hK (j : Fin r) : 0 ≤ K j := by
    have hηj := hη j
    have hLj := hL j
    dsimp only [K, centeredBudgetCoefficient]
    positivity
  let K₀ := 1 + ∑ j : Fin r, K j
  have hK₀ : 0 < K₀ := by
    have hsum : 0 ≤ ∑ j : Fin r, K j := Finset.sum_nonneg (fun j _ => hK j)
    dsimp only [K₀]
    linarith
  have hKbound (j : Fin r) : K j ≤ K₀ := by
    have h := Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ j)
    dsimp only [K₀]
    linarith
  let R := 4 * (M : ℝ) * K₀ / θ
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (((∑ j : Fin r, N j : ℕ) : ℝ) + R + 1)
  have hn₀pos : 0 < n₀ := by
    have hNsum : 0 ≤ (((∑ j : Fin r, N j : ℕ)) : ℝ) := by positivity
    exact_mod_cast (show (0 : ℝ) < n₀ by linarith)
  refine ⟨n₀, hn₀pos, ?_⟩
  intro n hn I _ hI rank G _ ε hε hsmall hregular hd W J _ _ _ _ q hq htotal Z hZ hZmean label e α hα hαδ hprob
  let : NeZero n := ⟨by omega⟩
  have hnpos : 0 < n := hn₀pos.trans_le hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnlarge : (((∑ j : Fin r, N j : ℕ)) : ℝ) + R + 1 < n := hn₀.trans_le (by exact_mod_cast hn)
  have hNR : R < n := by
    have hNsum : 0 ≤ (((∑ j : Fin r, N j : ℕ)) : ℝ) := by positivity
    linarith
  have hNrank (j : Fin r) : N j ≤ n := by
    have hsum : (∑ j : Fin r, N j : ℕ) ≤ n := by
      exact_mod_cast (show (((∑ j : Fin r, N j : ℕ)) : ℝ) ≤ n by linarith)
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hsum
  let D (i : I) := degreeScale n ((rank i).val + 1) (SharedBasePattern.extensionEdges 2 ((rank i).val + 1)).card (α i)
  let F := (i : I) × Equiv.Perm (Fin (2 + ((rank i).val + 1)))
  let H (s : F) := (G s.1).comap (MultipartiteCounting.roleEquiv s.2)
  let B (s : F) := MultipartiteExtension.bases (t := 2) (H s) \ typicalBases (H s) (η (rank s.1) / 4)
  let a (s : F) := θ * α s.1 * (n : ℝ) ^ 2
  let b (s : F) := η (rank s.1) * α s.1 * (n : ℝ) ^ 2 / (32 * L (rank s.1))
  let c (s : F) := η (rank s.1) ^ 3 * α s.1 * (n : ℝ) ^ 2 * (D s.1) ^ 2 / (128 * L (rank s.1))
  have hαpos (i : I) : 0 < α i := hα₀.trans_le (hα i)
  have hDpos (i : I) : 0 < D i := by
    have hαi := hαpos i
    dsimp only [D, degreeScale]
    positivity
  have hfloor (s : F) (j k : Fin (2 + ((rank s.1).val + 1))) (hjk : j < k) :
      δ ≤ pairDensity (H s) (j, k) := MultipartiteCounting.role_density (G s.1) s.2 δ (hd s.1) j k hjk
  have hbad (s : F) : ((B s).card : ℝ) ≤ ζ (rank s.1) * (n : ℝ) ^ 2 := by
    have h := hconcentration (rank s.1) n hnpos (H s) ε hε (hsmall.trans_le (hεsmall _))
      (MultipartiteCounting.role_regular (G s.1) s.2 ε (hregular s.1)) (hfloor s)
    have heq : B s = (MultipartiteExtension.bases (t := 2) (H s)).filter (fun x =>
        η (rank s.1) / 4 * MultipartiteExtension.prediction (H s) ≤
          |CliqueExtension.count (MultipartiteExtension.extensionRelation (H s)) x - MultipartiteExtension.prediction (H s)|) := by
      ext x
      simp only [B, typicalBases, Finset.mem_sdiff, Finset.mem_filter, not_and, not_lt]
      tauto
    rw [heq]
    exact h
  have hbudget : (∑ s : F, centeredSamplingBudget n ((rank s.1).val + 1) (α s.1) δ (a s) (b s) (c s)) < θ / 4 := by
    rw [Fintype.sum_sigma]
    have hinner (i : I) : (∑ σ : Equiv.Perm (Fin (2 + ((rank i).val + 1))),
        centeredSamplingBudget n ((rank i).val + 1) (α i) δ (a ⟨i, σ⟩) (b ⟨i, σ⟩) (c ⟨i, σ⟩)) ≤ K₀ / n := by
      simp only [a, b, c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h := centeredSamplingBudget_le n ((rank i).val + 1)
        (SharedBasePattern.extensionEdges 2 ((rank i).val + 1)).card hnpos (by omega)
        (α i) α₀ δ (η (rank i)) (L (rank i)) θ hα₀ (hα i) hδ (hη _) (hL _) hθ
      exact h.trans (div_le_div_of_nonneg_right (hKbound (rank i)) hn'.le)
    calc
      _ ≤ ∑ _ : I, K₀ / n := Finset.sum_le_sum (fun i _ => hinner i)
      _ = (Fintype.card I : ℝ) * K₀ / n := by simp; ring
      _ ≤ (M : ℝ) * K₀ / n := by
        apply div_le_div_of_nonneg_right _ hn'.le
        apply mul_le_mul_of_nonneg_right _ hK₀.le
        exact_mod_cast hI
      _ < θ / 4 := by
        apply (div_lt_iff₀ hn').mpr
        have hmul := (div_lt_iff₀ hθ).mp hNR
        nlinarith only [hmul]
  let emb (s : F) := (roleCoordinateEquiv s.2).toEmbedding.trans (e s.1)
  let localScore (s : F) (X : W → J) := centeredSamplingScore (H s) (B s) (α s.1) (a s) (b s) (c s)
    (fun v => CategoricalSampling.projection (label s.1) X (emb s v))
  let localBudget (s : F) := centeredSamplingBudget n ((rank s.1).val + 1) (α s.1) δ (a s) (b s) (c s)
  have ha (s : F) : 0 < a s := by have hαs := hαpos s.1; dsimp only [a]; positivity
  have hb (s : F) : 0 < b s := by
    have hαs := hαpos s.1
    have hηs := hη (rank s.1)
    have hLs := hL (rank s.1)
    dsimp only [b]
    positivity
  have hc (s : F) : 0 < c s := by
    have hαs := hαpos s.1
    have hηs := hη (rank s.1)
    have hLs := hL (rank s.1)
    have hDs := hDpos s.1
    dsimp only [c]
    positivity
  have hprob' (s : F) (v : Coordinate (2 + ((rank s.1).val + 1)) (Fin n)) :
      q (emb s v) (label s.1) = partProbability (normalizedProbability (H s) (α s.1)) v := by
    change q (e s.1 (roleCoordinateEquiv s.2 v)) (label s.1) = _
    rw [hprob]
    exact normalizedProbability_role (G s.1) (α s.1) s.2 v
  have hmeanScore (s : F) : (∑ X, CategoricalSampling.weight q X * localScore s X) ≤ localBudget s := by
    rw [CategoricalSampling.projection_embedding_expectation q htotal (label s.1) (emb s)]
    have hfun : (fun v => q (emb s v) (label s.1)) = partProbability (normalizedProbability (H s) (α s.1)) := funext (hprob' s)
    rw [hfun]
    simpa only [Fintype.card_fin] using centeredSamplingScore_expectation (H s) (hαpos s.1).le
      (hαδ s.1) hδ (hfloor s) (B s) (a s) (b s) (c s) (hc s)
  obtain ⟨X, hwX, hXall⟩ := FiniteSampling.exists_positive_all_scores_lt_one (CategoricalSampling.weight q)
    (CategoricalSampling.weight_nonneg q hq) (CategoricalSampling.total q htotal)
    (fun (o : Option F) X => match o with | none => Z X | some s => localScore s X)
    (fun o X => by
      cases o with
      | none => exact hZ X
      | some s => exact centeredSamplingScore_nonneg (H s) (B s) (α s.1) (a s) (b s) (c s) (hc s).le _)
    (fun (o : Option F) => match o with | none => 1 - θ | some s => localBudget s)
    (fun o => by cases o with | none => exact hZmean | some s => exact hmeanScore s)
    (by
      rw [Fintype.sum_option]
      change 1 - θ + (∑ s : F, localBudget s) < 1
      dsimp only [localBudget]
      linarith only [hbudget, hθ])
  have hX := fun s : F => centeredSamplingScore_controls (H s) (B s) (α s.1) (a s) (b s) (c s)
    (ha s) (hb s) (hc s) (fun v => CategoricalSampling.projection (label s.1) X (emb s v)) (hXall (some s))
  simp only [Fintype.card_fin] at hX
  refine ⟨X, hwX, hXall none, ?_⟩
  intro i
  let Y := fun v => CategoricalSampling.projection (label i) X (e i v)
  have hcontrol : ∀ σ : Equiv.Perm (Fin (2 + ((rank i).val + 1))),
      let H := (G i).comap (MultipartiteCounting.roleEquiv σ)
      let Z := fun v => Y (roleCoordinateEquiv σ v)
      |((retainedBases (MultipartiteExtension.bases (t := 2) H) Z).card : ℝ) - α i * (n : ℝ) ^ 2| < α i * (n : ℝ) ^ 2 / 2 ∧
      ((retainedBases ((MultipartiteExtension.bases (t := 2) H) \ typicalBases H (η (rank i) / 4)) Z).card : ℝ) <
        η (rank i) * α i * (n : ℝ) ^ 2 / (16 * L (rank i)) ∧
      retainedSquaredError (extensions H) (partProbability (normalizedProbability H (α i))) Z < c ⟨i, σ⟩ := by
    intro σ
    have hs := hX ⟨i, σ⟩
    have hmean : retainedBaseMean (H ⟨i, σ⟩) (B ⟨i, σ⟩) (α i) ≤ b ⟨i, σ⟩ := by
      have hp := normalized_baseProbability_le (H ⟨i, σ⟩) (hαpos i).le hδ
        (hfloor ⟨i, σ⟩ _ _ (by change (0 : ℕ) < 1; omega))
      have hp0 : 0 ≤ baseProbability (t := 2) (normalizedProbability (H ⟨i, σ⟩) (α i)) := by
        apply Finset.prod_nonneg
        intro d _
        exact (normalizedProbability_bounds (H ⟨i, σ⟩) (hαpos i).le (hαδ i) hδ (hfloor ⟨i, σ⟩)
          (Fin.castAdd ((rank i).val + 1) d.1, Fin.castAdd ((rank i).val + 1) d.2)).1
      have hζi := hζ (rank i)
      have hmul := mul_le_mul (hbad ⟨i, σ⟩) hp hp0
        (by positivity : 0 ≤ ζ (rank i) * (n : ℝ) ^ 2)
      dsimp only [retainedBaseMean]
      apply hmul.trans_eq
      dsimp only [ζ, b]
      field_simp [hδ.ne', (hL (rank i)).ne']
    refine ⟨hs.1.trans_le ?_, lt_of_lt_of_le hs.2.1 ?_, hs.2.2⟩
    · dsimp only [a]
      have h := mul_le_mul_of_nonneg_right hθhalf (mul_nonneg (hαpos i).le (sq_nonneg (n : ℝ)))
      nlinarith only [h]
    · calc
        _ ≤ b ⟨i, σ⟩ + b ⟨i, σ⟩ := add_le_add hmean (le_refl _)
        _ = _ := by
          dsimp only [b]
          field_simp [(hL (rank i)).ne']
          ring
  obtain ⟨hDi, hcodegi, _⟩ := hsize (rank i) n (hNrank _) (α i) (hα i)
  obtain ⟨T, hT, hdisj, hcard⟩ := hpack (rank i) n hnpos (G i) (α i) (hαpos i) (hd i) hDi hcodegi Y hcontrol
  refine ⟨T, hT, hdisj, hcard, ?_⟩
  intro σ
  have hs := (hX ⟨i, σ⟩).1
  apply hs.trans_le
  dsimp only [a]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθρ (hαpos i).le) (sq_nonneg (n : ℝ))

end Erdos1017.TransversalClique
