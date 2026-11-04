module

public import Erdos1017.Multipartite.Multipartite
public import Erdos1017.SelectedModel.MultipartiteValue.FiniteMultipartiteBenchmark
public import Erdos1017.FractionalLimit.FractionalGraphDelete
public import Erdos1017.IntegerTransfer.CliquePackingSampling
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Data.Fintype.BigOperators

/-!
# Benchmark bound for finite complete multipartite graphs

The edge count and normalized density of a finite complete multipartite graph
are determined by its independent-class cardinalities, and its normalized
fractional value satisfies the benchmark upper bound at its own normalized edge
density (`normalized_value_le_benchmark`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.Multipartite

open scoped BigOperators

/-- Every nonnegative finite mass vector has an actual feasible weighted
multipartite clique law, obtained from independent inclusion and scaling. -/
theorem exists_primal_feasible {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) : ∃ w, PrimalFeasible a w := by
  classical
  let M := 1 + ∑ i, a i
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
    dsimp [M]
    linarith
  let p := fun i => a i / M
  have hp (i : ι) : 0 ≤ p i ∧ p i ≤ 1 := by
    refine ⟨div_nonneg (ha i) hM.le, (div_le_one hM).mpr ?_⟩
    have hi := Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ i)
    dsimp [M]
    linarith
  let w := fun X : Selection ι => if Nontrivial X then M ^ 2 * CliqueSampling.weight p X else 0
  refine ⟨w, ?_, ?_, ?_⟩
  · intro X
    dsimp [w]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (CliqueSampling.weight_nonneg p hp X)
    · rfl
  · intro X hX
    simp [w, hX]
  · intro i j hij
    have hterm (X : Selection ι) : w X * (Selector.bit (X i) * Selector.bit (X j)) =
        M ^ 2 * (CliqueSampling.weight p X * (Selector.bit (X i) * Selector.bit (X j))) := by
      by_cases hX : Nontrivial X
      · simp only [w, hX, ite_true]
        ring
      · have hbits : Selector.bit (X i) * Selector.bit (X j) = 0 := by
          cases hi : X i <;> cases hj : X j <;> norm_num [Selector.bit]
          exact False.elim (hX ⟨i, j, hij, hi, hj⟩)
        simp only [w, hX, ite_false, hbits, mul_zero]
    simp_rw [hterm, ← Finset.mul_sum]
    rw [CliqueSampling.bernoulli_pair_moment p i j hij]
    dsimp [p]
    field_simp

end Erdos1017.Multipartite

namespace Erdos1017.FractionalMultipartite

open scoped BigOperators

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual vertices of one class of a finite vertex-class map. -/
abbrev ClassVertices (π : Fin n → ι) (i : ι) := {v : Fin n // π v = i}

/-- The actual cardinal mass of one independent class. -/
def classMass (π : Fin n → ι) (i : ι) : ℝ := Fintype.card (ClassVertices π i)

/-- Uniform independent choice of one actual vertex in every class. -/
def uniformWeight (π : Fin n → ι) (_f : ∀ i, ClassVertices π i) : ℝ :=
  ∏ i, (classMass π i)⁻¹

theorem uniformWeight_nonneg (π : Fin n → ι) (f : ∀ i, ClassVertices π i) :
    0 ≤ uniformWeight π f := by
  unfold uniformWeight classMass
  positivity

/-- Product observables of the actual uniform class choices factor exactly. -/
theorem uniform_product_expectation (π : Fin n → ι)
    (h : ∀ i, ClassVertices π i → ℝ) :
    (∑ f : ∀ i, ClassVertices π i, uniformWeight π f * ∏ i, h i (f i)) =
      ∏ i, (classMass π i)⁻¹ * ∑ v, h i v := by
  simp only [uniformWeight, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (v : ClassVertices π i) => (classMass π i)⁻¹ * h i v)]
  simp only [← Finset.mul_sum]

theorem uniform_total (π : Fin n → ι) (hπ : Function.Surjective π) :
    ∑ f : ∀ i, ClassVertices π i, uniformWeight π f = 1 := by
  have hmass (i : ι) : classMass π i ≠ 0 := by
    obtain ⟨v, hv⟩ := hπ i
    let _ : Nonempty (ClassVertices π i) := ⟨⟨v, hv⟩⟩
    dsimp [classMass]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassVertices π i)).ne'
  have h := uniform_product_expectation π (fun _ _ => 1)
  have hprod : (∏ i, (classMass π i)⁻¹ * ∑ _v : ClassVertices π i, (1 : ℝ)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change (classMass π i)⁻¹ * classMass π i = 1
    exact inv_mul_cancel₀ (hmass i)
  simpa only [Finset.prod_const_one, mul_one] using h.trans hprod

omit [Fintype ι] in
theorem classMass_pos (π : Fin n → ι) (hπ : Function.Surjective π) (i : ι) :
    0 < classMass π i := by
  obtain ⟨v, hv⟩ := hπ i
  let _ : Nonempty (ClassVertices π i) := ⟨⟨v, hv⟩⟩
  dsimp [classMass]
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ClassVertices π i))

omit [Fintype ι] in
/-- Each actual class has exactly one representative equal to a fixed vertex. -/
theorem class_indicator_sum (π : Fin n → ι) (i : ι) (a : Fin n) (ha : π a = i) :
    (∑ v : ClassVertices π i, if v.val = a then (1 : ℝ) else 0) = 1 := by
  have heq (v : ClassVertices π i) : v.val = a ↔ v = ⟨a, ha⟩ :=
    ⟨fun hv => Subtype.ext hv, fun hv => congrArg Subtype.val hv⟩
  simp only [heq]
  simp

/-- Independent uniform class choices give the exact two-vertex marginal
on each actual inter-class edge. -/
theorem uniform_pair_probability (π : Fin n → ι) (hπ : Function.Surjective π)
    (i j : ι) (hij : i ≠ j) (a b : Fin n) (ha : π a = i) (hb : π b = j) :
    (∑ f : ∀ k, ClassVertices π k, uniformWeight π f *
      (if (f i).val = a ∧ (f j).val = b then (1 : ℝ) else 0)) =
        (classMass π i)⁻¹ * (classMass π j)⁻¹ := by
  classical
  let h := fun (k : ι) (v : ClassVertices π k) =>
    (if k = i then (if v.val = a then (1 : ℝ) else 0) else 1) *
      (if k = j then (if v.val = b then (1 : ℝ) else 0) else 1)
  have hprod (f : ∀ k, ClassVertices π k) :
      (∏ k, h k (f k)) = if (f i).val = a ∧ (f j).val = b then (1 : ℝ) else 0 := by
    dsimp only [h]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    by_cases hi : (f i).val = a <;> by_cases hj : (f j).val = b <;> simp [hi, hj]
  have hfactor (k : ι) : (classMass π k)⁻¹ * (∑ v, h k v) =
      (if k = i then (classMass π i)⁻¹ else 1) *
        (if k = j then (classMass π j)⁻¹ else 1) := by
    by_cases hki : k = i
    · subst k
      simp only [h, ite_true, ite_false, hij, mul_one]
      rw [class_indicator_sum π i a ha]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [h, hki, ite_false, ite_true, one_mul]
        rw [class_indicator_sum π j b hb]
        ring
      · simp only [h, hki, hkj, ite_false, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one]
        change (classMass π k)⁻¹ * classMass π k = 1
        exact inv_mul_cancel₀ (classMass_pos π hπ k).ne'
  have hmean := uniform_product_expectation π h
  simp_rw [hprod, hfactor] at hmean
  rw [Finset.prod_mul_distrib] at hmean
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, ite_true] using hmean

/-- The actual vertex subset chosen by one class selection and one tuple of
uniform representatives. -/
def transversalVertices (π : Fin n → ι) (X : Multipartite.Selection ι)
    (f : ∀ i, ClassVertices π i) : Finset (Fin n) :=
  (Finset.univ.filter (fun i => X i = true)).image (fun i => (f i).val)

omit [DecidableEq ι] in
theorem mem_transversalVertices (π : Fin n → ι) (X : Multipartite.Selection ι)
    (f : ∀ i, ClassVertices π i) (a : Fin n) :
    a ∈ transversalVertices π X f ↔ X (π a) = true ∧ (f (π a)).val = a := by
  simp only [transversalVertices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hia⟩
    have hiπ : i = π a := (f i).property.symm.trans (congrArg π hia)
    subst i
    exact ⟨hi, hia⟩
  · rintro ⟨hX, hf⟩
    exact ⟨π a, hX, hf⟩

omit [DecidableEq ι] in
/-- Distinct chosen representatives lie in distinct independent classes,
so the selected actual subset is a clique of the original graph. -/
theorem transversalVertices_isClique (G : SimpleGraph (Fin n)) (π : Fin n → ι)
    (hgraph : ∀ a b, G.Adj a b ↔ π a ≠ π b)
    (X : Multipartite.Selection ι) (f : ∀ i, ClassVertices π i) :
    G.IsClique (transversalVertices π X f : Set (Fin n)) := by
  intro a ha b hb hab
  obtain ⟨_, hfa⟩ := (mem_transversalVertices π X f a).mp ha
  obtain ⟨_, hfb⟩ := (mem_transversalVertices π X f b).mp hb
  apply (hgraph a b).mpr
  intro hsame
  have hfb' : (f (π a)).val = b := (congrArg (fun i => (f i).val) hsame).trans hfb
  exact hab (hfa.symm.trans hfb')

omit [DecidableEq ι] in
theorem transversal_pair_indicator (π : Fin n → ι) (X : Multipartite.Selection ι)
    (f : ∀ i, ClassVertices π i) (a b : Fin n) :
    (if a ∈ transversalVertices π X f ∧ b ∈ transversalVertices π X f then (1 : ℝ) else 0) =
      (Selector.bit (X (π a)) * Selector.bit (X (π b))) *
        (if (f (π a)).val = a ∧ (f (π b)).val = b then (1 : ℝ) else 0) := by
  simp only [mem_transversalVertices]
  cases ha : X (π a) <;> cases hb : X (π b) <;> simp [Selector.bit]

/-- Every feasible finite weighted multipartite law lifts uniformly to an
actual fractional edge partition of the original finite graph. -/
theorem value_le_cost_of_primal (G : SimpleGraph (Fin n)) (π : Fin n → ι)
    (hπ : Function.Surjective π) (hgraph : ∀ a b, G.Adj a b ↔ π a ≠ π b)
    (w : Multipartite.Selection ι → ℝ) (hw : Multipartite.PrimalFeasible (classMass π) w) :
    FractionalGraph.value G ≤ Multipartite.cost w := by
  classical
  let μ := fun ω : Multipartite.Selection ι × (∀ i, ClassVertices π i) => w ω.1 * uniformWeight π ω.2
  let F := fun ω : Multipartite.Selection ι × (∀ i, ClassVertices π i) => transversalVertices π ω.1 ω.2
  have hμ (ω : Multipartite.Selection ι × (∀ i, ClassVertices π i)) : 0 ≤ μ ω :=
    mul_nonneg (hw.1 _) (uniformWeight_nonneg π _)
  have hfeasible : FractionalGraph.SubsetFeasible G (FractionalGraph.sampleWeights μ F) := by
    refine ⟨FractionalGraph.sampleWeights_nonneg μ F hμ,
      FractionalGraph.sampleWeights_supported G μ F (fun ω => transversalVertices_isClique G π hgraph ω.1 ω.2), ?_⟩
    intro a b hab
    have hij : π a ≠ π b := (hgraph a b).mp hab
    rw [FractionalGraph.sampleWeights_pairLoad μ F a b hab.ne, Fintype.sum_prod_type]
    have hinner (X : Multipartite.Selection ι) :
        (∑ f : ∀ i, ClassVertices π i, μ (X, f) *
          (if a ∈ F (X, f) ∧ b ∈ F (X, f) then (1 : ℝ) else 0)) =
          w X * (Selector.bit (X (π a)) * Selector.bit (X (π b))) *
            ((classMass π (π a))⁻¹ * (classMass π (π b))⁻¹) := by
      dsimp only [μ, F]
      simp_rw [transversal_pair_indicator]
      rw [show (∑ f : ∀ i, ClassVertices π i,
          (w X * uniformWeight π f) * ((Selector.bit (X (π a)) * Selector.bit (X (π b))) *
            (if (f (π a)).val = a ∧ (f (π b)).val = b then (1 : ℝ) else 0))) =
          (w X * (Selector.bit (X (π a)) * Selector.bit (X (π b)))) *
            (∑ f : ∀ i, ClassVertices π i, uniformWeight π f *
              (if (f (π a)).val = a ∧ (f (π b)).val = b then (1 : ℝ) else 0)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro f _
        ring]
      rw [uniform_pair_probability π hπ (π a) (π b) hij a b rfl rfl]
    simp_rw [hinner, ← Finset.sum_mul, hw.2.2 (π a) (π b) hij]
    field_simp [(classMass_pos π hπ (π a)).ne', (classMass_pos π hπ (π b)).ne']
  have hcost : (∑ ω, μ ω) = Multipartite.cost w := by
    rw [Fintype.sum_prod_type]
    dsimp only [μ]
    simp_rw [← Finset.mul_sum, uniform_total π hπ, mul_one]
    rfl
  exact (FractionalGraph.value_le_subset_cost G _ hfeasible).trans
    ((FractionalGraph.sampleWeights_cost_le μ F hμ).trans_eq hcost)

/-- The actual graph fractional value is bounded by the finite weighted
multipartite infimum of its actual independent-class cardinalities. -/
theorem value_le_multipartite_of_partMap (G : SimpleGraph (Fin n)) (π : Fin n → ι)
    (hπ : Function.Surjective π) (hgraph : ∀ a b, G.Adj a b ↔ π a ≠ π b) :
    FractionalGraph.value G ≤ Multipartite.value (classMass π) := by
  obtain ⟨w, hw⟩ := Multipartite.exists_primal_feasible (classMass π) (by intro i; unfold classMass; positivity)
  apply le_csInf (s := {c | ∃ v, Multipartite.PrimalFeasible (classMass π) v ∧ Multipartite.cost v = c})
    ⟨Multipartite.cost w, w, hw, rfl⟩
  rintro c ⟨v, hv, rfl⟩
  exact value_le_cost_of_primal G π hπ hgraph v hv

/-- Summing an actual class observable over vertices is the class-cardinality
weighted sum, with every vertex counted in its true fibre. -/
theorem sum_class_function (π : Fin n → ι) (f : ι → ℝ) :
    (∑ v : Fin n, f (π v)) = ∑ i, classMass π i * f i := by
  symm
  calc
    _ = ∑ i, ∑ v : ClassVertices π i, f (π v) := by
      apply Finset.sum_congr rfl
      intro i _
      have hpoint (v : ClassVertices π i) : f (π v) = f i := congrArg f v.property
      simp_rw [hpoint]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classMass]
    _ = _ := Fintype.sum_fiberwise π (fun v => f (π v))

theorem sum_class_pair_function (π : Fin n → ι) (f : ι → ι → ℝ) :
    (∑ v : Fin n, ∑ w : Fin n, f (π v) (π w)) =
      ∑ i, ∑ j, classMass π i * classMass π j * f i j := by
  rw [sum_class_function π (fun i => ∑ w : Fin n, f i (π w))]
  simp_rw [sum_class_function π]
  simp only [Finset.mul_sum, mul_assoc]

/-- The actual class cardinalities sum to the actual graph order. -/
theorem classMass_sum (π : Fin n → ι) : ∑ i, classMass π i = (n : ℝ) := by
  simpa only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    (sum_class_function π (fun _ => 1)).symm

/-- The graph's exact actual edge count is determined by its actual
independent-class cardinalities. -/
theorem edge_count_eq_class_squares (G : SimpleGraph (Fin n)) (π : Fin n → ι)
    (hgraph : ∀ a b, G.Adj a b ↔ π a ≠ π b) :
    (G.edgeSet.ncard : ℝ) = ((n : ℝ) ^ 2 - ∑ i, (classMass π i) ^ 2) / 2 := by
  classical
  have hcount : (∑ a : Fin n, ∑ b : Fin n, if G.Adj a b then (1 : ℝ) else 0) =
      2 * (G.edgeSet.ncard : ℝ) := by exact_mod_cast FractionalGraph.ordered_edge_count G
  have hclasses : (∑ a : Fin n, ∑ b : Fin n, if G.Adj a b then (1 : ℝ) else 0) =
      (n : ℝ) ^ 2 - ∑ i, (classMass π i) ^ 2 := by
    simp_rw [hgraph]
    rw [sum_class_pair_function π (fun i j => if i ≠ j then (1 : ℝ) else 0)]
    have hterm (i j : ι) : classMass π i * classMass π j * (if i ≠ j then (1 : ℝ) else 0) =
        classMass π i * classMass π j - (if j = i then (classMass π i) ^ 2 else 0) := by
      by_cases hij : i = j
      · subst j; simp [pow_two]
      · simp [hij, Ne.symm hij]
    simp_rw [hterm, Finset.sum_sub_distrib]
    have htotal : (∑ i, ∑ j, classMass π i * classMass π j) = (n : ℝ) ^ 2 := by
      simp_rw [← Finset.mul_sum, classMass_sum]
      rw [← Finset.sum_mul, classMass_sum]
      ring
    simp only [htotal, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  linarith

/-- Normalized actual class masses give the graph's exact normalized density. -/
theorem normalized_density_eq_class_squares (G : SimpleGraph (Fin n)) (π : Fin n → ι)
    (hn : 0 < n) (hgraph : ∀ a b, G.Adj a b ↔ π a ≠ π b) :
    (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 =
      (1 - ∑ i, (classMass π i / n) ^ 2) / 2 := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [edge_count_eq_class_squares G π hgraph]
  simp_rw [div_pow, ← Finset.sum_div]
  field_simp

/-- Normalizing the actual class law gives the required actual graph
fractional upper comparison at total mass one. -/
theorem normalized_value_le_multipartite_of_partMap (G : SimpleGraph (Fin n)) (π : Fin n → ι)
    (hn : 0 < n) (hπ : Function.Surjective π) (hgraph : ∀ a b, G.Adj a b ↔ π a ≠ π b) :
    FractionalGraph.value G / (n : ℝ) ^ 2 ≤ Multipartite.value (fun i => classMass π i / n) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  let a := fun i => classMass π i / n
  have ha : ∀ i, 0 ≤ a i := by intro i; dsimp [a, classMass]; positivity
  obtain ⟨w, hw⟩ := Multipartite.exists_primal_feasible a ha
  apply le_csInf (s := {c | ∃ v, Multipartite.PrimalFeasible a v ∧ Multipartite.cost v = c})
    ⟨Multipartite.cost w, w, hw, rfl⟩
  rintro c ⟨v, hv, rfl⟩
  have hscaled := Multipartite.scale_feasible a v hv (n : ℝ)
  have hmass : (fun i => (n : ℝ) * a i) = classMass π := by
    funext i
    dsimp [a]
    field_simp
  rw [hmass] at hscaled
  have hcost := value_le_cost_of_primal G π hπ hgraph _ hscaled
  rw [Multipartite.scale_cost] at hcost
  apply (div_le_iff₀ (sq_pos_of_pos hnreal)).mpr
  nlinarith

/-- Mathlib's complete-multipartite predicate supplies the actual finite
class quotient, its true vertex cardinalities and exact graph comparisons. -/
theorem exists_actual_class_model (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (hG : G.IsCompleteMultipartite) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a : ι → ℝ),
      (∀ i, 0 ≤ a i) ∧ (∑ i, a i = 1) ∧
      (G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2 = (1 - ∑ i, (a i) ^ 2) / 2 ∧
      FractionalGraph.value G / (n : ℝ) ^ 2 ≤ Multipartite.value a := by
  classical
  let Q := Quotient hG.setoid
  let π : Fin n → Q := Quotient.mk hG.setoid
  have hπ : Function.Surjective π := Quotient.mk_surjective
  have hgraph (a b : Fin n) : G.Adj a b ↔ π a ≠ π b := by
    change G.Adj a b ↔ ¬(Quotient.mk hG.setoid a = Quotient.mk hG.setoid b)
    rw [Quotient.eq]
    change G.Adj a b ↔ ¬¬G.Adj a b
    tauto
  let a := fun i : Q => classMass π i / n
  have hnonneg : ∀ i, 0 ≤ a i := by intro i; dsimp [a, classMass]; positivity
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : ∑ i, a i = 1 := by
    dsimp only [a]
    rw [← Finset.sum_div, classMass_sum, div_self hnreal]
  exact ⟨Q, inferInstance, inferInstance, a, hnonneg, hsum,
    normalized_density_eq_class_squares G π hn hgraph,
    normalized_value_le_multipartite_of_partMap G π hn hπ hgraph⟩

/-- Every actual finite complete multipartite graph satisfies the original
benchmark upper bound at its own exact normalized edge density. -/
theorem normalized_value_le_benchmark (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (hG : G.IsCompleteMultipartite) :
    FractionalGraph.value G / (n : ℝ) ^ 2 ≤
      benchmark ((G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2) := by
  obtain ⟨ι, hι, hdec, a, ha, hsum, hdensity, hvalue⟩ := exists_actual_class_model G hn hG
  rw [hdensity]
  exact hvalue.trans (Multipartite.value_le_benchmark a ha hsum)

/-- The same actual graph comparison in the original quadratic scale. -/
theorem value_le_benchmark_mul_sq (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (hG : G.IsCompleteMultipartite) :
    FractionalGraph.value G ≤
      benchmark ((G.edgeSet.ncard : ℝ) / (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_iff₀ (sq_pos_of_pos hnreal)).mp (normalized_value_le_benchmark G hn hG)

end Erdos1017.FractionalMultipartite
