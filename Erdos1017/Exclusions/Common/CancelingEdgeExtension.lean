module

public import Erdos1017.Models.PhysicalPrimal.TupleSampling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Inserting canceling edges on a rectangle

This module defines the extended adjacency and charge obtained by inserting
canceling edges on a symmetric rectangle `extensionPair`, proves measurability,
symmetry and the charge box, and shows that a recipient set can acquire
canceling edges while preserving every clique test
(`feasibleOrder_extension_of_single_root`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos1017.FiniteArity

/-- Deleting a set of leaves cannot decrease charge when every leaf's
root and distinguished-head incidences cancel and all its other
incidences are nonpositive. -/
theorem pairCharge_le_filter_of_canceling_leaves {α : Type*} [DecidableEq α]
    (U : Finset α) (Y : α → α → ℝ) (i j : α) (hi : i ∈ U) (hj : j ∈ U)
    (hij : i ≠ j) (E : Set α) [DecidablePred (· ∈ E)]
    (hiE : i ∉ E) (hjE : j ∉ E)
    (hsym : ∀ a b, Y a b = Y b a)
    (hcancel : ∀ k ∈ U, k ∈ E → Y i k + Y j k = 0)
    (hbody : ∀ k ∈ U, k ∈ E → ∀ b ∈ U, b ≠ i → b ≠ j → Y k b ≤ 0) :
    pairCharge U Y ≤ pairCharge (U.filter (· ∉ E)) Y := by
  let w (a : α) : ℝ := if a ∈ E then Y i a else 0
  let Z (a b : α) : ℝ := (if a ∈ E ∨ b ∈ E then 0 else Y a b) +
    (if a = i then w b else 0) + (if b = i then w a else 0) -
    (if a = j then w b else 0) - (if b = j then w a else 0)
  have hZsym (a b : α) : Z a b = Z b a := by
    have hbase : (if a ∈ E ∨ b ∈ E then 0 else Y a b) =
        (if b ∈ E ∨ a ∈ E then 0 else Y b a) := by
      by_cases ha : a ∈ E <;> by_cases hb : b ∈ E <;> simp [ha, hb, hsym a b]
    unfold Z
    rw [hbase]
    ring
  have hrow (a : α) (ha : a ∈ U) (haE : a ∈ E) (b : α) (hb : b ∈ U) :
      Y a b ≤ Z a b := by
    have hai : a ≠ i := fun he => hiE (he ▸ haE)
    have haj : a ≠ j := fun he => hjE (he ▸ haE)
    by_cases hbi : b = i
    · subst b
      simp [Z, haE, hai, haj, hij, w, hsym a i]
    · by_cases hbj : b = j
      · subst b
        have hc := hcancel a ha haE
        simp [Z, haE, hai, haj, hij.symm, w, hsym a j]
        linarith
      · have h := hbody a ha haE b hb hbi hbj
        simpa [Z, haE, hai, haj, hbi, hbj] using h
  have hbound : ∀ a ∈ U, ∀ b ∈ U, Y a b ≤ Z a b := by
    intro a ha b hb
    by_cases haE : a ∈ E
    · exact hrow a ha haE b hb
    · by_cases hbE : b ∈ E
      · rw [hsym a b, hZsym a b]
        exact hrow b hb hbE a ha
      · simp [Z, haE, hbE, w]
  have hsum : pairCharge U Z = pairCharge (U.filter (· ∉ E)) Y := by
    unfold pairCharge crossSum
    have hbase : (∑ a ∈ U, ∑ b ∈ U, if a ∈ E ∨ b ∈ E then 0 else Y a b) =
        ∑ a ∈ U.filter (· ∉ E), ∑ b ∈ U.filter (· ∉ E), Y a b := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases haE : a ∈ E <;> simp [haE]
    simp only [Z, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', hi, hj, ite_true]
    rw [hbase]
    ring
  rw [← hsum]
  unfold pairCharge crossSum
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hbound a ha b hb)))
    (by norm_num)

/-- The symmetric rectangle on which new canceling edges are inserted. -/
abbrev extensionPair {Ω : Type*} (J E : Set Ω) (x y : Ω) : Prop :=
  (x ∈ J ∧ y ∈ E) ∨ (y ∈ J ∧ x ∈ E)

/-- Insert the actual rectangle, retaining every old incidence elsewhere. -/
def extensionAdjacency {Ω : Type*} (A : Ω → Ω → Bool) (J E : Set Ω)
    [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)] (x y : Ω) : Bool :=
  if extensionPair J E x y then true else A x y

/-- The added charge cancels the exterior vertex's root charge. -/
def extensionCharge {Ω : Type*} (Y : Ω → Ω → ℝ) (s : Ω → ℝ) (J E : Set Ω)
    [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)] (x y : Ω) : ℝ :=
  if extensionPair J E x y then -(E.indicator s x + E.indicator s y) else Y x y

/-- The actual insertion rectangle is measurable. -/
theorem measurableSet_extensionPair {Ω : Type*} [MeasurableSpace Ω]
    (J E : Set Ω) (hJ : MeasurableSet J) (hE : MeasurableSet E) :
    MeasurableSet {p : Ω × Ω | extensionPair J E p.1 p.2} :=
  ((hJ.preimage measurable_fst).inter (hE.preimage measurable_snd)).union
    ((hJ.preimage measurable_snd).inter (hE.preimage measurable_fst))

/-- Measurable scalar inputs give a measurable extended graph. -/
theorem measurable_extensionAdjacency {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)]
    (hJ : MeasurableSet J) (hE : MeasurableSet E) :
    Measurable (Function.uncurry (extensionAdjacency A J E)) :=
  measurable_const.ite (measurableSet_extensionPair J E hJ hE) hA

/-- Measurable scalar inputs give the actual measurable extended charge. -/
theorem measurable_extensionCharge {Ω : Type*} [MeasurableSpace Ω]
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (s : Ω → ℝ) (hs : Measurable s)
    (J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)]
    (hJ : MeasurableSet J) (hE : MeasurableSet E) :
    Measurable (Function.uncurry (extensionCharge Y s J E)) :=
  (((hs.indicator hE).comp measurable_fst).add
    ((hs.indicator hE).comp measurable_snd)).neg.ite
      (measurableSet_extensionPair J E hJ hE) hY

theorem extensionAdjacency_symm {Ω : Type*} (A : Ω → Ω → Bool)
    (hA : ∀ x y, A x y = A y x)
    (J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)] (x y : Ω) :
    extensionAdjacency A J E x y = extensionAdjacency A J E y x := by
  simp only [extensionAdjacency, extensionPair, or_comm, hA x y]

theorem extensionCharge_symm {Ω : Type*} (Y : Ω → Ω → ℝ) (s : Ω → ℝ)
    (hY : ∀ x y, Y x y = Y y x)
    (J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)] (x y : Ω) :
    extensionCharge Y s J E x y = extensionCharge Y s J E y x := by
  simp only [extensionCharge, extensionPair, or_comm, add_comm, hY x y]

/-- Disjoint recipient and exterior sets keep every added charge in the
original compact color box. -/
theorem extensionCharge_mem_Icc {Ω : Type*} (Y : Ω → Ω → ℝ) (s : Ω → ℝ)
    (hY : ∀ x y, Y x y ∈ Icc (-3 : ℝ) 1) (hs : ∀ x, s x ∈ Icc (0 : ℝ) 1)
    (J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)]
    (hJE : Disjoint J E) (x y : Ω) : extensionCharge Y s J E x y ∈ Icc (-3 : ℝ) 1 := by
  unfold extensionCharge
  split_ifs with hp
  · rcases hp with hp | hp
    · have hx : x ∉ E := fun hx => Set.disjoint_left.mp hJE hp.1 hx
      simp only [indicator_of_notMem hx, indicator_of_mem hp.2, zero_add]
      constructor <;> linarith [(hs y).1, (hs y).2]
    · have hy : y ∉ E := fun hy => Set.disjoint_left.mp hJE hp.1 hy
      simp only [indicator_of_mem hp.2, indicator_of_notMem hy, add_zero]
      constructor <;> linarith [(hs x).1, (hs x).2]
  · exact hY x y

theorem extensionCharge_zero_of_nonedge {Ω : Type*}
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (s : Ω → ℝ)
    (hzero : ∀ x y, A x y = false → Y x y = 0)
    (J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)] (x y : Ω)
    (h : extensionAdjacency A J E x y = false) : extensionCharge Y s J E x y = 0 := by
  unfold extensionAdjacency at h
  unfold extensionCharge
  split_ifs at h ⊢ with hp
  exact hzero x y h

/-- A recipient set can acquire canceling edges while preserving
all original clique tests. Each new rooted clique is compared with its
actual old subclique; rootless cliques have nonpositive charge. -/
theorem feasibleOrder_extension_of_single_root
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (s : Ω → ℝ)
    (hYsym : ∀ x y, Y x y = Y y x)
    (R J E : Set Ω) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ E)]
    (hRJ : Disjoint R J) (hRE : Disjoint R E) (hJE : Disjoint J E)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0)
    (hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ E → Y p.1 p.2 = s p.2)
    (hs : ∀ᵐ x ∂μ, x ∈ E → 0 ≤ s x)
    (hfull : ∀ n, FeasibleOrder μ A Y n) (n : ℕ) :
    FeasibleOrder μ (extensionAdjacency A J E) (extensionCharge Y s J E) n := by
  classical
  have hpairs := ae_all_pairs μ n _ (hroot.and (hbody.and hstar))
  have hpoints : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ), ∀ i, v i ∈ E → 0 ≤ s (v i) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => μ) i).quasiMeasurePreserving.ae hs
  have hsub := ae_all_subtuples μ n n
    (fun _ v => TupleClique A v → tupleCharge Y v ≤ 1) (fun r _ => hfull r)
  filter_upwards [hpairs, hpoints, hsub] with v hp hs hv hclique
  let Z := extensionCharge Y s J E
  let z (i j : Fin n) : ℝ := if i = j then 0 else Z (v i) (v j)
  have hRnotJ {x : Ω} (hx : x ∈ R) : x ∉ J := fun hy => Set.disjoint_left.mp hRJ hx hy
  have hRnotE {x : Ω} (hx : x ∈ R) : x ∉ E := fun hy => Set.disjoint_left.mp hRE hx hy
  have hJnotE {x : Ω} (hx : x ∈ J) : x ∉ E := fun hy => Set.disjoint_left.mp hJE hx hy
  have hZsym (x y : Ω) : Z x y = Z y x := by
    simp only [Z, extensionCharge, extensionPair, or_comm, add_comm, hYsym x y]
  have hzsym (i j : Fin n) : z i j = z j i := by
    by_cases hij : i = j
    · simp [z, hij]
    · simp [z, hij, Ne.symm hij, hZsym]
  have hnonpos {i j : Fin n} (hi : v i ∉ R) (hj : v j ∉ R) : z i j ≤ 0 := by
    by_cases hij : i = j
    · simp [z, hij]
    · dsimp only [z, Z]
      rw [ite_eq_right hij]
      unfold extensionCharge
      split_ifs
      · apply neg_nonpos.mpr
        have h₁ : 0 ≤ E.indicator s (v i) := by
          by_cases hiE : v i ∈ E
          · simpa [hiE] using hs i hiE
          · simp [hiE]
        have h₂ : 0 ≤ E.indicator s (v j) := by
          by_cases hjE : v j ∈ E
          · simpa [hjE] using hs j hjE
          · simp [hjE]
        exact add_nonneg h₁ h₂
      · exact (hp i j hij).2.1 hi hj
  have holdTest (T : Finset (Fin n))
      (hnot : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬extensionPair J E (v i) (v j)) :
      pairCharge T z ≤ 1 := by
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin T.card) : e i ∈ T := T.orderEmbOfFin_mem rfl i
    have hn : T.card ≤ n := by simpa using Finset.card_le_univ T
    have hold : TupleClique A (fun i => v (e i)) := by
      intro i j hij
      have heij : e i ≠ e j := fun h => hij (e.injective h)
      have h := hclique (e i) (e j) heij
      simpa only [extensionAdjacency, ite_eq_right (hnot (e i) (he i) (e j) (he j) heij)] using h
    have ht := hv T.card hn e hold
    rw [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ T rfl] at ht
    convert ht using 1
    unfold pairCharge crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · simp [z, hij]
    · simp only [z, hij, ite_false, Z, extensionCharge, ite_eq_right (hnot i hi j hj hij)]
  by_cases hR : ∃ i, v i ∈ R
  · obtain ⟨i, hi⟩ := hR
    have hrootUnique {k : Fin n} (hk : v k ∈ R) : k = i := by
      by_contra hki
      have hold := (hp k i hki).1 hk hi
      have hnew := hclique k i hki
      have hnot : ¬extensionPair J E (v k) (v i) := by
        simp [extensionPair, hRnotJ hk, hRnotJ hi]
      simp only [extensionAdjacency, ite_eq_right hnot, hold] at hnew
      contradiction
    by_cases hJ : ∃ j, v j ∈ J
    · obtain ⟨j, hj⟩ := hJ
      have hij : i ≠ j := fun he => hRnotJ hi (he ▸ hj)
      have hle := pairCharge_le_filter_of_canceling_leaves Finset.univ z i j
        (Finset.mem_univ _) (Finset.mem_univ _) hij (v ⁻¹' E)
        (hRnotE hi) (hJnotE hj) hzsym
      have hc : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ∈ v ⁻¹' E → z i k + z j k = 0 := by
        intro k _ hk
        change v k ∈ E at hk
        have hik : i ≠ k := fun he => hRnotE hi (he ▸ hk)
        have hjk : j ≠ k := fun he => hJnotE hj (he ▸ hk)
        have hr := (hp i k hik).2.2 hi hk
        simp [z, Z, extensionCharge, extensionPair, hik, hjk, hRnotJ hi,
          hRnotE hi, hJnotE hj, hj, hk, hr]
      have hb : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ∈ v ⁻¹' E →
          ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ i → b ≠ j → z k b ≤ 0 := by
        intro k _ hk b _ hbi _
        apply hnonpos
        · exact fun hkR => hRnotE hkR hk
        · exact fun hbR => hbi (hrootUnique hbR)
      change pairCharge Finset.univ z ≤ 1
      apply (hle hc hb).trans
      apply holdTest
      intro a ha b hb _
      have haE := (Finset.mem_filter.mp ha).2
      have hbE := (Finset.mem_filter.mp hb).2
      simp only [mem_preimage] at haE hbE
      simp [extensionPair, haE, hbE]
    · change pairCharge Finset.univ z ≤ 1
      apply holdTest
      intro a _ b _ _
      have haJ : v a ∉ J := fun h => hJ ⟨a, h⟩
      have hbJ : v b ∉ J := fun h => hJ ⟨b, h⟩
      simp [extensionPair, haJ, hbJ]
  · have hle : pairCharge Finset.univ z ≤ 0 := by
      unfold pairCharge crossSum
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
      apply Finset.sum_nonpos
      intro i _
      apply Finset.sum_nonpos
      intro j _
      exact hnonpos (fun h => hR ⟨i, h⟩) (fun h => hR ⟨j, h⟩)
    exact hle.trans (by norm_num)

end Erdos1017.FiniteArity
