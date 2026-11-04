module

public import Erdos1017.IntegerTransfer.Nibble.HypergraphNibbleDegreeBounds

/-!
# First- and second-order bounds on the next-round degree mean

Near-regular degrees and small codegrees give explicit bounds on the conditional
survival exponent of an incident edge, and hence explicit first- and
second-order bounds on the next-round degree mean in a uniform hypergraph whose
degrees lie between `L` and `D` (`prospectiveDegree_mean_bounds`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.HypergraphNibble

open scoped BigOperators

/-- A coarse Bonferroni bound, sufficient when pair intersections have small codegree. -/
theorem sum_card_le_union_add_overlap {I A : Type*} [DecidableEq I] [DecidableEq A]
    (P : Finset I) (B : I → Finset A) (c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ((B i ∩ B j).card : ℝ) ≤ c) :
    (∑ i ∈ P, ((B i).card : ℝ)) ≤ ((P.biUnion B).card : ℝ) + P.card ^ 2 * c := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    have hpairs : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → ((B i ∩ B j).card : ℝ) ≤ c :=
      fun i hi j hj hij => hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hprior := ih hpairs
    have hinter : B a ∩ P.biUnion B = P.biUnion (fun i => B a ∩ B i) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_biUnion]
      aesop
    have hinter_bound : ((B a ∩ P.biUnion B).card : ℝ) ≤ P.card * c := by
      calc
        _ ≤ ∑ i ∈ P, ((B a ∩ B i).card : ℝ) := by
          rw [hinter]
          exact_mod_cast (Finset.card_biUnion_le (s := P) (t := fun i => B a ∩ B i))
        _ ≤ ∑ i ∈ P, c := Finset.sum_le_sum (fun i hi =>
          hpair a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
            (by intro h; subst i; exact ha hi))
        _ = _ := by simp
    have hcard : ((B a ∪ P.biUnion B).card : ℝ) + ((B a ∩ P.biUnion B).card : ℝ) =
        ((B a).card : ℝ) + ((P.biUnion B).card : ℝ) := by
      exact_mod_cast Finset.card_union_add_card_inter (B a) (P.biUnion B)
    rw [Finset.sum_insert ha, Finset.biUnion_insert, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    have hk : 0 ≤ (P.card : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc
    nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem blockers_eq_union_stars (H : Finset (Finset V)) (v : V) (e : Finset V) :
    blockers H v e = (e.erase v).biUnion (fun u => incident H {u} \ incident H {v}) := by
  simp only [blockers, incident_singleton]
  ext f
  simp only [incident, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hfH, u, hu⟩, hnot⟩
    obtain ⟨huf, hue⟩ := Finset.mem_inter.mp hu
    have hvf : v ∉ f := by intro hv; exact hnot ⟨hfH, hv⟩
    exact ⟨u, ⟨by intro h; subst u; exact hvf huf, hue⟩, ⟨hfH, huf⟩, hnot⟩
  · rintro ⟨u, ⟨_, hue⟩, ⟨hfH, huf⟩, hnot⟩
    exact ⟨⟨hfH, u, Finset.mem_inter.mpr ⟨huf, hue⟩⟩, hnot⟩

omit [Fintype V] in
private theorem star_inter_card (H : Finset (Finset V)) (u v : V) :
    (incident H {u} ∩ incident H {v}).card = codegree H u v := by
  congr 1
  ext f
  simp only [incident_singleton, Finset.mem_inter, Finset.mem_filter]
  tauto

omit [Fintype V] in
/-- Near-regular degrees and small codegrees give explicit bounds on the conditional
survival exponent of an incident edge. Only the other vertices of that edge need degree bounds. -/
theorem blockers_card_bounds (H : Finset (Finset V)) (v : V) (e : Finset V)
    (L D c : ℝ) (hc : 0 ≤ c)
    (hdegree : ∀ u ∈ e.erase v, L ≤ (degree H u : ℝ) ∧ (degree H u : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) :
    ((e.erase v).card : ℝ) * (L - c) - (e.erase v).card ^ 2 * c ≤ (blockers H v e).card ∧
      ((blockers H v e).card : ℝ) ≤ (e.erase v).card * D := by
  classical
  let B (u : V) := incident H {u} \ incident H {v}
  have hrow (u : V) (hu : u ∈ e.erase v) : L - c ≤ ((B u).card : ℝ) ∧ ((B u).card : ℝ) ≤ D := by
    have hcount : ((B u).card : ℝ) + (codegree H u v : ℝ) = degree H u := by
      have h := Finset.card_sdiff_add_card_inter (incident H {u}) (incident H {v})
      rw [star_inter_card] at h
      have hnat : (B u).card + codegree H u v = degree H u := by
        simpa only [B, degree, incident_singleton] using h
      exact_mod_cast hnat
    have hcode := hcodegree u v (Finset.mem_erase.mp hu).1
    have hdeg := hdegree u hu
    have hnonneg : 0 ≤ (codegree H u v : ℝ) := Nat.cast_nonneg _
    constructor <;> linarith
  have hpair : ∀ u ∈ e.erase v, ∀ w ∈ e.erase v, u ≠ w → ((B u ∩ B w).card : ℝ) ≤ c := by
    intro u _ w _ huw
    have hsub : B u ∩ B w ⊆ incident H {u} ∩ incident H {w} := by
      intro f hf
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).2).1⟩
    have hcount := Finset.card_le_card hsub
    rw [star_inter_card] at hcount
    have hcast : ((B u ∩ B w).card : ℝ) ≤ codegree H u w := by exact_mod_cast hcount
    exact hcast.trans (hcodegree u w huw)
  have hlow := sum_card_le_union_add_overlap (e.erase v) B c hc hpair
  have hsumlow : ((e.erase v).card : ℝ) * (L - c) ≤ ∑ u ∈ e.erase v, ((B u).card : ℝ) := by
    calc
      _ = ∑ u ∈ e.erase v, (L - c) := by simp [mul_sub]
      _ ≤ _ := Finset.sum_le_sum (fun u hu => (hrow u hu).1)
  have hunion : (e.erase v).biUnion B = blockers H v e := (blockers_eq_union_stars H v e).symm
  rw [hunion] at hlow
  refine ⟨by linarith, ?_⟩
  calc
    ((blockers H v e).card : ℝ) ≤ ∑ u ∈ e.erase v, ((B u).card : ℝ) := by
      rw [← hunion]
      exact_mod_cast (Finset.card_biUnion_le (s := e.erase v) (t := B))
    _ ≤ ∑ u ∈ e.erase v, D := Finset.sum_le_sum (fun u hu => (hrow u hu).2)
    _ = _ := by simp

/-- The elementary second-order estimate used to track a small nibble round. -/
theorem survival_power_bounds (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    1 - (k : ℝ) * p ≤ (1 - p) ^ k ∧
      (1 - p) ^ k ≤ 1 - (k : ℝ) * p + (k : ℝ) ^ 2 * p ^ 2 := by
  constructor
  · have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) k
    convert h using 1
    ring
  · induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.cast_succ]
      have h := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1)
      have hthird : 0 ≤ (k : ℝ) ^ 2 * p ^ 3 := mul_nonneg (sq_nonneg _) (pow_nonneg hp _)
      have hsecond : 0 ≤ ((k : ℝ) + 1) * p ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
      nlinarith

/-- Explicit first- and second-order bounds for the next-round degree mean in a
uniform hypergraph whose vertices have degrees between `L` and `D`. -/
theorem prospectiveDegree_mean_bounds (H : Finset (Finset V)) (p L D c : ℝ) (r : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 ≤ c)
    (huniform : ∀ e ∈ H, e.card = r)
    (hdegree : ∀ u, L ≤ (degree H u : ℝ) ∧ (degree H u : ℝ) ≤ D)
    (hcodegree : ∀ u w, u ≠ w → (codegree H u w : ℝ) ≤ c) (v : V) :
    (degree H v : ℝ) * (1 - p * ((r - 1 : ℕ) * D)) ≤
        (∑ X, CliqueSampling.weight (fun _ => p) X * prospectiveDegree H X v) ∧
      (∑ X, CliqueSampling.weight (fun _ => p) X * prospectiveDegree H X v) ≤
        (degree H v : ℝ) * (1 - p * ((r - 1 : ℕ) * (L - c) - (r - 1 : ℕ) ^ 2 * c) +
          ((r - 1 : ℕ) * D) ^ 2 * p ^ 2) := by
  classical
  rw [prospectiveDegree_expectation, ← Finset.sum_filter]
  have hterm (e : Finset V) (he : e ∈ H.filter (fun e => v ∈ e)) :
      1 - p * ((r - 1 : ℕ) * D) ≤ (1 - p) ^ (blockers H v e).card ∧
      (1 - p) ^ (blockers H v e).card ≤
        1 - p * ((r - 1 : ℕ) * (L - c) - (r - 1 : ℕ) ^ 2 * c) +
          ((r - 1 : ℕ) * D) ^ 2 * p ^ 2 := by
    obtain ⟨heH, hev⟩ := Finset.mem_filter.mp he
    have hk : (e.erase v).card = r - 1 := by
      rw [Finset.card_erase_of_mem hev, huniform e heH]
    have hb := blockers_card_bounds H v e L D c hc (fun u _ => hdegree u) hcodegree
    rw [hk] at hb
    have hpow := survival_power_bounds p hp hp1 (blockers H v e).card
    have hmulhi := mul_le_mul_of_nonneg_left hb.2 hp
    have hmullow := mul_le_mul_of_nonneg_left hb.1 hp
    have hsq : ((blockers H v e).card : ℝ) ^ 2 ≤ ((r - 1 : ℕ) * D) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ (blockers H v e).card from Nat.cast_nonneg _]
    have hsqp := mul_le_mul_of_nonneg_right hsq (sq_nonneg p)
    constructor <;> nlinarith
  constructor
  · calc
      _ = ∑ e ∈ H.filter (fun e => v ∈ e), (1 - p * ((r - 1 : ℕ) * D)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, degree]
      _ ≤ _ := Finset.sum_le_sum (fun e he => (hterm e he).1)
  · calc
      _ ≤ ∑ e ∈ H.filter (fun e => v ∈ e),
          (1 - p * ((r - 1 : ℕ) * (L - c) - (r - 1 : ℕ) ^ 2 * c) +
            ((r - 1 : ℕ) * D) ^ 2 * p ^ 2) := Finset.sum_le_sum (fun e he => (hterm e he).2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, degree]

end Erdos1017.HypergraphNibble
