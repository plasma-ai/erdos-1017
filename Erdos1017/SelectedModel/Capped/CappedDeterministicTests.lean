module

public import Erdos1017.SelectedModel.Capped.CappedSecondPositiveDirection
public import Erdos1017.Models.Capped.CappedColorConfiguration
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Scalar clique tests for deterministic sampled coordinates

Binary adjacency moments and a deterministic sampled shifted color force both
sampled coordinates to equal their Boolean and scalar kernels, so the sampled
color tests are equivalent to the scalar physical tuple tests at every order
(`fullFeasible_of_scalar_orders`).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open scoped Classical in
def positiveAdjacency (W : Model Ω μ) (m : ℝ) (x y : Ω) : Bool :=
  if 0 < shiftedMoment W m (x, y) then true else false

theorem positiveAdjacency_value (W : Model Ω μ) (m : ℝ) (p : Ω × Ω) :
    (if positiveAdjacency W m p.1 p.2 then (1 : ℝ) else 0) =
      (if 0 < shiftedMoment W m p then 1 else 0) := by
  classical
  change (if (if 0 < shiftedMoment W m p then true else false) then (1 : ℝ) else 0) = _
  by_cases hp : 0 < shiftedMoment W m p <;> simp [hp]

theorem positiveAdjacency_symm (W : Model Ω μ) (m : ℝ) :
    ∀ᵐ p ∂μ.prod μ, positiveAdjacency W m p.1 p.2 = positiveAdjacency W m p.2 p.1 := by
  filter_upwards [shiftedMoment_symm W m] with p hp
  change (if 0 < shiftedMoment W m p then true else false) =
    (if 0 < shiftedMoment W m p.swap then true else false)
  rw [hp]

theorem boolean_shift_eq (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ p ∂μ.prod μ, chargeKernel W p.1 p.2 + (-m) *
      (if positiveAdjacency W m p.1 p.2 then 1 else 0) = shiftedKernel W m p.1 p.2 := by
  filter_upwards [hA] with p hp
  rw [positiveAdjacency_value, ← hp]
  change W.moment CappedColor.charge p + (-m) * W.moment CappedColor.adjacency p = shiftedMoment W m p
  rw [shiftedMoment_eq]
  ring

theorem boolean_missing_charge_zero (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0) :
    ∀ᵐ p ∂μ.prod μ, positiveAdjacency W m p.1 p.2 = false → chargeKernel W p.1 p.2 = 0 := by
  filter_upwards [hA] with p hp
  intro hfalse
  have hval := positiveAdjacency_value W m p
  rw [hfalse] at hval
  change (0 : ℝ) = (if 0 < shiftedMoment W m p then 1 else 0) at hval
  have hzero : W.moment CappedColor.adjacency p = 0 := hp.trans hval.symm
  exact charge_moment_of_adjacency_zero W p hzero

/-- Actual binary adjacency moments and deterministic sampled shifted color
force both sampled coordinates to equal their Boolean/scalar kernels. -/
theorem ae_deterministic_coordinates (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p) :
    ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p,
      CappedColor.adjacency c = (if positiveAdjacency W m p.1 p.2 then 1 else 0) ∧
        CappedColor.charge c = chargeKernel W p.1 p.2 := by
  classical
  filter_upwards [hA, hdet] with p hA hdet
  have ha : ∀ᵐ c ∂W.kernel p, CappedColor.adjacency c = W.moment CappedColor.adjacency p := by
    by_cases hp : 0 < shiftedMoment W m p
    · rw [ite_eq_left hp] at hA
      rw [hA]
      exact ae_adjacency_one_of_moment_one W p hA
    · rw [ite_eq_right hp] at hA
      rw [hA]
      exact ae_adjacency_zero_of_moment_zero W p hA
  filter_upwards [ha, hdet] with c hc hd
  refine ⟨?_, ?_⟩
  · rw [hc, hA]
    change (if 0 < shiftedMoment W m p then 1 else 0) =
      (if (if 0 < shiftedMoment W m p then true else false) then 1 else 0)
    by_cases hp : 0 < shiftedMoment W m p <;> simp [hp]
  · rw [shiftedColor, shiftedMoment_eq, hc] at hd
    change CappedColor.charge c = W.moment CappedColor.charge p
    linarith

omit [MeasurableSpace Ω] in
theorem tupleCharge_eq_upper {n : ℕ} (Y : Ω → Ω → ℝ) (x : Fin n → Ω)
    (hsym : ∀ i j, i ≠ j → Y (x i) (x j) = Y (x j) (x i)) :
    FiniteArity.tupleCharge Y x = ∑ e : CliquePair n, Y (x e.val.1) (x e.val.2) := by
  classical
  let y : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else Y (x i) (x j)
  have hy : ∀ i j, y i j = y j i := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [y, hij, Ne.symm hij, ↓reduceIte]
      exact hsym i j hij
  have hd : ∀ i, y i i = 0 := by intro i; simp [y]
  change (∑ i, ∑ j, y i j) / 2 = _
  rw [ordered_sum_eq_twice_upper y hy hd]
  have hu : (∑ i, ∑ j, if i < j then y i j else 0) =
      ∑ e : CliquePair n, Y (x e.val.1) (x e.val.2) := by
    rw [sum_cliquePair_eq_upper]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [y, hij, hij.ne]
    · simp [hij]
  rw [hu]
  ring

omit [MeasurableSpace Ω] in
theorem tupleClique_iff_sampled_present {n : ℕ} (A : Ω → Ω → Bool) (x : Fin n → Ω)
    (c : CliquePair n → CappedColor)
    (hsym : ∀ i j, i ≠ j → A (x i) (x j) = A (x j) (x i))
    (hc : ∀ e, CappedColor.adjacency (c e) = (if A (x e.val.1) (x e.val.2) then 1 else 0)) :
    FiniteArity.TupleClique A x ↔ ∀ e, CappedColor.adjacency (c e) = 1 := by
  classical
  constructor
  · intro hclique e
    rw [hc e, hclique _ _ e.property.ne]
    rfl
  · intro hpresent i j hij
    have hupper (e : CliquePair n) : A (x e.val.1) (x e.val.2) = true := by
      have h := hpresent e
      rw [hc e] at h
      cases hA : A (x e.val.1) (x e.val.2) <;> simp_all
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hupper ⟨(i, j), hlt⟩
    · rw [hsym i j hij]
      exact hupper ⟨(j, i), hgt⟩

omit [MeasurableSpace Ω] in
theorem violation_eq_zero_iff_scalar_test {n : ℕ} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (x : Fin n → Ω) (c : CliquePair n → CappedColor)
    (hAsym : ∀ i j, i ≠ j → A (x i) (x j) = A (x j) (x i))
    (hYsym : ∀ i j, i ≠ j → Y (x i) (x j) = Y (x j) (x i))
    (hc : ∀ e, CappedColor.adjacency (c e) = (if A (x e.val.1) (x e.val.2) then 1 else 0) ∧
      CappedColor.charge (c e) = Y (x e.val.1) (x e.val.2)) :
    violation c = 0 ↔ (FiniteArity.TupleClique A x → FiniteArity.tupleCharge Y x ≤ 1) := by
  classical
  have hclique := tupleClique_iff_sampled_present A x c hAsym (fun e => (hc e).1)
  by_cases hpresent : ∀ e, CappedColor.adjacency (c e) = 1
  · have hprod : (∏ e, CappedColor.adjacency (c e)) = 1 := by simp only [hpresent, Finset.prod_const_one]
    have hcharge : (∑ e, CappedColor.charge (c e)) = FiniteArity.tupleCharge Y x := by
      rw [tupleCharge_eq_upper Y x hYsym]
      exact Finset.sum_congr rfl (fun e _ => (hc e).2)
    rw [violation, hprod, mul_one, hcharge]
    simp only [max_eq_right_iff, sub_nonpos, hclique.mpr hpresent, true_implies]
  · have hnot : ¬ FiniteArity.TupleClique A x := fun h => hpresent (hclique.mp h)
    push Not at hpresent
    obtain ⟨e, he⟩ := hpresent
    have hzero : CappedColor.adjacency (c e) = 0 :=
      (CappedColor.adjacency_eq_zero_or_one (c e)).resolve_right he
    have hprod : (∏ e, CappedColor.adjacency (c e)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) hzero
    simp only [violation, hprod, mul_zero, hnot, false_implies]

variable [IsProbabilityMeasure μ]

/-- The actual independently sampled color test is equivalent to the
Boolean/scalar physical tuple test after the two sampled coordinates have
been proved deterministic. The equivalence uses product-null statements
at the actual sampled order. -/
theorem sampled_test_iff_feasibleOrder (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (n : ℕ) :
    (∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ), ∀ᵐ c ∂cliqueLaw W x, violation c = 0) ↔
      FiniteArity.FeasibleOrder μ (positiveAdjacency W m) (chargeKernel W) n := by
  have hcoords := ae_deterministic_coordinates W m hA hdet
  have hpairs := FiniteArity.ae_all_pairs μ n _
    (hcoords.and ((positiveAdjacency_symm W m).and (chargeKernel_symm W)))
  apply Filter.eventually_congr
  filter_upwards [hpairs] with x hx
  have hcolors : ∀ᵐ c ∂cliqueLaw W x, ∀ e,
      CappedColor.adjacency (c e) =
          (if positiveAdjacency W m (x e.val.1) (x e.val.2) then 1 else 0) ∧
        CappedColor.charge (c e) = chargeKernel W (x e.val.1) (x e.val.2) := by
    apply ae_all_iff.mpr
    intro e
    have hμ := measurePreserving_eval (fun e : CliquePair n => W.kernel (x e.val.1, x e.val.2)) e
    exact hμ.quasiMeasurePreserving.ae ((hx e.val.1 e.val.2 e.property.ne).1)
  have hAsym := fun i j hij => (hx i j hij).2.1
  have hYsym := fun i j hij => (hx i j hij).2.2
  constructor
  · intro htest
    obtain ⟨c, hc, hzero⟩ := (hcolors.and htest).exists
    exact (violation_eq_zero_iff_scalar_test _ _ x c hAsym hYsym hc).mp hzero
  · intro htest
    filter_upwards [hcolors] with c hc
    exact (violation_eq_zero_iff_scalar_test _ _ x c hAsym hYsym hc).mpr htest

theorem feasible_iff_scalar_orders (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (r : ℕ) : Feasible r W ↔ ∀ n, 2 ≤ n → n ≤ r →
      FiniteArity.FeasibleOrder μ (positiveAdjacency W m) (chargeKernel W) n := by
  constructor
  · intro h n hn hnr
    exact (sampled_test_iff_feasibleOrder W m hA hdet n).mp (h n hn hnr)
  · intro h n hn hnr
    exact (sampled_test_iff_feasibleOrder W m hA hdet n).mpr (h n hn hnr)

theorem fullFeasible_of_scalar_orders (W : Model Ω μ) (m : ℝ)
    (hA : ∀ᵐ p ∂μ.prod μ, W.moment CappedColor.adjacency p =
      if 0 < shiftedMoment W m p then 1 else 0)
    (hdet : ∀ᵐ p ∂μ.prod μ, ∀ᵐ c ∂W.kernel p, shiftedColor m c = shiftedMoment W m p)
    (htests : ∀ n, FiniteArity.FeasibleOrder μ (positiveAdjacency W m) (chargeKernel W) n) :
    FullFeasible W := by
  intro r
  exact (feasible_iff_scalar_orders W m hA hdet r).mpr (fun n _ _ => htests n)

end Erdos1017.CappedModel
