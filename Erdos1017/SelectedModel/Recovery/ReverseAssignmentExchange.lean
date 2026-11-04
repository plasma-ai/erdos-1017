module

public import Erdos1017.SelectedModel.Recovery.ReverseAssignmentMinimizer
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Data.Finset.Max
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Exchange arguments for the minimizing reverse assignment

A squared-mass minimizer sends no atomic receipt from a source with diffuse
supply, nor into a larger atom from a source allowed a smaller one, so one
feasible assignment yields a minimizer with a finite positive top plateau
receiving only from the compulsory source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Erdos1017.ReverseAssignment

private theorem tsum_sub_eq_sum_of_eq_off {u v : ℕ → ℝ} (hu : Summable u)
    (hv : Summable v) (J : Finset ℕ) (heq : ∀ i ∉ J, u i = v i) :
    (∑' i, u i) - ∑' i, v i = ∑ i ∈ J, (u i - v i) := by
  rw [← hu.tsum_sub hv]
  apply tsum_eq_sum
  intro i hi
  rw [heq i hi, sub_self]

private theorem exists_positive_finite_argmax {u : ℕ → ℝ} (hu : Summable u)
    (hpositive : ∃ i, 0 < u i) :
    ∃ t : ℝ, 0 < t ∧ ∃ P : Finset ℕ, P.Nonempty ∧
      (∀ i, u i ≤ t) ∧ (∀ i, u i = t ↔ i ∈ P) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hpositive
  have hnear : ∀ᶠ i in cofinite, u i < u i₀ / 2 :=
    hu.tendsto_cofinite_zero.eventually_lt_const (by linarith)
  have hfinite : {i | u i₀ / 2 ≤ u i}.Finite := by
    apply (mem_cofinite.mp hnear).subset
    intro i hi
    change u i₀ / 2 ≤ u i at hi
    change ¬u i < u i₀ / 2
    exact not_lt.mpr hi
  let F := hfinite.toFinset
  have hi₀F : i₀ ∈ F := by
    exact hfinite.mem_toFinset.mpr (by dsimp; linarith)
  obtain ⟨i, hiF, hmax⟩ := F.exists_max_image u ⟨i₀, hi₀F⟩
  have hit : 0 < u i := hi₀.trans_le (hmax i₀ hi₀F)
  have hglobal (j : ℕ) : u j ≤ u i := by
    by_cases hj : j ∈ F
    · exact hmax j hj
    · have hjlt : u j < u i₀ / 2 := lt_of_not_ge (fun h => hj (hfinite.mem_toFinset.mpr h))
      linarith [hmax i₀ hi₀F]
  refine ⟨u i, hit, F.filter (fun j => u j = u i), ?_, hglobal, ?_⟩
  · exact ⟨i, Finset.mem_filter.mpr ⟨hiF, rfl⟩⟩
  · intro j
    constructor
    · intro hj
      apply Finset.mem_filter.mpr
      refine ⟨hfinite.mem_toFinset.mpr ?_, hj⟩
      change u i₀ / 2 ≤ u j
      rw [hj]
      linarith [hmax i₀ hi₀F]
    · exact fun hj => (Finset.mem_filter.mp hj).2

/-- The entire original source whose nonempty allowed-label set is
contained in the displayed plateau and has no diffuse supply. -/
def compulsorySource {Ω : Type*} (allowed : ℕ → Set Ω) (δ : Ω → ℝ)
    (P : Finset ℕ) : Set Ω :=
  {x | δ x = 0 ∧ (∃ i, x ∈ allowed i) ∧ ∀ i, x ∈ allowed i → i ∈ P}

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- The compulsory source is a measurable set defined by the original
allowed-label sections, without a chosen subset of sources. -/
theorem measurableSet_compulsorySource {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ) (P : Finset ℕ) :
    MeasurableSet (compulsorySource allowed δ P) := by
  have hsubset (i : ℕ) : MeasurableSet {x | x ∈ allowed i → i ∈ P} := by
    by_cases hi : i ∈ P
    · have heq : {x | x ∈ allowed i → i ∈ P} = univ := by
        ext x
        simp only [mem_ofPred_eq, hi, implies_true, mem_univ]
      rw [heq]
      exact MeasurableSet.univ
    · have heq : {x | x ∈ allowed i → i ∈ P} = (allowed i)ᶜ := by
        ext x
        simp only [mem_ofPred_eq, hi, imp_false, mem_compl_iff]
      rw [heq]
      exact (hallowed i).compl
  simp only [compulsorySource, ofPred_and, ofPred_exists, ofPred_forall, ofPred_mem_eq]
  exact (measurableSet_eq_fun hδ measurable_const).inter
    ((MeasurableSet.iUnion hallowed).inter (MeasurableSet.iInter hsubset))

omit [IsFiniteMeasure μ] in
private theorem feasible_delete_coordinate {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) (i : ℕ) (h : Lp ℝ 2 μ)
    (hh0 : ∀ᵐ x ∂μ, 0 ≤ h x) (hhle : ∀ᵐ x ∂μ, h x ≤ q i x)
    (hpattern : ∀ J : Finset ℕ, ∀ᵐ x ∂μ.restrict (finitePattern allowed δ J), h x = 0) :
    Feasible allowed δ (Function.update q i (q i - h)) := by
  classical
  let q' := Function.update q i (q i - h)
  have heq : ∀ᵐ x ∂μ, ∀ k, q' k x = q k x - if k = i then h x else 0 := by
    filter_upwards [Lp.coeFn_sub (q i) h] with x hx k
    by_cases hk : k = i
    · subst k
      simpa only [q', Function.update_self, ite_true, Pi.sub_apply] using hx
    · simp only [q', Function.update_of_ne hk, hk, ite_false, sub_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    filter_upwards [heq, hh0, hhle, hq.box k] with x he hx0 hle hb
    rw [he k]
    by_cases hk : k = i
    · subst k
      simp only [ite_true]
      exact ⟨by linarith, by linarith [hb.2]⟩
    · simpa only [hk, ite_false, sub_zero] using hb
  · intro k
    filter_upwards [heq, hh0, hhle, hq.support k] with x he hx0 hle hs hx
    rw [he k, hs hx]
    by_cases hk : k = i
    · subst k
      have hh : h x = 0 := le_antisymm (by simpa only [hs hx] using hle) hx0
      simp only [ite_true, hh, sub_self]
    · simp only [hk, ite_false, sub_zero]
  · intro J
    filter_upwards [heq, hh0, hq.partial_sum J] with x he hx0 hp
    calc
      ∑ k ∈ J, q' k x ≤ ∑ k ∈ J, q k x := by
        apply Finset.sum_le_sum
        intro k hk
        rw [he k]
        by_cases hki : k = i <;> simp only [hki, ite_true, ite_false, sub_zero]
        · linarith
        · exact le_rfl
      _ ≤ 1 := hp
  · intro J
    filter_upwards [ae_restrict_of_ae heq, hq.full_pattern J, hpattern J] with x he hp hh
    calc
      ∑ k ∈ J, q' k x = ∑ k ∈ J, q k x := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [he k, hh]
        simp only [ite_self, sub_zero]
      _ = 1 := hp

omit [IsFiniteMeasure μ] in
private theorem feasible_transfer_coordinate {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q) {i j : ℕ} (hij : i ≠ j)
    (h : Lp ℝ 2 μ) (hh0 : ∀ᵐ x ∂μ, 0 ≤ h x) (hhle : ∀ᵐ x ∂μ, h x ≤ q i x)
    (hsupport : ∀ᵐ x ∂μ, x ∉ allowed j → h x = 0) :
    Feasible allowed δ (Function.update (Function.update q i (q i - h)) j (q j + h)) := by
  classical
  let q' := Function.update (Function.update q i (q i - h)) j (q j + h)
  have heq : ∀ᵐ x ∂μ, ∀ k, q' k x = q k x +
      (if k = j then h x else 0) - (if k = i then h x else 0) := by
    filter_upwards [Lp.coeFn_sub (q i) h, Lp.coeFn_add (q j) h] with x hs ha k
    by_cases hki : k = i
    · subst k
      simpa only [q', Function.update_of_ne hij, Function.update_self, hij, ite_false,
        ite_true, add_zero, Pi.sub_apply] using hs
    · by_cases hkj : k = j
      · subst k
        simpa only [q', Function.update_self, hki, ite_false, ite_true, sub_zero,
          Pi.add_apply] using ha
      · simp only [q', Function.update_of_ne hkj, Function.update_of_ne hki, hki, hkj,
          ite_false, add_zero, sub_zero]
  have hsum (x : Ω) (he : ∀ k, q' k x = q k x +
      (if k = j then h x else 0) - (if k = i then h x else 0)) (J : Finset ℕ) :
      ∑ k ∈ J, q' k x = (∑ k ∈ J, q k x) +
        (if j ∈ J then h x else 0) - (if i ∈ J then h x else 0) := by
    simp_rw [he]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    filter_upwards [heq, hh0, hhle, hq.box k, hq.partial_sum {i, j}]
      with x he hx0 hle hb hp
    have hpij : q i x + q j x ≤ 1 := by simpa only [Finset.sum_pair hij] using hp
    rw [he k]
    by_cases hki : k = i
    · subst k
      simp only [hij, ite_false, ite_true, add_zero]
      exact ⟨by linarith, by linarith [hb.2]⟩
    · by_cases hkj : k = j
      · subst k
        simp only [hki, ite_false, ite_true, sub_zero]
        exact ⟨by linarith [hb.1], by linarith⟩
      · simpa only [hki, hkj, ite_false, add_zero, sub_zero] using hb
  · intro k
    filter_upwards [heq, hh0, hhle, hq.support k, hsupport]
      with x he hx0 hle hs hj hx
    rw [he k, hs hx]
    by_cases hki : k = i
    · subst k
      have hh : h x = 0 := le_antisymm (by simpa only [hs hx] using hle) hx0
      simp only [hh, ite_self, add_zero, sub_zero]
    · by_cases hkj : k = j
      · subst k
        simp only [hj hx, ite_self, add_zero, sub_zero]
      · simp only [hki, hkj, ite_false, add_zero, sub_zero]
  · intro J
    filter_upwards [heq, hh0, hhle, hq.partial_sum J, hq.partial_sum (insert i J)]
      with x he hx0 hle hp hins
    rw [hsum x he J]
    by_cases hi : i ∈ J
    · by_cases hj : j ∈ J <;> simp only [hi, hj, ite_true, ite_false] <;> linarith
    · have hplus : (∑ k ∈ J, q k x) + q i x ≤ 1 := by
        rw [Finset.sum_insert hi] at hins
        linarith
      by_cases hj : j ∈ J <;> simp only [hi, hj, ite_true, ite_false] <;> linarith
  · intro J
    filter_upwards [ae_restrict_of_ae heq, ae_restrict_of_ae hh0, ae_restrict_of_ae hhle,
      ae_restrict_of_ae (hq.support i), ae_restrict_of_ae hsupport, hq.full_pattern J,
      ae_restrict_mem (measurableSet_finitePattern hallowed hδ J)]
      with x he hx0 hle hi hs hp hx
    rw [hsum x he J]
    by_cases hh : h x = 0
    · simpa only [hh, ite_self, add_zero, sub_zero] using hp
    · have hqi : q i x ≠ 0 := by
        intro hz
        exact hh (le_antisymm (by simpa only [hz] using hle) hx0)
      have hia : x ∈ allowed i := by
        by_contra hnot
        exact hqi (hi hnot)
      have hja : x ∈ allowed j := by
        by_contra hnot
        exact hh (hs hnot)
      have hiJ : i ∈ J := hx.2 i |>.mpr hia
      have hjJ : j ∈ J := hx.2 j |>.mpr hja
      simpa only [hiJ, hjJ, ite_true, add_sub_cancel_right] using hp

/-- An actual squared-mass minimizer sends no atomic receipt from a source
with nonzero diffuse supply. Deleting the receipt is a derived legal competitor. -/
theorem Feasible.no_diffuse_receipt_of_minimum {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a)
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    (hmin : ∀ q' : ℕ → Lp ℝ 2 μ,
      Feasible allowed δ q' → objective a q ≤ objective a q') (i : ℕ) :
    ∀ᵐ x ∂μ, δ x ≠ 0 → q i x = 0 := by
  classical
  let E := {x | δ x ≠ 0}
  have hE : MeasurableSet E := (measurableSet_eq_fun hδ measurable_const).compl
  have hmem : MemLp (E.indicator (q i)) 2 μ :=
    MemLp.indicator hE.nullMeasurableSet (Lp.memLp (q i))
  let h : Lp ℝ 2 μ := hmem.toLp (E.indicator (q i))
  have heq : ∀ᵐ x ∂μ, h x = E.indicator (q i) x := hmem.coeFn_toLp
  have hh0 : ∀ᵐ x ∂μ, 0 ≤ h x := by
    filter_upwards [heq, hq.box i] with x he hb
    rw [he]
    by_cases hx : x ∈ E
    · simpa only [indicator_of_mem hx] using hb.1
    · simp only [indicator_of_notMem hx, le_refl]
  have hhle : ∀ᵐ x ∂μ, h x ≤ q i x := by
    filter_upwards [heq, hq.box i] with x he hb
    rw [he]
    by_cases hx : x ∈ E
    · simp only [indicator_of_mem hx, le_refl]
    · simpa only [indicator_of_notMem hx] using hb.1
  have hpattern : ∀ J : Finset ℕ,
      ∀ᵐ x ∂μ.restrict (finitePattern allowed δ J), h x = 0 := by
    intro J
    filter_upwards [ae_restrict_of_ae heq,
      ae_restrict_mem (measurableSet_finitePattern hallowed hδ J)] with x he hx
    rw [he]
    exact indicator_of_notMem (show x ∉ E from fun hne => hne hx.1) _
  let q' := Function.update q i (q i - h)
  have hq' : Feasible allowed δ q' := feasible_delete_coordinate hq i h hh0 hhle hpattern
  have hint : Integrable h μ := (Lp.memLp h).integrable (by norm_num)
  let e := ∫ x, h x ∂μ
  have he0 : 0 ≤ e := integral_nonneg_of_ae hh0
  have hemass : e ≤ mass a q i := by
    have hle := integral_mono_ae hint (coordinate_integrable q i) hhle
    dsimp only [mass]
    linarith [ha i]
  have hmassi : mass a q' i = mass a q i - e := by
    simp only [q', mass, Function.update_self]
    rw [integral_congr_ae (Lp.coeFn_sub (q i) h)]
    simp only [Pi.sub_apply]
    rw [integral_sub (coordinate_integrable q i) hint]
    dsimp only [e]
    ring
  have hobj : objective a q' - objective a q =
      (mass a q i - e) ^ 2 - mass a q i ^ 2 := by
    have hsum := tsum_sub_eq_sum_of_eq_off (hq'.square_mass_summable ha haSum)
      (hq.square_mass_summable ha haSum) {i} (fun k hk => by
        have hki : k ≠ i := by simpa only [Finset.mem_singleton] using hk
        simp only [q', mass, Function.update_of_ne hki])
    simpa only [objective, Finset.sum_singleton, hmassi] using hsum
  have hcompare := hmin q' hq'
  have hezero : e = 0 := by
    have hproduct := mul_nonneg he0 (sub_nonneg.mpr hemass)
    nlinarith [sq_nonneg e]
  have hz : ∀ᵐ x ∂μ, h x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hh0 hint).mp hezero
  filter_upwards [heq, hz] with x he hx hδx
  have hxE : x ∈ E := hδx
  simpa only [indicator_of_mem hxE] using he.symm.trans hx

/-- Receipt into a larger final atom cannot come from a source also
allowed to use a smaller one. The legal transfer and objective drop are derived. -/
theorem Feasible.no_receipt_of_mass_lt {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a)
    {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    (hmin : ∀ q' : ℕ → Lp ℝ 2 μ,
      Feasible allowed δ q' → objective a q ≤ objective a q')
    {i j : ℕ} (hlt : mass a q j < mass a q i) :
    ∀ᵐ x ∂μ, x ∈ allowed j → q i x = 0 := by
  classical
  have hij : i ≠ j := by
    intro he
    subst j
    exact (lt_irrefl _ hlt)
  have hmem : MemLp ((allowed j).indicator (q i)) 2 μ :=
    MemLp.indicator (hallowed j).nullMeasurableSet (Lp.memLp (q i))
  let v : Lp ℝ 2 μ := hmem.toLp ((allowed j).indicator (q i))
  have heq : ∀ᵐ x ∂μ, v x = (allowed j).indicator (q i) x := hmem.coeFn_toLp
  have hv : ∀ᵐ x ∂μ, 0 ≤ v x ∧ v x ≤ q i x := by
    filter_upwards [heq, hq.box i] with x he hb
    rw [he]
    by_cases hx : x ∈ allowed j
    · simp only [indicator_of_mem hx, le_refl, and_true]
      exact hb.1
    · simp only [indicator_of_notMem hx, le_refl, true_and]
      exact hb.1
  have hvInt : Integrable v μ := (Lp.memLp v).integrable (by norm_num)
  let e := ∫ x, v x ∂μ
  have he0 : 0 ≤ e := integral_nonneg_of_ae (hv.mono (fun _ hx => hx.1))
  have hezero : e = 0 := by
    by_contra hne
    have hepos : 0 < e := lt_of_le_of_ne he0 (fun hz => hne hz.symm)
    let gap := mass a q i - mass a q j
    have hgap : 0 < gap := sub_pos.mpr hlt
    let θ := min (1 : ℝ) (gap / (2 * e))
    have hθ0 : 0 < θ := lt_min (by norm_num) (div_pos hgap (by positivity))
    have hθle : θ ≤ 1 := min_le_left _ _
    have hεpos : 0 < θ * e := mul_pos hθ0 hepos
    have hεlt : θ * e < gap := by
      have hle := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (gap / (2 * e))) hepos.le
      have hid : gap / (2 * e) * e = gap / 2 := by field_simp
      rw [hid] at hle
      exact hle.trans_lt (by linarith)
    let h : Lp ℝ 2 μ := θ • v
    have hh : ∀ᵐ x ∂μ, h x = θ * v x := by
      filter_upwards [Lp.coeFn_smul θ v] with x hx
      simpa only [Pi.smul_apply, smul_eq_mul] using hx
    have hh0 : ∀ᵐ x ∂μ, 0 ≤ h x := by
      filter_upwards [hh, hv] with x he hx
      rw [he]
      exact mul_nonneg hθ0.le hx.1
    have hhle : ∀ᵐ x ∂μ, h x ≤ q i x := by
      filter_upwards [hh, hv] with x he hx
      rw [he]
      have hmul : θ * v x ≤ v x := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hθle hx.1
      exact hmul.trans hx.2
    have hsupport : ∀ᵐ x ∂μ, x ∉ allowed j → h x = 0 := by
      filter_upwards [hh, heq] with x he hx hnot
      rw [he, hx, indicator_of_notMem hnot, mul_zero]
    let q' := Function.update (Function.update q i (q i - h)) j (q j + h)
    have hq' : Feasible allowed δ q' :=
      feasible_transfer_coordinate hallowed hδ hq hij h hh0 hhle hsupport
    have hInt : Integrable h μ := (Lp.memLp h).integrable (by norm_num)
    have hintegral : (∫ x, h x ∂μ) = θ * e := by
      rw [integral_congr_ae hh, integral_const_mul]
    have hmi : mass a q' i = mass a q i - θ * e := by
      simp only [q', mass, Function.update_of_ne hij, Function.update_self]
      rw [integral_congr_ae (Lp.coeFn_sub (q i) h)]
      simp only [Pi.sub_apply]
      rw [integral_sub (coordinate_integrable q i) hInt, hintegral]
      ring
    have hmj : mass a q' j = mass a q j + θ * e := by
      simp only [q', mass, Function.update_self]
      rw [integral_congr_ae (Lp.coeFn_add (q j) h)]
      simp only [Pi.add_apply]
      rw [integral_add (coordinate_integrable q j) hInt, hintegral]
      ring
    have hobj : objective a q' - objective a q = -2 * (θ * e) * gap + 2 * (θ * e) ^ 2 := by
      have hsum := tsum_sub_eq_sum_of_eq_off (hq'.square_mass_summable ha haSum)
        (hq.square_mass_summable ha haSum) {i, j} (fun k hk => by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          simp only [q', mass, Function.update_of_ne hk.2, Function.update_of_ne hk.1])
      change objective a q' - objective a q = _ at hsum
      rw [hsum, Finset.sum_pair hij, hmi, hmj]
      dsimp only [gap]
      ring
    have hcompare := hmin q' hq'
    have hpositive := mul_pos hεpos (sub_pos.mpr hεlt)
    nlinarith
  have hz : ∀ᵐ x ∂μ, v x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (hv.mono (fun _ hx => hx.1)) hvInt).mp hezero
  filter_upwards [heq, hz] with x he hx hallowedx
  simpa only [indicator_of_mem hallowedx] using he.symm.trans hx

/-- Actual summability and minimization construct the full positive top
plateau and identify all its receipt with the entire compulsory source. -/
theorem Feasible.exists_top_plateau_entire_source {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a)
    (hpositive : ∃ i, 0 < a i) {q : ℕ → Lp ℝ 2 μ} (hq : Feasible allowed δ q)
    (hmin : ∀ q' : ℕ → Lp ℝ 2 μ,
      Feasible allowed δ q' → objective a q ≤ objective a q') :
    ∃ t : ℝ, 0 < t ∧ ∃ P : Finset ℕ, P.Nonempty ∧
      (∀ i, mass a q i ≤ t) ∧ (∀ i, mass a q i = t ↔ i ∈ P) ∧
      (∀ᵐ x ∂μ, (∑ i ∈ P, q i x) = (compulsorySource allowed δ P).indicator (fun _ => 1) x) ∧
      (P.card : ℝ) * t = (∑ i ∈ P, a i) + μ.real (compulsorySource allowed δ P) := by
  classical
  have hmassPositive : ∃ i, 0 < mass a q i := by
    obtain ⟨i, hi⟩ := hpositive
    have hr : 0 ≤ ∫ x, q i x ∂μ :=
      integral_nonneg_of_ae ((hq.box i).mono (fun _ hx => hx.1))
    refine ⟨i, ?_⟩
    dsimp only [mass]
    linarith
  obtain ⟨t, ht, P, hP, hmax, hmaxiff⟩ :=
    exists_positive_finite_argmax (hq.mass_summable ha haSum) hmassPositive
  have hsupport : ∀ᵐ x ∂μ, ∀ i, x ∉ allowed i → q i x = 0 := ae_all_iff.mpr hq.support
  have hdiffuse : ∀ᵐ x ∂μ, ∀ i, δ x ≠ 0 → q i x = 0 :=
    ae_all_iff.mpr (fun i => hq.no_diffuse_receipt_of_minimum hallowed hδ ha haSum hmin i)
  have hpair : ∀ᵐ x ∂μ, ∀ i j, mass a q j < mass a q i → x ∈ allowed j → q i x = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hlt : mass a q j < mass a q i
    · exact (hq.no_receipt_of_mass_lt hallowed hδ ha haSum hmin hlt).mono (fun _ hx _ => hx)
    · exact Eventually.of_forall (fun _ h => False.elim (hlt h))
  have hpatterns : ∀ᵐ x ∂μ, ∀ J : Finset ℕ,
      x ∈ finitePattern allowed δ J → ∑ i ∈ J, q i x = 1 := by
    apply ae_all_iff.mpr
    intro J
    exact (ae_restrict_iff' (measurableSet_finitePattern hallowed hδ J)).mp (hq.full_pattern J)
  have hreceipt : ∀ᵐ x ∂μ,
      (∑ i ∈ P, q i x) = (compulsorySource allowed δ P).indicator (fun _ => 1) x := by
    filter_upwards [hsupport, hdiffuse, hpair, hpatterns] with x hs hd hp hf
    by_cases hx : x ∈ compulsorySource allowed δ P
    · rw [indicator_of_mem hx]
      let J := P.filter (fun i => x ∈ allowed i)
      have hxPattern : x ∈ finitePattern allowed δ J := by
        refine ⟨hx.1, ?_⟩
        intro i
        constructor
        · exact fun hi => (Finset.mem_filter.mp hi).2
        · exact fun hi => Finset.mem_filter.mpr ⟨hx.2.2 i hi, hi⟩
      have hsum : (∑ i ∈ J, q i x) = ∑ i ∈ P, q i x := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hiP hiJ
        apply hs i
        intro hi
        exact hiJ (Finset.mem_filter.mpr ⟨hiP, hi⟩)
      rw [← hsum]
      exact hf J hxPattern
    · rw [indicator_of_notMem hx]
      apply Finset.sum_eq_zero
      intro i hiP
      by_contra hne
      have hia : x ∈ allowed i := by
        by_contra hnot
        exact hne (hs i hnot)
      have hδzero : δ x = 0 := by
        by_contra hnot
        exact hne (hd i hnot)
      have hsubset (j : ℕ) (hj : x ∈ allowed j) : j ∈ P := by
        by_contra hjP
        have hjlt : mass a q j < t := lt_of_le_of_ne (hmax j)
          (fun he => hjP ((hmaxiff j).mp he))
        have hilt : mass a q j < mass a q i := by rwa [(hmaxiff i).mpr hiP]
        exact hne (hp i j hilt hj)
      exact hx ⟨hδzero, ⟨i, hia⟩, hsubset⟩
  have hsumMass : (∑ i ∈ P, mass a q i) = (P.card : ℝ) * t := by
    calc
      (∑ i ∈ P, mass a q i) = ∑ _i ∈ P, t :=
        Finset.sum_congr rfl (fun i hi => (hmaxiff i).mpr hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hsumReceipt : (∑ i ∈ P, ∫ x, q i x ∂μ) = μ.real (compulsorySource allowed δ P) := by
    calc
      (∑ i ∈ P, ∫ x, q i x ∂μ) = ∫ x, ∑ i ∈ P, q i x ∂μ :=
        (integral_finsetSum P (fun i _ => coordinate_integrable q i)).symm
      _ = ∫ x, (compulsorySource allowed δ P).indicator (fun _ => (1 : ℝ)) x ∂μ :=
        integral_congr_ae hreceipt
      _ = _ := by
        rw [integral_indicator (measurableSet_compulsorySource hallowed hδ P), setIntegral_const]
        simp
  refine ⟨t, ht, P, hP, hmax, hmaxiff, hreceipt, ?_⟩
  rw [← hsumMass]
  simp only [mass, Finset.sum_add_distrib, hsumReceipt]

/-- One actual feasible assignment produces an actual minimizing assignment,
its finite positive top plateau and the entire-source mass identity. -/
theorem exists_minimizer_top_plateau {allowed : ℕ → Set Ω} {δ : Ω → ℝ}
    (hallowed : ∀ i, MeasurableSet (allowed i)) (hδ : Measurable δ)
    {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (haSum : Summable a)
    (hpositive : ∃ i, 0 < a i) (q0 : ℕ → Lp ℝ 2 μ) (hq0 : Feasible allowed δ q0) :
    ∃ q : ℕ → Lp ℝ 2 μ, Feasible allowed δ q ∧
      (∀ v : ℕ → Lp ℝ 2 μ, Feasible allowed δ v → objective a q ≤ objective a v) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ P : Finset ℕ, P.Nonempty ∧
        (∀ i, mass a q i ≤ t) ∧ (∀ i, mass a q i = t ↔ i ∈ P) ∧
        (∀ᵐ x ∂μ,
          (∑ i ∈ P, q i x) = (compulsorySource allowed δ P).indicator (fun _ => 1) x) ∧
        (P.card : ℝ) * t = (∑ i ∈ P, a i) + μ.real (compulsorySource allowed δ P) := by
  obtain ⟨q, hq, hmin⟩ := exists_minimizer hallowed hδ ha haSum q0 hq0
  exact ⟨q, hq, hmin, hq.exists_top_plateau_entire_source hallowed hδ ha haSum hpositive hmin⟩

end Erdos1017.ReverseAssignment
