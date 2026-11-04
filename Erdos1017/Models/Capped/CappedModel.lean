module

public import Erdos1017.Models.Decorated.DecoratedKernel
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FunProp

/-!
# Capped models and their basic edits

The capped color space (`cappedColors`) has zero charge on absent pairs and
charge in `[-3,1]` on present pairs; adjacency, objective and both maximality
notions (`IsFixedMeasureMaximizer`, `IsMaximizer`) are defined, and vertex
reweighting and measurable color deletion preserve all imposed tests.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1017

/-- The compact color space: absent pairs have zero charge, and present
pairs have charge in the closed interval `[-3,1]`. -/
def cappedColors : Set (ℝ × ℝ) :=
  ({0} ×ˢ {0}) ∪ ({1} ×ˢ Icc (-3) 1)

abbrev CappedColor := cappedColors

instance : CompactSpace CappedColor :=
  isCompact_iff_compactSpace.mp
    ((isCompact_singleton.prod isCompact_singleton).union
      (isCompact_singleton.prod isCompact_Icc))

namespace CappedColor

def adjacency (c : CappedColor) : ℝ := c.val.1

def charge (c : CappedColor) : ℝ := c.val.2

def absent : CappedColor := ⟨(0, 0), Or.inl ⟨rfl, rfl⟩⟩

def present (y : ℝ) (hy : y ∈ Icc (-3) 1) : CappedColor :=
  ⟨(1, y), Or.inr ⟨rfl, hy⟩⟩

@[fun_prop] theorem continuous_adjacency : Continuous adjacency :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop] theorem continuous_charge : Continuous charge :=
  continuous_snd.comp continuous_subtype_val

theorem adjacency_mem (c : CappedColor) : adjacency c ∈ Icc 0 1 := by
  rcases c.property with h | h
  · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
    simp [adjacency, h.1]
  · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
    simp [adjacency, h.1]

theorem charge_mem (c : CappedColor) : charge c ∈ Icc (-3) 1 := by
  rcases c.property with h | h
  · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
    simp [charge, h.2]
  · exact h.2

theorem adjacency_eq_zero_or_one (c : CappedColor) : adjacency c = 0 ∨ adjacency c = 1 := by
  rcases c.property with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

@[simp] theorem adjacency_absent : adjacency absent = 0 := rfl

@[simp] theorem charge_absent : charge absent = 0 := rfl

end CappedColor

/-- One index for each unordered pair of distinct labeled clique vertices. -/
abbrev CliquePair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

namespace CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω}

abbrev Model (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) :=
  DecoratedKernel Ω CappedColor μ

/-- Each clique pair receives its own independent conditional color. -/
def cliqueLaw (W : Model Ω μ) {n : ℕ} (x : Fin n → Ω) : Measure (CliquePair n → CappedColor) :=
  W.sampleLaw (fun e => (x e.val.1, x e.val.2))

instance (W : Model Ω μ) {n : ℕ} (x : Fin n → Ω) :
    IsProbabilityMeasure (cliqueLaw W x) := by
  unfold cliqueLaw
  infer_instance

def cliqueKernel (W : Model Ω μ) (n : ℕ) : Kernel (Fin n → Ω) (CliquePair n → CappedColor) :=
  W.sampleKernel (fun x e => (x e.val.1, x e.val.2))
    (fun e => (measurable_pi_apply e.val.1).prodMk (measurable_pi_apply e.val.2))

instance (W : Model Ω μ) (n : ℕ) : IsMarkovKernel (cliqueKernel W n) := by
  unfold cliqueKernel
  infer_instance

/-- The nonnegative continuous clique test from capped compactness. -/
def violation {n : ℕ} (c : CliquePair n → CappedColor) : ℝ :=
  max ((∑ e, CappedColor.charge (c e)) - 1) 0 * ∏ e, CappedColor.adjacency (c e)

@[fun_prop] theorem continuous_violation (n : ℕ) :
    Continuous (violation : (CliquePair n → CappedColor) → ℝ) := by
  unfold violation
  fun_prop

theorem violation_nonneg {n : ℕ} (c : CliquePair n → CappedColor) : 0 ≤ violation c := by
  apply mul_nonneg (le_max_right _ _)
  exact Finset.prod_nonneg (fun e _ => (CappedColor.adjacency_mem (c e)).1)

/-- The expected continuous clique violation under the actual two-stage
sampling law: independent vertices, then independent conditional colors. -/
def testIntegral (W : Model Ω μ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Fin n → Ω, ∫⁻ c, ENNReal.ofReal (violation c) ∂cliqueLaw W x
    ∂Measure.pi (fun _ : Fin n => μ)

theorem testIntegral_eq_zero_iff (W : Model Ω μ) (n : ℕ) :
    testIntegral W n = 0 ↔ ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
      ∀ᵐ c ∂cliqueLaw W x, violation c = 0 := by
  have hm : Measurable (fun c : CliquePair n → CappedColor => ENNReal.ofReal (violation c)) :=
    (continuous_violation n).measurable.ennreal_ofReal
  have hinner : Measurable (fun x : Fin n → Ω =>
      ∫⁻ c, ENNReal.ofReal (violation c) ∂cliqueLaw W x) :=
    hm.lintegral_kernel (κ := cliqueKernel W n)
  rw [testIntegral, lintegral_eq_zero_iff hinner]
  apply Filter.eventually_congr
  filter_upwards with x
  simp only [Pi.zero_apply]
  rw [lintegral_eq_zero_iff hm]
  apply Filter.eventually_congr
  filter_upwards with c
  simp only [Pi.zero_apply]
  rw [ENNReal.ofReal_eq_zero]
  exact ⟨fun h => le_antisymm h (violation_nonneg c), fun h => h.le⟩

/-- Feasibility requires only the imposed clique orders. The inner law is
the actual independent color sampling law, rather than a mean-kernel test. -/
def Feasible (r : ℕ) (W : Model Ω μ) : Prop :=
  ∀ n, 2 ≤ n → n ≤ r → ∀ᵐ x ∂Measure.pi (fun _ : Fin n => μ),
    ∀ᵐ c ∂cliqueLaw W x, violation c = 0

theorem feasible_iff_testIntegral (W : Model Ω μ) (r : ℕ) :
    Feasible r W ↔ ∀ n, 2 ≤ n → n ≤ r → testIntegral W n = 0 := by
  simp only [Feasible, testIntegral_eq_zero_iff]

def density (W : Model Ω μ) : ℝ :=
  (∫ p, W.moment CappedColor.adjacency p ∂μ.prod μ) / 2

def objective (W : Model Ω μ) : ℝ :=
  (∫ p, W.moment CappedColor.charge p ∂μ.prod μ) / 2

/-- Capped extremality at one density is stated using the actual feasible
decorated competitors. This definition makes no existence assertion. -/
def IsFixedMeasureMaximizer (r : ℕ) (W : Model Ω μ) : Prop :=
  Feasible r W ∧ ∀ V : Model Ω μ, Feasible r V → density V = density W →
    objective V ≤ objective W

/-- Maximality also compares absolutely continuous latent probability laws.
Transporting this property from a fixed atomless presentation needs its own
proof; it is not supplied by fixed-measure maximality alone. -/
def IsMaximizer (r : ℕ) (W : Model Ω μ) : Prop :=
  Feasible r W ∧ ∀ (ν : Measure Ω) [IsProbabilityMeasure ν], ν ≪ μ →
    ∀ V : Model Ω ν, Feasible r V → density V = density W → objective V ≤ objective W

/-- Every absolutely continuous vertex reweighting preserves all imposed
tests, with no feasibility assumption at omitted orders. -/
theorem feasible_changeMeasure [SigmaFinite μ] [SigmaFinite ν]
    (W : Model Ω μ) (hν : ν ≪ μ) {r : ℕ} (hW : Feasible r W) :
    Feasible r (W.changeMeasure hν) := by
  intro n hn hnr
  exact (DecoratedKernel.pi_absolutelyContinuous hν n).ae_le (hW n hn hnr)

/-- Turning any subset of sampled colors into absent pairs preserves a
valid clique test. A deleted pair makes the presence product zero. -/
theorem violation_map_deletion {n : ℕ} (f : CappedColor → CappedColor)
    (hf : ∀ c, f c = CappedColor.absent ∨ f c = c)
    (c : CliquePair n → CappedColor) (hc : violation c = 0) :
    violation (fun e => f (c e)) = 0 := by
  classical
  by_cases h : ∃ e, f (c e) = CappedColor.absent
  · obtain ⟨e, he⟩ := h
    have hprod : (∏ i, CappedColor.adjacency (f (c i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (by rw [he]; rfl)
    simp only [violation, hprod, mul_zero]
  · have heq : ∀ e, f (c e) = c e := by
      intro e
      exact (hf (c e)).resolve_left (fun he => h ⟨e, he⟩)
    simpa only [heq] using hc

/-- A measurable color-deletion map gives an actual feasible decorated
kernel, sampled independently at each pair. -/
theorem feasible_map_deletion (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (f : CappedColor → CappedColor) (hf : Measurable f)
    (hdelete : ∀ c, f c = CappedColor.absent ∨ f c = c) :
    Feasible r (W.map f hf) := by
  intro n hn hnr
  filter_upwards [hW n hn hnr] with x hx
  unfold cliqueLaw
  rw [DecoratedKernel.sampleLaw_map]
  have hm : Measurable (fun c : CliquePair n → CappedColor => fun e => f (c e)) :=
    measurable_pi_iff.mpr (fun e => hf.comp (measurable_pi_apply e))
  apply (ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (continuous_violation n).measurable measurable_const)).2
  exact hx.mono (fun c hc => violation_map_deletion f hdelete c hc)

open scoped Classical in
/-- Delete precisely the outcomes in a specified measurable color set. -/
def deleteColors (W : Model Ω μ) (s : Set CappedColor) (hs : MeasurableSet s) : Model Ω μ :=
  W.map (s.piecewise (fun _ => CappedColor.absent) id)
    (measurable_const.piecewise hs measurable_id)

theorem feasible_deleteColors (W : Model Ω μ) {r : ℕ} (hW : Feasible r W)
    (s : Set CappedColor) (hs : MeasurableSet s) : Feasible r (deleteColors W s hs) := by
  classical
  apply feasible_map_deletion W hW
  intro c
  by_cases hc : c ∈ s
  · exact Or.inl (Set.piecewise_eq_of_mem s _ _ hc)
  · exact Or.inr (Set.piecewise_eq_of_notMem s _ _ hc)

end CappedModel

end Erdos1017
