module

public import Erdos1017.Multipartite.MultipartiteCountableMeasure
public import Erdos1017.Multipartite.Dust.DustPhysicalValue

/-!
# Embedding finite realizations in the carrier

`embedLabel` and `embedVertex` embed every finite-head realization injectively
in the same countable physical carrier; the graph relation is unchanged, and the
pushed-forward finite vertex measure and graph demand are exactly the dust
prefix.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableMeasure

open MeasureTheory
open scoped BigOperators

local instance : MeasurableSpace Label := ⊤
local instance (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤
local instance (n : ℕ) : MeasurableSpace (DustCommonRealization.Label n) := ⊤

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Embed every finite-head realization in the same countable physical carrier. -/
def embedLabel (n : ℕ) : DustCommonRealization.Label n → Label :=
  Sum.map (Option.map Fin.val) id

def embedVertex (n : ℕ) : DustCommonRealization.Label n × Ω → Label × Ω :=
  Prod.map (embedLabel n) id

theorem embedVertex_measurable (n : ℕ) : Measurable (embedVertex (Ω := Ω) n) :=
  (measurable_of_countable (embedLabel n)).prodMap measurable_id

theorem embedLabel_injective (n : ℕ) : Function.Injective (embedLabel n) :=
  Sum.map_injective.mpr ⟨Option.map_injective Fin.val_injective, Function.injective_id⟩

omit [MeasurableSpace Ω] in
theorem embedVertex_injective (n : ℕ) : Function.Injective (embedVertex (Ω := Ω) n) :=
  fun _ _ h => Prod.ext ((embedLabel_injective n) (congrArg Prod.fst h))
    (by simpa only [embedVertex, Prod.map_snd, id_eq] using congrArg Prod.snd h)

omit [MeasurableSpace Ω] in
/-- The graph relation is the same before and after prefix embedding. -/
theorem embedVertex_adj (n : ℕ) (x y : DustCommonRealization.Label n × Ω) :
    PhysicalCellLift.Adj ({.inr ()} : Finset Label) (embedVertex n x) (embedVertex n y) ↔
      PhysicalCellLift.Adj ({.inr ()} : Finset (DustCommonRealization.Label n)) x y := by
  simp only [PhysicalCellLift.Adj, ne_eq, (embedVertex_injective n).eq_iff,
    Finset.mem_singleton]
  have hlabel : (embedVertex n x).1 = (embedVertex n y).1 ↔ x.1 = y.1 :=
    (embedLabel_injective n).eq_iff
  have hdust : (embedVertex n x).1 = .inr () ↔ x.1 = .inr () := by
    rcases x with ⟨i, z⟩
    rcases i with i | u <;> simp [embedVertex, embedLabel]
  rw [hlabel, hdust]

/-- The pushed-forward finite vertex measure is exactly the genuine-dust prefix. -/
theorem map_finite_vertexMeasure (ν : Measure Ω) (p : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    (PhysicalCellLift.vertexMeasure (fun _ : DustCommonRealization.Label n => ν)
      (DustCommonRealization.masses (fun i : Fin n => p i.val) s)).map (embedVertex n) =
      prefixMeasure ν p s n := by
  unfold PhysicalCellLift.vertexMeasure
  rw [Measure.map_sum (embedVertex_measurable n).aemeasurable]
  have hterm (i : DustCommonRealization.Label n) :
      (ENNReal.ofReal (DustCommonRealization.masses (fun i : Fin n => p i.val) s i) •
        ν.map (fun x => (i, x))).map (embedVertex n) =
      ENNReal.ofReal (DustCommonRealization.masses (fun i : Fin n => p i.val) s i) •
        component ν (embedLabel n i) := by
    have hm : Measurable (fun x : Ω => (i, x)) := measurable_const.prodMk measurable_id
    rw [Measure.map_smul _ (embedVertex_measurable n).aemeasurable,
      Measure.map_map (embedVertex_measurable n) hm]
    rfl
  simp_rw [hterm]
  rw [Measure.sum_fintype]
  simp only [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_unique,
    DustCommonRealization.masses, Multipartite.anchorMasses, Sum.elim_inl, Sum.elim_inr,
    embedLabel, Sum.map_inl, Sum.map_inr, Option.map_none, Option.map_some,
    Option.elim', ENNReal.ofReal_one, one_smul, id_eq]
  unfold prefixMeasure headMeasure
  rw [← Fin.sum_univ_eq_sum_range]
  ac_rfl

theorem finite_vertexMeasure_finite (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    IsFiniteMeasure (PhysicalCellLift.vertexMeasure
      (fun _ : DustCommonRealization.Label n => ν)
      (DustCommonRealization.masses (fun i : Fin n => p i.val) s)) := by
  have hmap (i : DustCommonRealization.Label n) :
      IsFiniteMeasure (ν.map (fun x => (i, x))) := Measure.isFiniteMeasure_map _ _
  have hterm (i : DustCommonRealization.Label n) :
      IsFiniteMeasure (ENNReal.ofReal
        (DustCommonRealization.masses (fun i : Fin n => p i.val) s i) •
          ν.map (fun x => (i, x))) := Measure.smul_finite _ ENNReal.ofReal_ne_top
  unfold PhysicalCellLift.vertexMeasure
  rw [Measure.sum_fintype]
  infer_instance

/-- The embedded finite graph demand is the actual restricted product of the
countable carrier's prefix vertex measure. -/
theorem map_finite_graphDemand [MeasurableEq Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (p : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    (PhysicalPrimal.graphDemand
      (PhysicalCellLift.vertexMeasure (fun _ : DustCommonRealization.Label n => ν)
        (DustCommonRealization.masses (fun i : Fin n => p i.val) s))
      (PhysicalCellLift.edgeSet ({.inr ()} : Finset (DustCommonRealization.Label n)))).map
        (Prod.map (embedVertex n) (embedVertex n)) =
      PhysicalPrimal.graphDemand (prefixMeasure ν p s n)
        (PhysicalCellLift.edgeSet ({.inr ()} : Finset Label)) := by
  have := finite_vertexMeasure_finite ν p s n
  have hpre : Prod.map (embedVertex (Ω := Ω) n) (embedVertex n) ⁻¹'
      PhysicalCellLift.edgeSet ({.inr ()} : Finset Label) =
      PhysicalCellLift.edgeSet ({.inr ()} : Finset (DustCommonRealization.Label n)) := by
    ext z
    exact embedVertex_adj n z.1 z.2
  rw [PhysicalPrimal.graphDemand, PhysicalPrimal.graphDemand, ← map_finite_vertexMeasure ν p s n,
    Measure.map_prod_map _ _ (embedVertex_measurable n) (embedVertex_measurable n),
    Measure.restrict_map ((embedVertex_measurable n).prodMap (embedVertex_measurable n))
      (PhysicalCellLift.edgeSet_measurable _), hpre]

end Erdos1017.MultipartiteCountableMeasure
