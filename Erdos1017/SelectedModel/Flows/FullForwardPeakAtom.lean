module

public import Erdos1017.SelectedModel.Flows.FullForwardPeak
public import Erdos1017.SelectedModel.Flows.SelectedAtomRedirection
public import Erdos1017.SelectedModel.SelectedAtomAvoidance

/-!
# Whole atoms under full forward flows

Low whole atoms are removed and neutral ones keep their mass at every full
forward endpoint, every original atom can be avoided by some full forward flow,
and the common forward peak is a high or neutral atom dominating every other
high closed missing mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Classical

namespace Erdos1017.CappedModel.SelectedHighLowStructure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : Model Ω μ} {m : ℝ}

/-- Every tracked atomic label is literally its original whole-row fiber. -/
theorem collapsedPartLabel_fiber (S : SelectedHighLowStructure W m) (i : S.I) :
    S.collapsedPartLabel ⁻¹' {some i} = {x | S.ρ x = i} := by
  ext x
  change (if h : S.ρ x ∈ S.I then some ⟨S.ρ x, h⟩ else none) = some i ↔ S.ρ x = i
  by_cases hx : S.ρ x ∈ S.I
  · simp only [hx, ↓reduceDIte, Option.some.injEq, Subtype.ext_iff]
  · simp only [hx, ↓reduceDIte, reduceCtorEq, false_iff]
    exact fun he => hx (he ▸ i.property)

/-- Endpoint class mass uses the unchanged original whole-row cell. -/
theorem forwardClassMass_eq_fiber (S : SelectedHighLowStructure W m)
    (q : Ω × Ω → ℝ) (i : S.I) :
    S.forwardClassMass q i = (missingFlowEndpointLaw μ q).real {x | S.ρ x = i} := by
  rw [forwardClassMass, S.collapsedPartLabel_fiber]

namespace IsFullForwardFlow

variable {S : SelectedHighLowStructure W m} {q : Ω × Ω → ℝ}

/-- Avoidance of an original atom forces its actual receipt to vanish. -/
theorem receipt_zero_of_avoids_atom (_hq : S.IsFullForwardFlow q) (i : S.I)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    ∀ᵐ x ∂μ, S.ρ x = i → MissingFlow.receipt μ q x = 0 := by
  filter_upwards [Measure.ae_ae_of_ae_prod havoid] with x hx hxi
  apply integral_eq_zero_of_ae
  filter_upwards [hx] with y hy
  by_contra hne
  exact hy hne hxi

/-- An avoided non-LOW whole atom retains its original mass. Both actual
marginals vanish there; no endpoint mass-retention premise is supplied. -/
theorem classMass_eq_original_of_avoids_nonlow (hq : S.IsFullForwardFlow q) (i : S.I)
    (hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L)
    (havoid : ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) :
    S.forwardClassMass q i = μ.real {x | S.ρ x = i} := by
  rw [S.forwardClassMass_eq_fiber]
  apply MissingFlow.endpoint_real_set_eq_original q hq.integrable hq.nonnegative
    hq.supply_le_one _ (S.hfibers i i.property).1 (hq.receipt_zero_of_avoids_atom i havoid)
  filter_upwards [hq.supply, (ae_restrict_iff' (S.hfibers i i.property).1).mp hnonlow]
    with x hs hn hxi
  rw [hs, indicator_of_notMem (hn hxi)]

/-- Any original whole atom outside HIGH is avoided by every full forward
flow, as a consequence of its actual recipient support. -/
theorem avoids_atom_of_nonhigh (hq : S.IsFullForwardFlow q) (i : S.I)
    (hnonhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.H) :
    ∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i := by
  have hh := (ae_restrict_iff' (S.hfibers i i.property).1).mp hnonhigh
  filter_upwards [hq.support, Measure.quasiMeasurePreserving_fst.ae hh] with p hp hh hqz hxi
  exact hh hxi (hp hqz).2.1

/-- Every neutral whole atom retains its original mass under every actual
full forward flow. Neutrality excludes both HIGH receipt and LOW supply. -/
theorem classMass_eq_original_of_neutral (hq : S.IsFullForwardFlow q) (i : S.I)
    (hneutral : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N) :
    S.forwardClassMass q i = μ.real {x | S.ρ x = i} := by
  have hnL : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L :=
    hneutral.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  have hnH : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.H :=
    hneutral.mono (fun _ hx hH => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hH hx)
  exact hq.classMass_eq_original_of_avoids_nonlow i hnL (hq.avoids_atom_of_nonhigh i hnH)

/-- Every LOW whole atom is removed at every actual full forward endpoint. -/
theorem classMass_eq_zero_of_low (hq : S.IsFullForwardFlow q) (i : S.I)
    (hlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.L) :
    S.forwardClassMass q i = 0 := by
  rw [S.forwardClassMass_eq_fiber]
  have hdirection : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, MissingFlow.direction μ q x = -1 := by
    filter_upwards [hlow, ae_restrict_of_ae hq.endpoint_removes_low] with x hx he
    linarith [he hx]
  have he := integrableTilt_real_set (MissingFlow.direction μ q)
    (MissingFlow.integrable_direction hq.integrable)
    (MissingFlow.direction_ge_neg_one hq.nonnegative hq.supply_le_one)
    1 ⟨by norm_num, le_rfl⟩ {x | S.ρ x = i} (S.hfibers i i.property).1
  change (missingFlowEndpointLaw μ q).real {x | S.ρ x = i} = _ at he
  rw [he, integral_congr_ae hdirection, setIntegral_const, smul_eq_mul]
  ring

end IsFullForwardFlow

variable [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [StandardBorelSpace Ω] [MeasurableEq Ω] [NullSingletonClass μ]

/-- Normalize the actual reduced zero relation on precisely the original
LOW sources. The removed recipient is an original whole-row atom. -/
def highAtomAvoidingFlow (S : SelectedHighLowStructure W m) (i : S.I) : Ω × Ω → ℝ :=
  MissingFlow.normalizedDensity μ {p | p ∈ S.reducedZeroRelation i ∧ p.2 ∈ S.L}

/-- Positive reduced columns construct an actual full forward flow avoiding
any HIGH atom. No avoidance or full-flow existence premise is supplied. -/
theorem highAtomAvoidingFlow_properties (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (i : S.I)
    (hhigh : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) :
    S.IsFullForwardFlow (S.highAtomAvoidingFlow i) ∧
      (∀ᵐ p ∂μ.prod μ, S.highAtomAvoidingFlow i p ≠ 0 → S.ρ p.1 ≠ i) := by
  let Z : Set (Ω × Ω) := {p | p ∈ S.reducedZeroRelation i ∧ p.2 ∈ S.L}
  have hZ : MeasurableSet Z := (S.measurableSet_reducedZeroRelation i).inter
    (S.hpartition.2.1.preimage measurable_snd)
  have hmem (p : Ω × Ω) (hp : S.highAtomAvoidingFlow i p ≠ 0) : p ∈ Z := by
    by_contra hn
    exact hp (MissingFlow.normalizedDensity_eq_zero_of_notMem Z p hn)
  have hsource : ∀ᵐ y ∂μ, y ∈ MissingFlow.positiveSources μ Z ↔ y ∈ S.L := by
    filter_upwards [S.ae_reducedZeroRelation_columnMass_pos_of_low hW hd hgap i i.property hhigh]
      with y hy
    by_cases hL : y ∈ S.L
    · have heq : MissingFlow.columnMass μ Z y =
          MissingFlow.columnMass μ (S.reducedZeroRelation i) y := by
        unfold MissingFlow.columnMass
        congr 1
        ext x
        simp only [Z, mem_ofPred_eq, hL, and_true]
      change (0 < MissingFlow.columnMass μ Z y) ↔ _
      rw [heq]
      exact iff_of_true (hy hL) hL
    · have hz : MissingFlow.columnMass μ Z y = 0 := by
        simp [MissingFlow.columnMass, Z, hL]
      change (0 < MissingFlow.columnMass μ Z y) ↔ _
      rw [hz]
      exact iff_of_false (lt_irrefl _) hL
  refine ⟨⟨MissingFlow.integrable_normalizedDensity Z hZ,
    Eventually.of_forall (MissingFlow.normalizedDensity_nonneg Z), ?_, ?_⟩, ?_⟩
  · change MissingFlow.supply μ (MissingFlow.normalizedDensity μ Z) =ᵐ[μ] _
    rw [MissingFlow.supply_normalizedDensity Z hZ]
    filter_upwards [hsource] with y hy
    change (if y ∈ MissingFlow.positiveSources μ Z then (1 : ℝ) else 0) =
      (if y ∈ S.L then 1 else 0)
    rw [hy]
  · filter_upwards [S.hrelation] with p hp hq
    have hm := hmem p hq
    refine ⟨hm.1.1, ?_, hm.2⟩
    rcases hp hm.1.1 with h | h
    · exact h.1
    · exact False.elim (Set.disjoint_left.mp S.hpartition.2.2.2.2.1 h.1 hm.2)
  · exact Eventually.of_forall (fun p hp => (hmem p hp).1.2)

/-- Every original atom can be avoided by a genuine full forward flow.
LOW and neutral atoms are already avoided by the original normalized flow. -/
theorem exists_fullForwardFlow_avoiding_atom (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) (i : S.I) :
    ∃ q, S.IsFullForwardFlow q ∧
      (∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) := by
  rcases S.hfiberClass i i.property with hH | hL | hN
  · exact ⟨S.highAtomAvoidingFlow i, S.highAtomAvoidingFlow_properties hW hd hgap i hH⟩
  · refine ⟨S.forwardFlow, S.forwardFlow_isFullForwardFlow,
      S.forwardFlow_isFullForwardFlow.avoids_atom_of_nonhigh i ?_⟩
    exact hL.mono (fun _ hx hH => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hH hx)
  · refine ⟨S.forwardFlow, S.forwardFlow_isFullForwardFlow,
      S.forwardFlow_isFullForwardFlow.avoids_atom_of_nonhigh i ?_⟩
    exact hN.mono (fun _ hx hH => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.1 hH hx)

/-- The fixed original peak is HIGH or neutral. It admits an actual
avoiding witness with its original mass, and dominates every other HIGH
closed missing mass and every other neutral atomic mass by the same gap.
No comparison with other LOW atoms is claimed here. -/
theorem exists_common_forward_peak_atom (S : SelectedHighLowStructure W m)
    {d c : ℝ} (hW : FullStationaryClass d c W m)
    (hd : d ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (hgap : benchmark d < c) :
    0 < forwardPeakGap d c m ∧ ∃ (i : S.I) (q : Ω × Ω → ℝ),
      S.IsFullForwardFlow q ∧
      (∀ᵐ p ∂μ.prod μ, q p ≠ 0 → S.ρ p.1 ≠ i) ∧
      ((∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
        (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N)) ∧
      S.forwardClassMass q i = μ.real {x | S.ρ x = i} ∧
      (∀ (u : Ω × Ω → ℝ), S.IsFullForwardFlow u →
        0 < S.forwardClassMass u i ∧
        ForwardPeak.massPeak (S.forwardClassMass u) = S.forwardClassMass u i ∧
        ForwardPeak.IsSeparatedPeak (S.forwardClassMass u) (forwardPeakGap d c m) i) ∧
      (∀ (u : Ω × Ω → ℝ) (hu : S.IsFullForwardFlow u),
        (∀ᵐ p ∂μ.prod μ, u p ≠ 0 → S.ρ p.1 ≠ i) →
          S.forwardClassMass u i = μ.real {x | S.ρ x = i} ∧
          objective hu.endpoint ≤ (μ.real {x | S.ρ x = i}) ^ 2 ∧
          (2 * (c - m * d) + m) + KernelOperator.kernelEnergy (μ := μ)
            (shiftedKernel W m) (MissingFlow.direction μ u) ≤
              2 * (μ.real {x | S.ρ x = i}) ^ 2 + m * (1 - 2 * density hu.endpoint)) ∧
      (∀ k : S.I, k ≠ i → (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.H) →
        μ.real {x | S.ρ x = k} + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) ≤
          μ.real {x | S.ρ x = i} - forwardPeakGap d c m) ∧
      (∀ k : S.I, k ≠ i → (∀ᵐ x ∂μ.restrict {x | S.ρ x = k}, x ∈ S.N) →
        μ.real {x | S.ρ x = k} ≤ μ.real {x | S.ρ x = i} - forwardPeakGap d c m) := by
  obtain ⟨hΔ, i, hi, _⟩ := S.exists_unique_common_forward_peak hW hd hgap
  have hside : (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.H) ∨
      (∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∈ S.N) := by
    rcases S.hfiberClass i i.property with hH | hL | hN
    · exact Or.inl hH
    · have hp := (hi S.forwardFlow S.forwardFlow_isFullForwardFlow).1
      rw [S.forwardFlow_isFullForwardFlow.classMass_eq_zero_of_low i hL] at hp
      exact False.elim (lt_irrefl _ hp)
    · exact Or.inr hN
  have hnonlow : ∀ᵐ x ∂μ.restrict {x | S.ρ x = i}, x ∉ S.L := by
    rcases hside with hH | hN
    · exact hH.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.1 hx hL)
    · exact hN.mono (fun _ hx hL => Set.disjoint_left.mp S.hpartition.2.2.2.2.2.2 hL hx)
  obtain ⟨q, hq, havoid⟩ := S.exists_fullForwardFlow_avoiding_atom hW hd hgap i
  have hmass := hq.classMass_eq_original_of_avoids_nonlow i hnonlow havoid
  refine ⟨hΔ, i, q, hq, havoid, hside, hmass, hi, ?_, ?_, ?_⟩
  · intro u hu havoidU
    have hmassU := hu.classMass_eq_original_of_avoids_nonlow i hnonlow havoidU
    have hcost := hu.objective_le_peak_sq hW hd hgap
    rw [(hi u hu).2.1, hmassU] at hcost
    refine ⟨hmassU, hcost, ?_⟩
    rw [hu.endpoint_budget hW]
    linarith
  · intro k hki hhigh
    have hredirect := hq.atomRedirect_of_stationary hW k k.property hhigh
    have hne : (k : Lp ℝ 2 μ) ≠ i := fun he => hki (Subtype.ext he)
    have hstill := S.atomRedirect_avoids k i hne q havoid
    have hmassI := hredirect.classMass_eq_original_of_avoids_nonlow i hnonlow hstill
    have hmassK : S.forwardClassMass (S.atomRedirect k q) k =
        μ.real {x | S.ρ x = k} + μ.real (KernelOperator.wholeFiberMissingSet S.ρ k) := by
      rw [S.forwardClassMass_eq_fiber]
      exact hq.atomRedirect_endpoint_mass hW k k.property hhigh
    have hsep := (hi (S.atomRedirect k q) hredirect).2.2 k hki
    rw [hmassI, hmassK] at hsep
    linarith
  · intro k hki hneutral
    have hmassK := hq.classMass_eq_original_of_neutral k hneutral
    have hsep := (hi q hq).2.2 k hki
    rw [hmass, hmassK] at hsep
    linarith

end Erdos1017.CappedModel.SelectedHighLowStructure
