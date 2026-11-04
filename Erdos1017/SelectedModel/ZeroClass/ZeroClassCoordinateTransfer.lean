module

public import Erdos1017.SelectedModel.ZeroClass.ZeroClassCliqueOrders
public import Erdos1017.SelectedModel.ZeroClass.ZeroClassPatternSupport

/-!
# Clique presence through membership patterns

Conditional independence of sampled pair colors turns the restricted
clique-presence integral into a product of adjacency moments, and splitting
internal and external coordinates of one membership pattern (`patternSet`)
preserves the restricted product law and identifies the internal integral with
the restricted clique presence.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos1017.CappedModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Conditional independence of actual sampled pair colors turns the raw
restricted clique-presence integral into a product of adjacency moments. -/
theorem restrictedCliquePresence_eq_integral_prod_moment (W : Model Ω μ)
    (s : Set Ω) (j : ℕ) :
    restrictedCliquePresence W s j =
      ∫ x : Fin j → Ω,
        ∏ e : CliquePair j,
          W.moment CappedColor.adjacency (x e.val.1, x e.val.2)
        ∂Measure.pi (fun _ : Fin j => μ.restrict s) := by
  unfold restrictedCliquePresence
  rw [Measure.restrict_pi_pi]
  apply integral_congr_ae
  filter_upwards with x
  change (∫ c, ∏ e : CliquePair j, CappedColor.adjacency (c e)
    ∂Measure.pi (fun e : CliquePair j => W.kernel (x e.val.1, x e.val.2))) = _
  rw [integral_fintype_prod_eq_prod]
  rfl

private theorem pi_fintype_independent {ι : Type*} {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (ρ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (ρ i)] (F₁ F₂ : Fintype ι) :
    @Measure.pi ι α F₁ (fun _ => inferInstance) ρ =
      @Measure.pi ι α F₂ (fun _ => inferInstance) ρ := by
  apply @Measure.pi_eq ι α F₁ (fun _ => inferInstance) ρ _ _
  intro s hs
  rw [@Measure.pi_pi ι α F₂ (fun _ => inferInstance) ρ _ s]
  have huniv : (@Finset.univ ι F₁) = (@Finset.univ ι F₂) := by
    ext i
    simp
  exact congrArg (fun t : Finset ι => t.prod (fun i => ρ i (s i))) huniv.symm

/-- The exact membership pattern for the internal vertices of a tuple. -/
def patternSet {n : ℕ} (s : Set Ω) (S : Finset (Fin n)) : Set (Fin n → Ω) :=
  Set.univ.pi (fun i : Fin n => if i ∈ S then s else sᶜ)

/-- Splitting internal and external coordinates preserves the actual
restricted product law of one fixed membership pattern. -/
theorem measurePreserving_patternSplit {n : ℕ} (s : Set Ω) (S : Finset (Fin n)) :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S))
      ((Measure.pi (fun _ : Fin n => μ)).restrict (patternSet s S))
      ((Measure.pi (fun _ : {i : Fin n // i ∈ S} => μ.restrict s)).prod
        (Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict sᶜ))) := by
  rw [patternSet, Measure.restrict_pi_pi]
  have h := measurePreserving_piEquivPiSubtypeProd
    (fun i : Fin n => μ.restrict (if i ∈ S then s else sᶜ)) (fun i => i ∈ S)
  have hint : (fun i : {i : Fin n // i ∈ S} =>
      μ.restrict (if (i : Fin n) ∈ S then s else sᶜ)) =
      (fun _ : {i : Fin n // i ∈ S} => μ.restrict s) := by
    funext i
    simp [i.property]
  have hext : (fun i : {i : Fin n // i ∉ S} =>
      μ.restrict (if (i : Fin n) ∈ S then s else sᶜ)) =
      (fun _ : {i : Fin n // i ∉ S} => μ.restrict sᶜ) := by
    funext i
    simp [i.property]
  rw [hint, hext] at h
  have hpi := pi_fintype_independent
    (fun _ : {i : Fin n // i ∈ S} => μ.restrict s)
    (Subtype.fintype (fun i : Fin n => i ∈ S)) (Finset.Subtype.fintype S)
  rw [hpi] at h
  simpa using h

/-- Canonical ordered reindexing identifies the internal coordinates of
one membership pattern with the raw restricted clique-presence integral. -/
theorem integral_internal_product_eq_restrictedCliquePresence {n : ℕ}
    (W : Model Ω μ) (s : Set Ω) (S : Finset (Fin n)) :
    let e : Fin S.card ≃ {i : Fin n // i ∈ S} := (S.orderIsoOfFin rfl).toEquiv
    (∫ z : ({i : Fin n // i ∈ S} → Ω),
      ∏ p : CliquePair S.card,
        W.moment CappedColor.adjacency (z (e p.val.1), z (e p.val.2))
      ∂Measure.pi (fun _ : {i : Fin n // i ∈ S} => μ.restrict s)) =
      restrictedCliquePresence W s S.card := by
  classical
  let e : Fin S.card ≃ {i : Fin n // i ∈ S} := (S.orderIsoOfFin rfl).toEquiv
  rw [restrictedCliquePresence_eq_integral_prod_moment]
  dsimp only
  rw [← (measurePreserving_piCongrLeft
    (fun _ : {i : Fin n // i ∈ S} => μ.restrict s) e).integral_comp']
  change (∫ x : Fin S.card → Ω,
    ∏ p : CliquePair S.card,
      W.moment CappedColor.adjacency
        ((MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i ∈ S} => Ω) e) x (e p.val.1),
          (MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i ∈ S} => Ω) e) x (e p.val.2))
      ∂Measure.pi (fun _ : Fin S.card => μ.restrict s)) = _
  simp only [MeasurableEquiv.piCongrLeft_apply_apply]

end Erdos1017.CappedModel
