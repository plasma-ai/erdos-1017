module

public import Erdos1017.Multipartite.Dust.CountableDustRowSurgery
public import Erdos1017.Multipartite.MultipartiteGamma
public import Erdos1017.Multipartite.MultipartiteDustCellVariation

/-!
# Incidence and penalty floors for dust

The positive-dust row surgery gives both incidence floors in anchor-normalized
units for the selected dual's own multiplier, and the dust-cell surgery supplies
the internal-dust floor without a unit-box competitor assumption.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

/-- The actual positive-dust row surgery gives both source incidence floors
in anchor-normalized units, for the selected dual's own multiplier. -/
theorem incident_floor_of_head_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    anchorRow x.2 (MultipartiteProfiles.dust x) D - ℓ ≤ incident D i * (1 - x.2 i) ∧
      anchorRow x.2 (MultipartiteProfiles.dust x) D - ℓ ≤ incident D i := by
  have hfloor := incident_floor_at_optimum hx.1 hD hopt i hi
  rw [dust_row_of_head_multiplier hε hx hmax hxvalue hD hopt ℓ hrows i hi hs] at hfloor
  refine ⟨hfloor, hfloor.trans ?_⟩
  have hci : 0 ≤ incident D i := hD.1.1 _
  nlinarith [mul_nonneg hci hi.le]

/-- The actual dust-cell surgery supplies the source internal-dust floor
for the selected multiplier, without a unit-box competitor assumption. -/
theorem penalty_floor_of_head_multiplier {ε : ℝ} (hε : 0 < ε) {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε)
    (hmax : ∀ y ∈ MultipartiteProfiles.densityFiber (1 / Real.sqrt ε - 1) ε,
      MultipartiteProfiles.normalizedValue y ≤ MultipartiteProfiles.normalizedValue x)
    (hxvalue : ε < MultipartiteProfiles.normalizedValue x)
    {D : Coefficients} (hD : D ∈ feasible)
    (hopt : objective x.2 (MultipartiteProfiles.dust x) D = MultipartiteProfiles.limitValue x)
    (ℓ : ℝ) (hrows : ∀ k, 0 < x.2 k → headRow x.2 (MultipartiteProfiles.dust x) D k -
      anchorRow x.2 (MultipartiteProfiles.dust x) D = ℓ * (x.2 k - 1))
    (i : ℕ) (hi : 0 < x.2 i) (hs : 0 < MultipartiteProfiles.dust x) :
    anchorRow x.2 (MultipartiteProfiles.dust x) D - ℓ ≤ penalty D := by
  have h := dust_penalty_floor hε hx hmax hxvalue hD hopt i hi hs
  rwa [dust_row_of_head_multiplier hε hx hmax hxvalue hD hopt ℓ hrows i hi hs] at h

end Erdos1017.MultipartiteCountableDual
