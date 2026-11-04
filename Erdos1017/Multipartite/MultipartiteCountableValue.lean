module

public import Erdos1017.Multipartite.MultipartiteCountableExtension
public import Erdos1017.Multipartite.MultipartiteMomentSelection

/-!
# Countable value equals the profile limit

The attained countable coefficient maximum is the continuous profile limit, so
the limiting profile value has a bounded countable homogeneous optimizer,
without any physical primal identification.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableDual

/-- The attained countable coefficient maximum is the continuous profile limit. -/
theorem value_eq_profile_limit {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) :
    value x.2 (MultipartiteProfiles.dust x) = MultipartiteProfiles.limitValue x := by
  obtain ⟨D, hD, hval⟩ := exists_value_eq x.2 (fun i => hx.1.1.2 i)
    (MultipartiteProfiles.atoms_summable hx) (MultipartiteProfiles.dust x)
  apply le_antisymm
  · rw [hval]
    exact objective_le_profile_limit hx hD
  · apply le_of_tendsto (MultipartiteProfiles.actualDustValue_tendsto hx)
    apply Filter.Eventually.of_forall
    intro n
    obtain ⟨E, hE, hEn⟩ := MultipartiteDust.exists_value_eq
      (fun i : Fin n => x.2 i.val) (MultipartiteProfiles.dust x)
    have hbound : objective x.2 (MultipartiteProfiles.dust x) (extendZero E) ≤
        value x.2 (MultipartiteProfiles.dust x) := by
      apply le_csSup
      · exact (feasible_isCompact.image_of_continuousOn
          ((objective_continuousOn x.2 (fun i => hx.1.1.2 i)
            (MultipartiteProfiles.atoms_summable hx) (MultipartiteProfiles.dust x)).mono
              Set.inter_subset_left)).bddAbove
      · exact ⟨extendZero E, extendZero_feasible hE, rfl⟩
    rw [objective_extendZero, ← hEn] at hbound
    exact hbound

/-- The limiting profile value has a bounded countable homogeneous optimizer.
No countable physical primal identification or attainment is inferred here. -/
theorem exists_profile_optimal {L : ℝ} {x : MultipartiteProfiles.Profile}
    (hx : x ∈ MultipartiteProfiles.space L) :
    ∃ D ∈ feasible,
      MultipartiteProfiles.limitValue x = objective x.2 (MultipartiteProfiles.dust x) D := by
  rw [← value_eq_profile_limit hx]
  exact exists_value_eq x.2 (fun i => hx.1.1.2 i)
    (MultipartiteProfiles.atoms_summable hx) (MultipartiteProfiles.dust x)

end Erdos1017.MultipartiteCountableDual
