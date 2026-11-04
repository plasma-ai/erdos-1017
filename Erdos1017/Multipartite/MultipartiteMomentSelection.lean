module

public import Erdos1017.Multipartite.MultipartiteProfileValues

/-!
# Maximizing on a fixed moment fiber

The fiber of fixed total secondary mass and fixed atomic square moment is
compact in the sorted profile space, so the limiting finite-head value attains
its maximum on each nonempty fiber, and a maximizer with greatest dust can be
selected.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

/-- Fixed total secondary mass and fixed atomic square moment. -/
def momentFiber (L T Q : ℝ) : Set Profile :=
  space L ∩ {x | x.1 = T ∧ (∑' i, (x.2 i) ^ 2) = Q}

/-- Both moments are continuous on the sorted compact profile space. -/
theorem momentFiber_isCompact (L T Q : ℝ) : IsCompact (momentFiber L T Q) := by
  have hmoment : ContinuousOn (fun x : Profile => (x.1, ∑' i, (x.2 i) ^ 2)) (space L) :=
    continuous_fst.continuousOn.prodMk (squareMoment_continuousOn L)
  have hclosed := hmoment.preimage_isClosed_of_isClosed
    (space_isCompact L).isClosed (isClosed_singleton (x := (T, Q)))
  apply (space_isCompact L).of_isClosed_subset
  · simpa only [momentFiber, Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using hclosed
  · exact Set.inter_subset_left

/-- The limiting finite-head value attains its maximum on each nonempty
moment fiber. This does not yet identify that value with a countable physical infimum. -/
theorem exists_moment_maximum (L T Q : ℝ) (hne : (momentFiber L T Q).Nonempty) :
    ∃ x ∈ momentFiber L T Q, ∀ y ∈ momentFiber L T Q, limitValue y ≤ limitValue x := by
  exact (momentFiber_isCompact L T Q).exists_isMaxOn hne
    ((limitValue_continuousOn L).mono Set.inter_subset_left)

/-- Within a fixed moment fiber, select a value maximizer with greatest dust.
All compactness hypotheses are proved for the actual value-maximizing set. -/
theorem exists_greatest_dust_moment_maximum (L T Q : ℝ)
    (hne : (momentFiber L T Q).Nonempty) :
    ∃ x ∈ momentFiber L T Q,
      (∀ y ∈ momentFiber L T Q, limitValue y ≤ limitValue x) ∧
      ∀ y ∈ momentFiber L T Q, limitValue y = limitValue x → dust y ≤ dust x := by
  obtain ⟨z, hz, hmax⟩ := exists_moment_maximum L T Q hne
  let K := momentFiber L T Q ∩ {x | limitValue x = limitValue z}
  have hK : IsCompact K := by
    apply (momentFiber_isCompact L T Q).of_isClosed_subset
    · have hc : ContinuousOn limitValue (momentFiber L T Q) :=
        (limitValue_continuousOn L).mono Set.inter_subset_left
      exact hc.preimage_isClosed_of_isClosed (momentFiber_isCompact L T Q).isClosed
        (isClosed_singleton (x := limitValue z))
    · exact Set.inter_subset_left
  have hsub : K ⊆ space L := fun _ hx => hx.1.1
  obtain ⟨x, hx, hdust⟩ := exists_greatest_dust hK ⟨z, hz, rfl⟩ hsub
  refine ⟨x, hx.1, ?_, ?_⟩
  · intro y hy
    rw [hx.2]
    exact hmax y hy
  · intro y hy heq
    exact hdust y ⟨hy, heq.trans hx.2⟩

end Erdos1017.MultipartiteProfiles
