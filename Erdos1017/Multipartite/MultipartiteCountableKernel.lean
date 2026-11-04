module

public import Erdos1017.Multipartite.MultipartitePhysicalUpper

/-!
# The countable homogeneous dual kernel

`kernel` retains the negative dust diagonal and is preserved by prefix
embedding, with a uniform pointwise bound from the coefficient box; every clique
satisfies the countable dual test pointwise, and the physical kernel is
measurable and integrable for every finite demand measure.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteCountableMeasure

open MeasureTheory
open scoped BigOperators

local instance : MeasurableSpace Label := ⊤

/-- The countable homogeneous dual kernel retains the negative dust diagonal. -/
def kernel (D : MultipartiteCountableDual.Coefficients) : Label → Label → ℝ
  | .inl none, .inl none => 0
  | .inl none, .inl (some j) => MultipartiteCountableDual.head D j
  | .inl (some i), .inl none => MultipartiteCountableDual.head D i
  | .inl (some i), .inl (some j) => -(if i < j then MultipartiteCountableDual.pair D i j
      else if j < i then MultipartiteCountableDual.pair D j i else 0)
  | .inl none, .inr _ => MultipartiteCountableDual.linear D
  | .inr _, .inl none => MultipartiteCountableDual.linear D
  | .inl (some i), .inr _ => -MultipartiteCountableDual.incident D i
  | .inr _, .inl (some i) => -MultipartiteCountableDual.incident D i
  | .inr _, .inr _ => -MultipartiteCountableDual.penalty D

/-- Prefix embedding preserves the actual dual kernel, including dust pairs. -/
theorem kernel_embed (D : MultipartiteCountableDual.Coefficients) (n : ℕ)
    (a b : DustCommonRealization.Label n) :
    kernel D (embedLabel n a) (embedLabel n b) =
      DustCommonRealization.kernel (MultipartiteCountableDual.restrict n D) a b := by
  rcases a with a | a <;> rcases b with b | b
  · cases a <;> cases b <;> rfl
  · cases a <;> rfl
  · cases b <;> rfl
  · rfl

/-- The bounded coefficient box gives a uniform pointwise kernel bound. -/
theorem norm_kernel_le_one {D : MultipartiteCountableDual.Coefficients}
    (hD : D ∈ MultipartiteCountableDual.feasible) (a b : Label) : ‖kernel D a b‖ ≤ 1 := by
  have hc (c : MultipartiteCountableDual.Coordinate) : ‖D c‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hD.1.1 c)]
    exact hD.1.2 c
  rcases a with a | a <;> rcases b with b | b
  · cases a <;> cases b
    · simp [kernel]
    · exact hc _
    · exact hc _
    · simp only [kernel, norm_neg]
      split_ifs <;> first | exact hc _ | norm_num
  · cases a
    · exact hc _
    · simpa only [kernel, norm_neg, MultipartiteCountableDual.incident] using
        hc (.inr (.inr (.inl _)))
  · cases b
    · exact hc _
    · simpa only [kernel, norm_neg, MultipartiteCountableDual.incident] using
        hc (.inr (.inr (.inl _)))
  · simpa only [kernel, norm_neg, MultipartiteCountableDual.penalty] using
      hc (.inr (.inr (.inr true)))

/-- Every finite family of countable labels belongs to one finite prefix. -/
theorem exists_prefix_labels {k : ℕ} (v : Fin k → Label) :
    ∃ (n : ℕ) (w : Fin k → DustCommonRealization.Label n), ∀ i, embedLabel n (w i) = v i := by
  classical
  let rank : Label → ℕ
    | .inl (some i) => i + 1
    | _ => 0
  let n := Finset.univ.sup (fun i => rank (v i))
  have hbound (i : Fin k) : rank (v i) ≤ n :=
    Finset.le_sup (f := fun i => rank (v i)) (Finset.mem_univ i)
  have hex (i : Fin k) : ∃ a : DustCommonRealization.Label n, embedLabel n a = v i := by
    have hi := hbound i
    cases hvi : v i with
    | inl a =>
      cases a with
      | none => exact ⟨.inl none, rfl⟩
      | some j =>
        rw [hvi] at hi
        exact ⟨.inl (some ⟨j, by change j + 1 ≤ n at hi; omega⟩), rfl⟩
    | inr u => exact ⟨.inr u, rfl⟩
  choose w hw using hex
  exact ⟨n, w, hw⟩

/-- Every genuine clique satisfies the countable dual test. This is pointwise,
so no independent-sampling assumption is imposed on physical laws. -/
theorem physical_clique_test {Ω : Type*} {k : ℕ}
    {D : MultipartiteCountableDual.Coefficients} (hD : D ∈ MultipartiteCountableDual.feasible)
    (v : Fin k → Label × Ω)
    (hv : ∀ i j, i ≠ j → PhysicalCellLift.Adj ({.inr ()} : Finset Label) (v i) (v j)) :
    PhysicalPrimal.charge (fun z => kernel D z.1.1 z.2.1) v ≤ 1 := by
  obtain ⟨n, w, hw⟩ := exists_prefix_labels (fun i => (v i).1)
  have hi (a : Option (Fin n)) (i j : Fin k) (hia : w i = .inl a)
      (hja : w j = .inl a) : i = j := by
    by_contra hij
    have h := (hv i j hij).2
    rw [← hw i, ← hw j, hia, hja] at h
    simp [embedLabel] at h
  have hc := DustCommonRealization.kernel_charge_le_one
    (MultipartiteCountableDual.restrict n D)
    (MultipartiteCountableDual.restrict_mem_feasible hD n) w hi
  convert hc using 1
  unfold PhysicalPrimal.charge
  congr 1
  apply Finset.sum_congr rfl
  intro ij _
  dsimp only
  rw [← hw ij.val.1, ← hw ij.val.2, kernel_embed]

variable {Ω : Type*} [MeasurableSpace Ω]

def physicalKernel (D : MultipartiteCountableDual.Coefficients)
    (z : (Label × Ω) × (Label × Ω)) : ℝ := kernel D z.1.1 z.2.1

theorem physicalKernel_measurable (D : MultipartiteCountableDual.Coefficients) :
    Measurable (physicalKernel (Ω := Ω) D) :=
  (measurable_of_countable (fun z : Label × Label => kernel D z.1 z.2)).comp
    (measurable_fst.fst.prodMk measurable_snd.fst)

/-- The homogeneous kernel is integrable for every finite demand measure. -/
theorem physicalKernel_integrable {D : MultipartiteCountableDual.Coefficients}
    (hD : D ∈ MultipartiteCountableDual.feasible)
    (ρ : Measure ((Label × Ω) × (Label × Ω))) [IsFiniteMeasure ρ] :
    Integrable (physicalKernel D) ρ := by
  apply (integrable_const (1 : ℝ)).mono' (physicalKernel_measurable D).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => norm_kernel_le_one hD z.1.1 z.2.1)

end Erdos1017.MultipartiteCountableMeasure
