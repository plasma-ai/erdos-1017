module

public import Erdos1017.Multipartite.MultipartiteProfileValues
public import Erdos1017.Multipartite.Dust.DustMassContinuity

/-!
# Finite-head values with the dust alone

The dust is nonnegative on the compact profile space and is the limit of the
residual dust of finite completions; keeping a finite head prefix with the dust
alone and omitting tail heads changes the value by a controlled amount and has
the same limiting coefficient value.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators
open Filter

/-- The actual dust is nonnegative on the compact profile space. -/
theorem dust_nonneg {L : ℝ} {x : Profile} (hx : x ∈ space L) : 0 ≤ dust x := by
  apply le_ciInf
  exact residual_nonneg hx

theorem dust_le_residual {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    dust x ≤ residual n x := by
  exact ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact residual_nonneg hx i⟩ n

/-- The residual dust of the finite completions tends to the actual dust. -/
theorem residual_tendsto_dust {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    Tendsto (fun n => residual n x) atTop (nhds (dust x)) := by
  rw [dust_eq_sub_tsum hx]
  exact tendsto_const_nhds.sub (atoms_summable hx).hasSum.tendsto_sum_nat

/-- Retain the finite head prefix and only the genuine dust, omitting all tail heads. -/
def actualDustValue (n : ℕ) (x : Profile) : ℝ :=
  MultipartiteDust.value (fun i : Fin n => x.2 i.val) (dust x)

/-- Removing the residual tail mass from dust has a controlled value discrepancy. -/
theorem actualDustValue_error {L : ℝ} {x : Profile} (hx : x ∈ space L) (n : ℕ) :
    |actualDustValue n x - finiteValue n x| ≤
      (1 + x.1) * (residual n x - dust x) := by
  have htotal : (∑ i : Fin n, x.2 i.val) + max (dust x) (residual n x) ≤ x.1 := by
    rw [max_eq_right (dust_le_residual hx n), Fin.sum_univ_eq_sum_range]
    unfold residual
    linarith
  have h := MultipartiteDust.value_dust_lipschitz (fun i : Fin n => x.2 i.val)
    (fun i => hx.1.1.2 i.val) (dust x) (residual n x) x.1
    (dust_nonneg hx) (residual_nonneg hx n) htotal
  rw [abs_sub_comm (dust x), abs_of_nonneg (sub_nonneg.mpr (dust_le_residual hx n))] at h
  exact h

/-- The genuine-dust finite-head values have the same limiting coefficient value.
This is a value estimate; it does not construct countable physical partitions. -/
theorem actualDustValue_tendsto {L : ℝ} {x : Profile} (hx : x ∈ space L) :
    Tendsto (fun n => actualDustValue n x) atTop (nhds (limitValue x)) := by
  have hzero : Tendsto (fun n => actualDustValue n x - finiteValue n x) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => (1 + x.1) * (residual n x - dust x)) atTop (nhds 0) from by
        simpa using tendsto_const_nhds.mul ((residual_tendsto_dust hx).sub_const (dust x)))
    simpa only [Real.norm_eq_abs] using actualDustValue_error hx n
  have hfinite := (finiteValue_tendstoUniformlyOn L).tendsto_at hx
  simpa only [sub_add_cancel, zero_add] using hzero.add hfinite

end Erdos1017.MultipartiteProfiles
