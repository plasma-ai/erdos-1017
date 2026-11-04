module

public import Erdos1017.SelectedModel.Flows.ForwardPeakSeparation
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Common peak label along an interpolation

Affine interpolation of masses keeps the label type, with a uniform Lipschitz
bound in the parameter, so two uniformly separated peaks at nearby parameters
share a label and a positive separated peak at every parameter gives one common
original peak label on the connected parameter set.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Erdos1017.ForwardPeak

/-- Interpolation keeps the actual original label type unchanged. -/
def affineMass {ι : Type*} (a b : ι → ℝ) (θ : ℝ) (i : ι) : ℝ :=
  (1 - θ) * a i + θ * b i

/-- Unit-interval endpoint coordinates give one uniform Lipschitz bound
for every affine coordinate, regardless of the number of labels. -/
theorem affineMass_abs_sub_le {ι : Type*} (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1)
    (s t : ℝ) (i : ι) : |affineMass a b s i - affineMass a b t i| ≤ |s - t| := by
  have hslope : |b i - a i| ≤ 1 := abs_le.mpr ⟨by linarith [(ha i).2, (hb i).1],
    by linarith [(hb i).2, (ha i).1]⟩
  calc
    |affineMass a b s i - affineMass a b t i| = |(s - t) * (b i - a i)| := by
      congr 1
      unfold affineMass
      ring
    _ = |s - t| * |b i - a i| := abs_mul _ _
    _ ≤ |s - t| * 1 := mul_le_mul_of_nonneg_left hslope (abs_nonneg _)
    _ = |s - t| := mul_one _

/-- Two uniformly separated actual peaks at nearby parameters must have the
same original label. Both positive gaps enter the comparison. -/
theorem separatedPeak_eq_of_abs_sub_lt {ι : Type*} (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1)
    {Δ s t : ℝ} {i j : ι}
    (hi : IsSeparatedPeak (affineMass a b s) Δ i)
    (hj : IsSeparatedPeak (affineMass a b t) Δ j) (hst : |s - t| < Δ) : i = j := by
  by_contra hne
  have hsi := hi j (fun he => hne he.symm)
  have htj := hj i hne
  have hdi := abs_le.mp (affineMass_abs_sub_le a b ha hb s t i)
  have hdj := abs_le.mp (affineMass_abs_sub_le a b ha hb s t j)
  linarith [hdi.2, hdj.1]

/-- A positive separated peak at every interpolation parameter constructs a
locally constant actual selector, hence one common original peak label on
the connected parameter interval. No finite atomic support is assumed. -/
theorem exists_common_separated_peak {ι : Type*} (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hpeak : ∀ θ ∈ Icc (0 : ℝ) 1, ∃ i, IsSeparatedPeak (affineMass a b θ) Δ i) :
    ∃ i, ∀ θ ∈ Icc (0 : ℝ) 1, IsSeparatedPeak (affineMass a b θ) Δ i := by
  classical
  choose p hp using fun θ : Icc (0 : ℝ) 1 => hpeak θ θ.property
  have hlocal : IsLocallyConstant p := by
    apply (IsLocallyConstant.iff_eventually_eq p).mpr
    intro t
    filter_upwards [Metric.ball_mem_nhds t hΔ] with s hs
    apply separatedPeak_eq_of_abs_sub_lt a b ha hb (hp s) (hp t)
    simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hs
  have : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  let t₀ : Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  refine ⟨p t₀, ?_⟩
  intro θ hθ
  have heq := hlocal.apply_eq_of_preconnectedSpace (⟨θ, hθ⟩ : Icc (0 : ℝ) 1) t₀
  rw [← heq]
  exact hp ⟨θ, hθ⟩

/-- Any actual peak witnesses at any two parameters identify the same
original label, rather than merely some choice of a constant selector. -/
theorem separated_peak_label_eq {ι : Type*} (a b : ι → ℝ)
    (ha : ∀ i, a i ∈ Icc (0 : ℝ) 1) (hb : ∀ i, b i ∈ Icc (0 : ℝ) 1)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hpeak : ∀ θ ∈ Icc (0 : ℝ) 1, ∃ i, IsSeparatedPeak (affineMass a b θ) Δ i)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) {i j : ι}
    (hi : IsSeparatedPeak (affineMass a b s) Δ i)
    (hj : IsSeparatedPeak (affineMass a b t) Δ j) : i = j := by
  obtain ⟨k, hk⟩ := exists_common_separated_peak a b ha hb Δ hΔ hpeak
  exact (hi.unique (hk s hs) hΔ).trans (hj.unique (hk t ht) hΔ).symm

end Erdos1017.ForwardPeak
