module

public import Erdos1017.Benchmark.BenchmarkProperties

/-!
# Mixed contact profile at a one-head integer contact

A one-head integer contact with slope between one half and two thirds uses the
second count interval, which with the smooth-`W` slope determines the three
region masses from their stationary rows and hence the mixed density and value.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MixedContactIdentity

/-- An actual one-head integer contact with own slope between one half
and two thirds must use the second count interval. -/
theorem integer_contact_eq_two {j : ℕ} {b e ell : ℝ}
    (hj : 1 ≤ j) (hb : 0 < b)
    (hell : ell ∈ Set.Ioo (1 / 2 : ℝ) (2 / 3))
    (hfirst : ((j : ℝ) - 1) * b ≤ e)
    (hfloor : 2 / ((j : ℝ) * (j + 1)) < ell)
    (hrow : b * (1 - 2 / ((j : ℝ) + 1)) =
      e * (ell - 2 / ((j : ℝ) * (j + 1)))) : j = 2 := by
  have hjne : j ≠ 1 := by
    rintro rfl
    norm_num at hfloor
    linarith [hell.2]
  by_contra hne
  have hjthree : 3 ≤ j := by omega
  have hJ : (3 : ℝ) ≤ j := by exact_mod_cast hjthree
  have hJ0 : (0 : ℝ) < j := by linarith
  have hJ1 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have hden : (0 : ℝ) < (j : ℝ) * (j + 1) := mul_pos hJ0 hJ1
  have hrow' : b * (j : ℝ) * (j - 1) =
      e * ((j : ℝ) * (j + 1) * ell - 2) := by
    have h := congrArg (fun x : ℝ => x * ((j : ℝ) * (j + 1))) hrow
    field_simp at h
    nlinarith only [h]
  have hcoef : (j : ℝ) < (j : ℝ) * (j + 1) * ell - 2 := by
    have hstrict := mul_lt_mul_of_pos_left hell.1 hden
    have hquad : (4 : ℝ) < (j : ℝ) * (j - 1) := by nlinarith [sq_nonneg ((j : ℝ) - 3)]
    nlinarith only [hstrict, hquad]
  have hleft : 0 < ((j : ℝ) - 1) * b := mul_pos (by linarith) hb
  have hbound := mul_le_mul_of_nonneg_right hfirst
    (show 0 ≤ (j : ℝ) * (j + 1) * ell - 2 by linarith)
  have hstrict := mul_lt_mul_of_pos_left hcoef hleft
  nlinarith only [hrow', hbound, hstrict]

/-- The second count interval and the own smooth-W slope determine the
literal three-region masses, using only their actual stationary rows. -/
theorem profile_eq {a b e ell s : ℝ} (hs : 0 < s)
    (hmass : a + b + e = 1) (hell : ell = (s + 1) / (3 * s))
    (hrowAE : b * (1 - 2 / 3) = e * (ell - 1 / 3))
    (hrowAB : a * (1 + ell) + e * (2 / 3 + ell) = b * (1 + ell)) :
    a = (-3 * s ^ 2 + 3 * s + 1) / Benchmark.mixedDenominator s ∧
      b = (4 * s + 1) / Benchmark.mixedDenominator s ∧
      e = s * (4 * s + 1) / Benchmark.mixedDenominator s := by
  have hsne : s ≠ 0 := hs.ne'
  have hden : Benchmark.mixedDenominator s ≠ 0 :=
    (Benchmark.mixedDenominator_pos hs.le).ne'
  have he : e = s * b := by
    rw [hell] at hrowAE
    field_simp at hrowAE
    nlinarith only [hrowAE]
  have hcross : a * (4 * s + 1) = b * (-3 * s ^ 2 + 3 * s + 1) := by
    rw [hell, he] at hrowAB
    field_simp at hrowAB
    nlinarith only [hrowAB]
  have hb : b = (4 * s + 1) / Benchmark.mixedDenominator s := by
    apply (eq_div_iff hden).mpr
    dsimp only [Benchmark.mixedDenominator]
    nlinarith only [hcross, congrArg (fun x : ℝ => x * (4 * s + 1)) hmass,
      congrArg (fun x : ℝ => x * (4 * s + 1)) he]
  refine ⟨?_, hb, by rw [he, hb]; ring⟩
  rw [he, hb] at hmass
  apply (eq_div_iff hden).mpr
  field_simp at hmass
  dsimp only [Benchmark.mixedDenominator] at hmass ⊢
  nlinarith only [hmass]

/-- Substitution of the actual stationary profile gives the defining
mixed density and value, with no envelope or optimizer premise. -/
theorem density_value_eq {a b e s : ℝ} (hs : 0 < s)
    (ha : a = (-3 * s ^ 2 + 3 * s + 1) / Benchmark.mixedDenominator s)
    (hb : b = (4 * s + 1) / Benchmark.mixedDenominator s)
    (he : e = s * (4 * s + 1) / Benchmark.mixedDenominator s) :
    (a ^ 2 + b ^ 2) / 2 + a * e = Benchmark.mixedDensity s ∧
      a * b + b * e * (2 / 3) - e ^ 2 / 6 = Benchmark.mixedValue s := by
  have hden : Benchmark.mixedDenominator s ≠ 0 :=
    (Benchmark.mixedDenominator_pos hs.le).ne'
  rw [ha, hb, he]
  constructor <;> simp only [Benchmark.mixedDensity, Benchmark.mixedValue] <;>
    field_simp <;> ring

end Erdos1017.MixedContactIdentity
