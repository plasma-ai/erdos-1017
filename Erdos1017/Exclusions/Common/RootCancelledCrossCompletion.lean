module

public import Erdos1017.Exclusions.Common.Flows.MaskedCompletionDensityReturn
public import Erdos1017.Exclusions.Common.Covered.CoveredAtomCompletion

/-!
# Cross completion with root cancellation

The mask `crossMask` inserts cross edges without changing either within-set
square; deleting a cross-completed `F` vertex cancels its possible root star
against a retained `C` vertex, so original independent-sample tests license
neutral completion across `C` and `F` only.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.FiniteArity

/-- Cross insertion changes neither within-set square. -/
def crossMask {Ω : Type*} (C F : Set Ω) : Set (Ω × Ω) := (C ×ˢ F) ∪ (F ×ˢ C)

theorem measurableSet_crossMask {Ω : Type*} [MeasurableSpace Ω] (C F : Set Ω)
    (hC : MeasurableSet C) (hF : MeasurableSet F) : MeasurableSet (crossMask C F) :=
  (hC.prod hF).union (hF.prod hC)

theorem crossMask_symm {Ω : Type*} (C F : Set Ω) (p : Ω × Ω) :
    p.swap ∈ crossMask C F ↔ p ∈ crossMask C F := by
  simp only [crossMask, mem_union, mem_prod, Prod.swap]
  tauto

private theorem pairCharge_erase_cross {α : Type*} [DecidableEq α]
    (U : Finset α) (a : α) (ha : a ∈ U) (Y : α → α → ℝ)
    (hdiag : ∀ i, Y i i = 0) (hsym : ∀ i j, Y i j = Y j i) :
    pairCharge U Y = pairCharge (U.erase a) Y + ∑ b ∈ U.erase a, Y a b := by
  have hU : {a} ∪ U.erase a = U := by ext b; simp; grind
  have hdisj : Disjoint ({a} : Finset α) (U.erase a) := by simp
  nth_rw 1 [← hU]
  rw [pairCharge_union _ _ hdisj]
  simp only [pairCharge, crossSum, Finset.sum_singleton, hdiag, zero_div, zero_add]
  simp_rw [hsym a]
  ring

/-- Deleting a cross-completed F vertex cancels its possible root star
against a retained C vertex. Every final test is an original subset test;
there is no insertion inside either C or F. -/
theorem pairCharge_le_of_root_cancelled_cross {α : Type*} [DecidableEq α]
    (U : Finset α) (Y : α → α → ℝ) (R C F : Set α) (ell : ℝ)
    (hdiag : ∀ i, Y i i = 0) (hsym : ∀ i j, Y i j = Y j i)
    (hCR : ∀ c ∈ C, c ∉ R) (hFC : ∀ f ∈ F, f ∉ C)
    (hroot : ∀ a ∈ U, ∀ b ∈ U, a ∈ R → b ∈ R → a = b)
    (hcross : ∀ f ∈ U, ∀ c ∈ U, f ∈ F → c ∈ C → Y f c ≤ -ell)
    (hstar : ∀ f ∈ U, ∀ r ∈ U, f ∈ F → r ∈ R → Y f r ≤ ell)
    (hbody : ∀ f ∈ U, ∀ b ∈ U, f ≠ b → f ∈ F → b ∉ R → Y f b ≤ 0)
    (htest : ∀ S ⊆ U, ¬(∃ c ∈ S, c ∈ C ∧ ∃ f ∈ S, f ∈ F) → pairCharge S Y ≤ 1) :
    pairCharge U Y ≤ 1 := by
  have hall : ∀ S : Finset α, S ⊆ U → pairCharge S Y ≤ 1 := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hS
    by_cases hcrossS : ∃ c ∈ S, c ∈ C ∧ ∃ f ∈ S, f ∈ F
    · obtain ⟨c, hc, hcC, f, hf, hfF⟩ := hcrossS
      have hfc : f ≠ c := fun he => hFC f hfF (he ▸ hcC)
      have hc' : c ∈ S.erase f := Finset.mem_erase.mpr ⟨hfc.symm, hc⟩
      have hrow : (∑ b ∈ S.erase f, Y f b) ≤ 0 := by
        by_cases hex : ∃ r ∈ S.erase f, r ∈ R
        · obtain ⟨r, hr, hrR⟩ := hex
          have hcr : c ≠ r := fun he => hCR c hcC (he.symm ▸ hrR)
          calc
            _ ≤ ∑ b ∈ S.erase f,
                ((if b = c then -ell else 0) + (if b = r then ell else 0)) := by
              apply Finset.sum_le_sum
              intro b hb
              have hbS := Finset.mem_of_mem_erase hb
              by_cases hbc : b = c
              · subst b
                simpa only [ite_true, hcr, ite_false, add_zero] using
                  hcross f (hS hf) c (hS hc) hfF hcC
              · by_cases hbr : b = r
                · subst b
                  simpa only [hbc, ite_false, ite_true, zero_add] using
                    hstar f (hS hf) r (hS hbS) hfF hrR
                · simp only [hbc, hbr, ite_false, add_zero]
                  apply hbody f (hS hf) b (hS hbS) (Finset.ne_of_mem_erase hb).symm hfF
                  intro hbR
                  exact hbr (hroot b (hS hbS) r (hS (Finset.mem_of_mem_erase hr)) hbR hrR)
            _ = 0 := by simp [Finset.sum_add_distrib, hc', hr]
        · apply Finset.sum_nonpos
          intro b hb
          exact hbody f (hS hf) b (hS (Finset.mem_of_mem_erase hb))
            (Finset.ne_of_mem_erase hb).symm hfF (fun hbR => hex ⟨b, hb, hbR⟩)
      rw [pairCharge_erase_cross S f hf Y hdiag hsym]
      have hle := ih (S.erase f) (Finset.erase_ssubset hf)
        (Finset.Subset.trans (Finset.erase_subset _ _) hS)
      linarith
    · exact htest S hS hcrossS
  exact hall U Finset.Subset.rfl

/-- Actual old independent-sample tests license neutral completion only
across C and F. A retained C vertex cancels each possible F-root star;
no C-square insertion or repeated physical point is used. -/
theorem feasibleOrder_root_cancelled_cross
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hAsym : ∀ x y, A x y = A y x) (hYsym : ∀ x y, Y x y = Y y x)
    (R C F : Set Ω) (hRC : Disjoint R C) (hRF : Disjoint R F) (hCF : Disjoint C F)
    (ell : ℝ) (hell : 0 ≤ ell)
    (hroot : ∀ᵐ p ∂μ.prod μ, p.1 ∈ R → p.2 ∈ R → A p.1 p.2 = false)
    (hcross : ∀ᵐ p ∂μ.prod μ, p.1 ∈ C → p.2 ∈ F → A p.1 p.2 = false)
    (hbody : ∀ᵐ p ∂μ.prod μ, p.1 ∉ R → p.2 ∉ R → Y p.1 p.2 ≤ 0)
    (hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ F → p.2 ∈ R → Y p.1 p.2 ≤ ell)
    (hfull : ∀ n, FeasibleOrder μ A Y n) (n : ℕ) :
    FeasibleOrder μ (maskAdjacency A (crossMask C F))
      (maskCharge A Y (crossMask C F) (-ell)) n := by
  have hpairs := ae_all_pairs μ n _ (hroot.and (hcross.and (hbody.and hstar)))
  have hsub := ae_all_subtuples μ n n
    (fun _ v => TupleClique A v → tupleCharge Y v ≤ 1) (fun k _ => hfull k)
  filter_upwards [hpairs, hsub] with v hp hv hclique
  let Z := maskCharge A Y (crossMask C F) (-ell)
  let z (i j : Fin n) : ℝ := if i = j then 0 else Z (v i) (v j)
  have hsepC {x : Ω} (hx : x ∈ C) : x ∉ R := fun hr => Set.disjoint_left.mp hRC hr hx
  have hsepF {x : Ω} (hx : x ∈ F) : x ∉ R := fun hr => Set.disjoint_left.mp hRF hr hx
  have hsepFC {x : Ω} (hx : x ∈ F) : x ∉ C := fun hc => Set.disjoint_left.mp hCF hc hx
  have hZsym (x y : Ω) : Z x y = Z y x := by
    simp only [Z, maskCharge, crossMask, mem_union, mem_prod, hAsym x y, hYsym x y]
    congr 1
    exact propext (by tauto)
  have hzsym (i j : Fin n) : z i j = z j i := by
    by_cases hij : i = j
    · simp [z, hij]
    · simp [z, hij, Ne.symm hij, hZsym]
  change pairCharge Finset.univ z ≤ 1
  apply pairCharge_le_of_root_cancelled_cross Finset.univ z
    (v ⁻¹' R) (v ⁻¹' C) (v ⁻¹' F) ell (fun i => by simp [z]) hzsym
    (fun i hi => hsepC hi) (fun i hi => hsepFC hi)
  · intro i _ j _ hiR hjR
    by_contra hij
    have hA := (hp i j hij).1 hiR hjR
    have hmask : (v i, v j) ∉ crossMask C F := by
      rintro (h | h)
      · exact hsepC h.1 hiR
      · exact hsepF h.1 hiR
    have ht := hclique i j hij
    simp only [maskAdjacency, ite_eq_right hmask, hA] at ht
    contradiction
  · intro i _ j _ hiF hjC
    have hij : i ≠ j := fun he => hsepFC hiF (he ▸ hjC)
    have hA : A (v i) (v j) = false := by
      rw [hAsym]
      exact (hp j i (Ne.symm hij)).2.1 hjC hiF
    have hmask : (v i, v j) ∈ crossMask C F := Or.inr ⟨hiF, hjC⟩
    simp [z, Z, maskCharge, hij, hmask, hA]
  · intro i _ j _ hiF hjR
    have hij : i ≠ j := fun he => hsepF hiF (he ▸ hjR)
    have hmask : (v i, v j) ∉ crossMask C F := by
      rintro (h | h)
      · exact hsepF h.2 hjR
      · exact hsepC h.2 hjR
    simpa only [z, hij, ite_false, Z, maskCharge, hmask, false_and] using
      (hp i j hij).2.2.2 hiF hjR
  · intro i _ j _ hij hiF hjR
    simp only [z, hij, ite_false, Z, maskCharge]
    split_ifs
    · exact neg_nonpos.mpr hell
    · exact (hp i j hij).2.2.1 (hsepF hiF) hjR
  · intro T _ hnocross
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have he (i : Fin T.card) : e i ∈ T := T.orderEmbOfFin_mem rfl i
    have hn : T.card ≤ n := by simpa using Finset.card_le_univ T
    have hnotmask {i j : Fin n} (hi : i ∈ T) (hj : j ∈ T) :
        (v i, v j) ∉ crossMask C F := by
      rintro (h | h)
      · exact hnocross ⟨i, hi, h.1, j, hj, h.2⟩
      · exact hnocross ⟨j, hj, h.2, i, hi, h.1⟩
    have hold : TupleClique A (fun i => v (e i)) := by
      intro i j hij
      have heij : e i ≠ e j := fun heq => hij (e.injective heq)
      simpa only [maskAdjacency, ite_eq_right (hnotmask (he i) (he j))] using
        hclique (e i) (e j) heij
    have ht := hv T.card hn e hold
    rw [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ T rfl] at ht
    convert ht using 1
    unfold pairCharge crossSum
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · simp [z, hij]
    · simp only [z, hij, ite_false, Z, maskCharge, hnotmask hi hj, false_and]

end Erdos1017.FiniteArity
