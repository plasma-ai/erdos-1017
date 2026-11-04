module

public import Erdos1017.Models.PhysicalPrimal.FiniteChargePartition
public import Erdos1017.Models.PhysicalPrimal.TupleSampling

/-!
# Signed star edit at an independent root

The edit direction increases the independent root-to-cell star and decreases the
cell's other present incidences on the unchanged graph; within an explicit
radius both signs of the edited charge pass every finite test, stay measurable
and bounded, and keep zero charge on absent edges.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Erdos1017.IndependentStarPerturbation

open FiniteArity

/-- Increase the independent root-to-cell star and decrease the cell's
other present incidences, on the unchanged Boolean graph. -/
def direction {Ω : Type*} (A : Ω → Ω → Bool) (I J : Set Ω) (x y : Ω) : ℝ :=
  if (x ∈ I ∧ y ∈ J) ∨ (y ∈ I ∧ x ∈ J) then 1
  else if A x y = true ∧ ((x ∈ J ∧ y ∉ I ∪ J) ∨ (y ∈ J ∧ x ∉ I ∪ J)) then -1
  else 0

/-- The actual signed charge edit, retaining the original carrier and graph. -/
def charge {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I J : Set Ω) (eps : ℝ) (x y : Ω) : ℝ :=
  Y x y + eps * direction A I J x y

/-- A concrete two-sided interval pays the star and every body incidence. -/
def radius (t p0 : ℝ) : ℝ := min (1 - t) (min (p0 - (1 - t)) p0)

theorem radius_pos {t p0 : ℝ} (ht : t < 1) (hp : 1 - t < p0) :
    0 < radius t p0 := by
  exact lt_min (sub_pos.mpr ht) (lt_min (sub_pos.mpr hp) (by linarith))

theorem direction_symm {Ω : Type*} (A : Ω → Ω → Bool)
    (hA : ∀ x y, A x y = A y x) (I J : Set Ω) (x y : Ω) :
    direction A I J x y = direction A I J y x := by
  simp only [direction, hA x y, or_comm]

theorem charge_symm {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hA : ∀ x y, A x y = A y x) (hY : ∀ x y, Y x y = Y y x)
    (I J : Set Ω) (eps : ℝ) (x y : Ω) :
    charge A Y I J eps x y = charge A Y I J eps y x := by
  rw [charge, charge, hY, direction_symm A hA]

private theorem pairCharge_erase {α : Type*} [DecidableEq α]
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

private theorem pairCharge_le_penalty {α : Type*} [DecidableEq α]
    (T : Finset α) (Z : α → α → ℝ) (p0 : ℝ)
    (hdiag : ∀ i, Z i i = 0)
    (hbound : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Z i j ≤ -p0) :
    pairCharge T Z ≤ -p0 * (T.card : ℝ) * ((T.card : ℝ) - 1) / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  unfold crossSum
  calc
    _ ≤ ∑ i ∈ T, ∑ j ∈ T, (-p0 - if i = j then -p0 else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · simp [hij, hdiag]
      · simpa [hij] using hbound i hi j hj hij
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.sum_ite_eq]
      simp
      ring

/-- Two actual anchors and their old triangles control every number of
outside vertices. No maximum order or outside-count bound is assumed. -/
private theorem pairCharge_two_anchors_le {α : Type*} [DecidableEq α]
    (S : Finset α) (Z : α → α → ℝ) (a b : α) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hdiag : ∀ i, Z i i = 0) (hsym : ∀ i j, Z i j = Z j i)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hstar : Z a b ≤ 1) (hslack : 1 - Z a b ≤ p0)
    (htriangle : ∀ k ∈ S, k ≠ a → k ≠ b → Z a b + Z a k + Z b k ≤ 1)
    (hbody : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → i ≠ a → i ≠ b →
      j ≠ a → j ≠ b → Z i j ≤ -p0) : pairCharge S Z ≤ 1 := by
  let T := (S.erase a).erase b
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hsum : (∑ k ∈ T, (Z a k + Z b k)) ≤ (T.card : ℝ) * (1 - Z a b) := by
    calc
      _ ≤ ∑ _k ∈ T, (1 - Z a b) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_erase.mp hk
        have hk'' := Finset.mem_erase.mp hk'.2
        linarith only [htriangle k hk''.2 hk''.1 hk'.1]
      _ = _ := by simp; ring
  have hbody' := pairCharge_le_penalty T Z p0 hdiag (by
    intro i hi j hj hij
    have hi' := Finset.mem_erase.mp hi
    have hi'' := Finset.mem_erase.mp hi'.2
    have hj' := Finset.mem_erase.mp hj
    have hj'' := Finset.mem_erase.mp hj'.2
    exact hbody i hi''.2 j hj''.2 hij hi''.1 hi'.1 hj''.1 hj'.1)
  have hinv : pairCharge S Z = pairCharge T Z + Z a b +
      ∑ k ∈ T, (Z a k + Z b k) := by
    rw [pairCharge_erase S a ha Z hdiag hsym,
      pairCharge_erase (S.erase a) b hb' Z hdiag hsym]
    have he := Finset.sum_erase_add (S.erase a) (fun k => Z a k) hb'
    change _ + ∑ k ∈ S.erase a, Z a k = _
    rw [← he, Finset.sum_add_distrib]
    ring
  by_cases hn : T.card = 0
  · have hT : T = ∅ := Finset.card_eq_zero.mp hn
    rw [hinv, hT]
    simpa [pairCharge, crossSum] using hstar
  · have hn1 : (1 : ℝ) ≤ T.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    by_cases hone : T.card = 1
    · rw [hone] at hbody' hsum
      norm_num at hbody' hsum
      linarith only [hinv, hbody', hsum]
    · have hn2 : (2 : ℝ) ≤ T.card := by exact_mod_cast (show 2 ≤ T.card by omega)
      have hpair := mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hn1)
      have hweight := mul_nonneg hp0 hpair
      have hslack' := mul_le_mul_of_nonneg_left hslack (sub_nonneg.mpr hn1)
      nlinarith only [hinv, hbody', hsum, hweight, hslack']

/-- The direction is uniformly bounded independently of the graph and cells. -/
theorem direction_abs_le_one {Ω : Type*} (A : Ω → Ω → Bool) (I J : Set Ω) (x y : Ω) :
    |direction A I J x y| ≤ 1 := by
  unfold direction
  split_ifs <;> norm_num

/-- Every original finite test remains valid for both signs of the edit.
Atomic uniqueness and all triangle tests are derived on one original
product-AE event; no pointwise representative or count inventory is supplied. -/
theorem full_feasible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (hA : ∀ x y, A x y = A y x) (hY : ∀ x y, Y x y = Y y x)
    (I J : Set Ω) (hdisj : Disjoint I J) (t p0 eps : ℝ)
    (ht : t < 1) (hp : 1 - t < p0) (heps : |eps| ≤ radius t p0)
    (hI : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ I → A p.1 p.2 = false)
    (hJ : ∀ᵐ p ∂μ.prod μ, p.1 ∈ J → p.2 ∈ J → A p.1 p.2 = false)
    (hstar : ∀ᵐ p ∂μ.prod μ, p.1 ∈ I → p.2 ∈ J → Y p.1 p.2 = t)
    (hbody : ∀ᵐ p ∂μ.prod μ,
      p.1 ∉ I → p.2 ∉ I → A p.1 p.2 = true → Y p.1 p.2 ≤ -p0)
    (hfull : ∀ n, FeasibleOrder μ A Y n) :
    ∀ n, FeasibleOrder μ A (charge A Y I J eps) n := by
  have he1 : |eps| ≤ 1 - t := heps.trans (min_le_left _ _)
  have he2 : |eps| ≤ p0 - (1 - t) :=
    heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he3 : |eps| ≤ p0 := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hp0 : 0 ≤ p0 := by linarith
  intro n
  have hpairs := ae_all_pairs μ n _ (hI.and (hJ.and (hstar.and hbody)))
  have hsub := ae_all_subtuples μ n n
    (fun _ v => TupleClique A v → tupleCharge Y v ≤ 1) (fun k _ => hfull k)
  filter_upwards [hpairs, hsub] with v hv htests hc
  let Z (i j : Fin n) : ℝ := if i = j then 0 else charge A Y I J eps (v i) (v j)
  let Z0 (i j : Fin n) : ℝ := if i = j then 0 else Y (v i) (v j)
  have hzdiag (i : Fin n) : Z i i = 0 := by simp [Z]
  have hzsym (i j : Fin n) : Z i j = Z j i := by
    by_cases hij : i = j
    · simp [Z, hij]
    · simp [Z, hij, Ne.symm hij, charge_symm A Y hA hY]
  have hold (T : Finset (Fin n)) : pairCharge T Z0 ≤ 1 := by
    let e := (T.orderEmbOfFin rfl).toEmbedding
    have htest := htests T.card (by simpa using Finset.card_le_univ T) e
      (fun i j hij => hc (e i) (e j) (fun he => hij (e.injective he)))
    rwa [tupleCharge_subtuple, Finset.map_orderEmbOfFin_univ T rfl] at htest
  have huniI (a b : Fin n) (ha : v a ∈ I) (hb : v b ∈ I) : a = b := by
    by_contra hab
    have hfalse := (hv a b hab).1 ha hb
    exact Bool.false_ne_true (hfalse.symm.trans (hc a b hab))
  have huniJ (a b : Fin n) (ha : v a ∈ J) (hb : v b ∈ J) : a = b := by
    by_contra hab
    have hfalse := (hv a b hab).2.1 ha hb
    exact Bool.false_ne_true (hfalse.symm.trans (hc a b hab))
  change pairCharge Finset.univ Z ≤ 1
  by_cases hexJ : ∃ b, v b ∈ J
  · obtain ⟨b, hb⟩ := hexJ
    by_cases hexI : ∃ a, v a ∈ I
    · obtain ⟨a, ha⟩ := hexI
      have hab : a ≠ b := fun he => Set.disjoint_left.mp hdisj ha (he.symm ▸ hb)
      have haJ : v a ∉ J := fun h => Set.disjoint_left.mp hdisj ha h
      have hbI : v b ∉ I := fun h => Set.disjoint_left.mp hdisj h hb
      have houtI (k : Fin n) (hk : k ≠ a) : v k ∉ I := fun h => hk (huniI k a h ha)
      have houtJ (k : Fin n) (hk : k ≠ b) : v k ∉ J := fun h => hk (huniJ k b h hb)
      have habstar : Z a b = t + eps := by
        simp [Z, hab, charge, direction, ha, hb, (hv a b hab).2.2.1 ha hb]
      apply pairCharge_two_anchors_le Finset.univ Z a b (Finset.mem_univ _) (Finset.mem_univ _)
        hab hzdiag hzsym p0 hp0
      · rw [habstar]
        linarith only [le_abs_self eps, he1]
      · rw [habstar]
        linarith only [neg_abs_le eps, he2]
      · intro k _ hka hkb
        have hkI := houtI k hka
        have hkJ := houtJ k hkb
        have ht := hold {a, b, k}
        have hyab := (hv a b hab).2.2.1 ha hb
        simp [pairCharge, crossSum, Z0, hab, hab.symm, hka, hka.symm,
          hkb, hkb.symm, hY (v b) (v a), hY (v k) (v a), hY (v k) (v b)] at ht
        simp [Z, hab, hka.symm, hkb.symm, charge, direction,
          ha, hb, haJ, hbI, hkI, hkJ, hc b k hkb.symm, hyab]
        nlinarith only [ht, hyab]
      · intro i _ j _ hij hia hib hja hjb
        have hiI := houtI i hia
        have hjI := houtI j hja
        have hiJ := houtJ i hib
        have hjJ := houtJ j hjb
        simpa [Z, hij, charge, direction, hiI, hjI, hiJ, hjJ] using
          (hv i j hij).2.2.2 hiI hjI (hc i j hij)
    · have hnonpos (i j : Fin n) : Z i j ≤ 0 := by
        by_cases hij : i = j
        · simp [Z, hij]
        · have hiI : v i ∉ I := fun h => hexI ⟨i, h⟩
          have hjI : v j ∉ I := fun h => hexI ⟨j, h⟩
          have hbody := (hv i j hij).2.2.2 hiI hjI (hc i j hij)
          have he : eps * direction A I J (v i) (v j) ≤ |eps| := by
            calc
              _ ≤ |eps * direction A I J (v i) (v j)| := le_abs_self _
              _ = |eps| * |direction A I J (v i) (v j)| := abs_mul _ _
              _ ≤ |eps| * 1 := mul_le_mul_of_nonneg_left
                (direction_abs_le_one A I J (v i) (v j)) (abs_nonneg _)
              _ = _ := mul_one _
          dsimp only [Z]
          rw [ite_eq_right hij, charge]
          linarith only [hbody, he, he3]
      have hn : pairCharge Finset.univ Z ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (Finset.sum_nonpos (fun i _ => Finset.sum_nonpos (fun j _ => hnonpos i j)))
          (by norm_num)
      linarith
  · have heq : Z = Z0 := by
      funext i j
      have hiJ : v i ∉ J := fun h => hexJ ⟨i, h⟩
      have hjJ : v j ∉ J := fun h => hexJ ⟨j, h⟩
      simp [Z, Z0, charge, direction, hiJ, hjJ]
    rw [heq]
    exact hold Finset.univ

/-- The same-graph direction is jointly measurable for measurable cells. -/
theorem measurable_direction {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) :
    Measurable (Function.uncurry (direction A I J)) := by
  apply Measurable.ite (((hI.preimage measurable_fst).inter
    (hJ.preimage measurable_snd)).union
      ((hI.preimage measurable_snd).inter (hJ.preimage measurable_fst))) measurable_const
  apply Measurable.ite
    ((hA (measurableSet_singleton true)).inter
      (((hJ.preimage measurable_fst).inter ((hI.union hJ).compl.preimage measurable_snd)).union
        ((hJ.preimage measurable_snd).inter ((hI.union hJ).compl.preimage measurable_fst))))
    measurable_const measurable_const

/-- The edited charge remains jointly measurable. -/
theorem measurable_charge {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Ω → Bool) (hA : Measurable (Function.uncurry A))
    (Y : Ω → Ω → ℝ) (hY : Measurable (Function.uncurry Y))
    (I J : Set Ω) (hI : MeasurableSet I) (hJ : MeasurableSet J) (eps : ℝ) :
    Measurable (Function.uncurry (charge A Y I J eps)) :=
  hY.add (measurable_const.mul (measurable_direction A hA I J hI hJ))

/-- An arbitrary original uniform bound suffices; no compact color box
is imposed on the signed charge. -/
theorem charge_abs_bound {Ω : Type*} (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ)
    (I J : Set Ω) (eps B : ℝ) (hB : ∀ x y, |Y x y| ≤ B) (x y : Ω) :
    |charge A Y I J eps x y| ≤ B + |eps| := by
  calc
    _ ≤ |Y x y| + |eps * direction A I J x y| := abs_add_le _ _
    _ = |Y x y| + |eps| * |direction A I J x y| := by rw [abs_mul]
    _ ≤ B + |eps| * 1 := add_le_add (hB x y)
      (mul_le_mul_of_nonneg_left (direction_abs_le_one A I J x y) (abs_nonneg _))
    _ = _ := by ring

/-- Only the actual I-J adjacency license is needed to preserve zero
charge on absent edges. No universal-root premise is hidden in the edit. -/
theorem charge_zero_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → Ω → Bool) (Y : Ω → Ω → ℝ) (I J : Set Ω) (eps : ℝ)
    (hzero : ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → Y p.1 p.2 = 0)
    (hjoined : ∀ᵐ p ∂μ.prod μ,
      (p.1 ∈ I ∧ p.2 ∈ J) ∨ (p.2 ∈ I ∧ p.1 ∈ J) → A p.1 p.2 = true) :
    ∀ᵐ p ∂μ.prod μ, A p.1 p.2 = false → charge A Y I J eps p.1 p.2 = 0 := by
  filter_upwards [hzero, hjoined] with p hz hj hp
  have hn : ¬((p.1 ∈ I ∧ p.2 ∈ J) ∨ (p.2 ∈ I ∧ p.1 ∈ J)) := by
    intro h
    have ht := hj h
    simp [hp] at ht
  simp [charge, direction, hn, hp, hz hp]

end Erdos1017.IndependentStarPerturbation
