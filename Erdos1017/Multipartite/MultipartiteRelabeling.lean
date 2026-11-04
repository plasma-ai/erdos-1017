module

public import Erdos1017.Multipartite.Dust.DustReindex
public import Erdos1017.Multipartite.MultipartiteCountableValue
public import Erdos1017.Multipartite.MultipartiteSorting
public import Mathlib.Logic.Equiv.Fintype

/-!
# Relabeling heads in the countable coefficient problem

Masking heads and injectively relabeling the positive heads preserve the
countable coefficient value, so every normalized summable competitor has a
sorted representative with the same total mass, dust, square moment and value
(`exists_sorted_representative`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Filter

namespace Erdos1017.MultipartiteDust

/-- Ignore every head outside a chosen set, retaining the two dust coefficients. -/
def maskHeadSet {m : ℕ} (S : Finset (Fin m)) (C : Coefficients m) : Coefficients m
  | .inl i => if i ∈ S then head C i else 0
  | .inr (.inl (i, j)) => if i ∈ S ∧ j ∈ S then pair C i j else 0
  | .inr (.inr (.inl i)) => if i ∈ S then incident C i else 0
  | .inr (.inr (.inr false)) => linear C
  | .inr (.inr (.inr true)) => penalty C

theorem maskHeadSet_objective {m : ℕ} (S : Finset (Fin m)) (C : Coefficients m)
    (p : Fin m → ℝ) (s : ℝ) :
    objective p s (maskHeadSet S C) = objective (fun i => if i ∈ S then p i else 0) s C := by
  have hh : (∑ i, head (maskHeadSet S C) i * p i) =
      ∑ i, head C i * (if i ∈ S then p i else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [head, maskHeadSet, hi]
  have hpair : (∑ i, ∑ j, pair (maskHeadSet S C) i j * (if i < j then 1 else 0) * p i * p j) =
      ∑ i, ∑ j, pair C i j * (if i < j then 1 else 0) *
        (if i ∈ S then p i else 0) * (if j ∈ S then p j else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp [pair, maskHeadSet, hi, hj]
  have hi : (∑ i, incident (maskHeadSet S C) i * p i * s) =
      ∑ i, incident C i * (if i ∈ S then p i else 0) * s := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [incident, maskHeadSet, hi]
  simp only [objective, hh, hpair, hi, linear, penalty, maskHeadSet]

/-- Masking a head is a genuine restriction of all Boolean head tests. -/
theorem maskHeadSet_feasible {m : ℕ} (S : Finset (Fin m)) {C : Coefficients m}
    (hC : C ∈ feasible m) : maskHeadSet S C ∈ feasible m := by
  have hbox (c : Coordinate m) : 0 ≤ maskHeadSet S C c ∧ maskHeadSet S C c ≤ 1 := by
    rcases c with i | (⟨i, j⟩ | (i | b))
    all_goals simp only [maskHeadSet]
    all_goals (try split_ifs) <;> first
      | exact ⟨hC.1.1 _, hC.1.2 _⟩
      | exact ⟨le_rfl, zero_le_one⟩
      | cases b <;> exact ⟨hC.1.1 _, hC.1.2 _⟩
  refine ⟨⟨fun c => (hbox c).1, fun c => (hbox c).2⟩, ?_⟩
  intro X k
  have h := hC.2 (fun i => if i ∈ S then X i else false) k
  rw [DustCellBridge.charge_eq_objective, maskHeadSet_objective]
  rw [DustCellBridge.charge_eq_objective] at h
  have hb : (fun i => if i ∈ S then Selector.bit (X i) else 0) =
      fun i => Selector.bit (if i ∈ S then X i else false) := by
    funext i
    by_cases hi : i ∈ S <;> simp [hi, Selector.bit]
  simpa only [hb, penalty, maskHeadSet] using h

end Erdos1017.MultipartiteDust

namespace Erdos1017.MultipartiteCountableDual

/-- Zero extension has the original finite objective on every larger prefix,
regardless of the masses assigned to the unused added heads. -/
theorem objective_restrict_extendZero_of_le {m : ℕ} (C : MultipartiteDust.Coefficients m)
    (p : ℕ → ℝ) (s : ℝ) (N : ℕ) (hmN : m ≤ N) :
    MultipartiteDust.objective (fun i : Fin N => p i.val) s (restrict N (extendZero C)) =
      MultipartiteDust.objective (fun i : Fin m => p i.val) s C := by
  induction N, hmN using Nat.le_induction with
  | base => rw [restrict_extendZero]
  | @succ N hmN ih =>
    rw [restrict_extendZero_succ C N hmN, MultipartiteDust.insertHead_objective]
    convert ih using 1
    congr 1
    funext i
    simp [Fin.removeNth]

/-- Ignoring all remaining heads embeds every actual finite optimum in the
countable feasible problem. -/
theorem finite_value_le_value (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) (n : ℕ) :
    MultipartiteDust.value (fun i : Fin n => p i.val) s ≤ value p s := by
  obtain ⟨C, hC, heq⟩ := MultipartiteDust.exists_value_eq (fun i : Fin n => p i.val) s
  have h := le_csSup
    ((feasible_isCompact.image_of_continuousOn
      ((objective_continuousOn p hp hsum s).mono Set.inter_subset_left)).bddAbove)
    (show objective p s (extendZero C) ∈ objective p s '' feasible from
      ⟨extendZero C, extendZero_feasible hC, rfl⟩)
  rw [objective_extendZero, ← heq] at h
  exact h

/-- A finite dual can be placed on any injection of its positive-mass heads.
Zero-mass heads are first ignored, so they consume no target head slots. -/
theorem finite_objective_le_value_of_positive_embedding
    (p q : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hqsum : Summable q) (s : ℝ)
    (f : {i // 0 < p i} → ℕ) (hf : Function.Injective f)
    (hmass : ∀ i, q (f i) = p i)
    (m : ℕ) {C : MultipartiteDust.Coefficients m} (hC : C ∈ MultipartiteDust.feasible m) :
    MultipartiteDust.objective (fun i : Fin m => p i.val) s C ≤ value q s := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i => 0 < p i.val)
  let g : S → ℕ := fun i => f ⟨i.val.val, (Finset.mem_filter.mp i.2).2⟩
  let N := m + Finset.univ.sup g + 1
  have hmN : m ≤ N := by dsimp [N]; omega
  have hgN (i : S) : g i < N := by
    have h := Finset.le_sup (f := g) (Finset.mem_univ i)
    change g i < m + Finset.univ.sup g + 1
    omega
  let a : S → Fin N := fun i => i.val.castLE hmN
  let b : S → Fin N := fun i => ⟨g i, hgN i⟩
  have ha : Function.Injective a := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    change i.val.castLE hmN = j.val.castLE hmN at hij
    exact congrArg (fun k : Fin N => k.val) hij
  have hb : Function.Injective b := by
    intro i j hij
    have heq := hf (congrArg Fin.val hij)
    apply Subtype.ext
    exact Fin.ext (congrArg Subtype.val heq)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  let w : ℕ → ℝ := fun i => if hi : i < N then q (σ ⟨i, hi⟩).val else 0
  let E := MultipartiteDust.maskHeadSet S C
  let F := restrict N (extendZero E)
  have hE : E ∈ MultipartiteDust.feasible m := MultipartiteDust.maskHeadSet_feasible S hC
  have hF : F ∈ MultipartiteDust.feasible N :=
    restrict_mem_feasible (extendZero_feasible hE) N
  have hmask : (fun i : Fin m => if i ∈ S then w i.val else 0) =
      fun i : Fin m => p i.val := by
    funext i
    by_cases hi : i ∈ S
    · have hiN : i.val < N := i.isLt.trans_le hmN
      simp only [hi, ↓reduceIte, w, hiN, ↓reduceDIte]
      have heq := hσ ⟨i, hi⟩
      change σ ⟨i.val, hiN⟩ = b ⟨i, hi⟩ at heq
      rw [heq]
      exact hmass ⟨i.val, (Finset.mem_filter.mp hi).2⟩
    · have hi' : ¬ 0 < p i.val := by simpa [S] using hi
      simp only [hi, ↓reduceIte]
      exact (le_antisymm (le_of_not_gt hi') (hp i.val)).symm
  have hobj : MultipartiteDust.objective (fun i : Fin N => q i.val) s
      (MultipartiteDust.reindexHead σ.symm F) =
        MultipartiteDust.objective (fun i : Fin m => p i.val) s C := by
    rw [MultipartiteDust.reindexHead_objective]
    have hw : (fun i : Fin N => q (σ.symm.symm i).val) = fun i : Fin N => w i.val := by
      funext i
      simp [w, i.isLt]
    rw [hw]
    change MultipartiteDust.objective (fun i : Fin N => w i.val) s
      (restrict N (extendZero E)) = _
    rw [objective_restrict_extendZero_of_le E w s N hmN]
    rw [MultipartiteDust.maskHeadSet_objective, hmask]
  rw [← hobj]
  exact (MultipartiteDust.objective_le_value _ _ _
    (MultipartiteDust.reindexHead_feasible σ.symm F hF)).trans
      (finite_value_le_value q hq hqsum s N)

/-- Injectively relabeling all positive heads preserves every feasible
countable objective as a lower bound for the target optimum. -/
theorem value_le_of_positive_embedding
    (p q : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (hq : ∀ i, 0 ≤ q i) (hqsum : Summable q) (s : ℝ)
    (f : {i // 0 < p i} → ℕ) (hf : Function.Injective f)
    (hmass : ∀ i, q (f i) = p i) : value p s ≤ value q s := by
  obtain ⟨D, hD, hval⟩ := exists_value_eq p hp hsum s
  rw [hval]
  apply le_of_tendsto (objective_restrict_tendsto p hp hsum s hD.1)
  exact Eventually.of_forall (fun m =>
    finite_objective_le_value_of_positive_embedding p q hp hq hqsum s f hf hmass m
      (restrict_mem_feasible hD m))

/-- A mass-preserving equivalence of positive supports leaves the actual
countable coefficient optimum unchanged. Arbitrarily placed zero heads
need not be matched. -/
theorem value_eq_of_positive_equiv
    (p q : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : Summable p)
    (hq : ∀ i, 0 ≤ q i) (hqsum : Summable q) (s : ℝ)
    (e : {i // 0 < p i} ≃ {i // 0 < q i})
    (hmass : ∀ i, q (e i) = p i) : value p s = value q s := by
  apply le_antisymm
  · exact value_le_of_positive_embedding p q hp hsum hq hqsum s
      (fun i => (e i).val) (Subtype.val_injective.comp e.injective) hmass
  · apply value_le_of_positive_embedding q p hq hqsum hp hsum s
      (fun i => (e.symm i).val) (Subtype.val_injective.comp e.symm.injective)
    intro i
    simpa using (hmass (e.symm i)).symm

/-- Sorting the positive support preserves the attained coefficient value,
including sequences with both infinitely many positive heads and zero heads. -/
theorem value_sortedHeads (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (s : ℝ) :
    value p s = value (MultipartiteProfiles.sortedHeads p) s := by
  exact value_eq_of_positive_equiv p (MultipartiteProfiles.sortedHeads p) hp hsum
    (MultipartiteProfiles.sortedHeads_nonneg p) (MultipartiteProfiles.sortedHeads_summable hsum)
    s (MultipartiteProfiles.positiveHeadEquiv hsum)
    (MultipartiteProfiles.positiveHeadEquiv_mass hsum)

/-- The sorted representative has exactly the original countable coefficient
value, expressed as the continuous value on the compact profile space. -/
theorem value_eq_sortedProfile_limit {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p) {s L : ℝ} (hs : 0 ≤ s)
    (hL : s + (∑' i, p i) ≤ L) (hQ : (∑' i, (p i) ^ 2) ≤ 1) :
    value p s = MultipartiteProfiles.limitValue (MultipartiteProfiles.sortedProfile p s) := by
  have hx := MultipartiteProfiles.sortedProfile_mem_space hp hp1 hsum hs hL hQ
  have hdust := (MultipartiteProfiles.sortedProfile_dust_and_square hp hp1 hsum hs hL hQ).1
  calc
    value p s = value (MultipartiteProfiles.sortedHeads p) s := value_sortedHeads p hp hsum s
    _ = value (MultipartiteProfiles.sortedProfile p s).2
        (MultipartiteProfiles.dust (MultipartiteProfiles.sortedProfile p s)) :=
      congrArg (fun r => value (MultipartiteProfiles.sortedHeads p) r) hdust.symm
    _ = MultipartiteProfiles.limitValue (MultipartiteProfiles.sortedProfile p s) :=
      value_eq_profile_limit hx

end Erdos1017.MultipartiteCountableDual

namespace Erdos1017.MultipartiteProfiles

/-- Every normalized summable competitor has a sorted representative with
identical total mass, dust, square moment and actual coefficient value. -/
theorem exists_sorted_representative
    (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p)
    (s : ℝ) (hs : 0 ≤ s) (L : ℝ) (hL : s + (∑' i, p i) ≤ L)
    (hQ : (∑' i, (p i) ^ 2) ≤ 1) :
    ∃ x ∈ space L, x.1 = s + (∑' i, p i) ∧ dust x = s ∧
      (∑' i, (x.2 i) ^ 2) = (∑' i, (p i) ^ 2) ∧
      MultipartiteCountableDual.value p s = limitValue x := by
  obtain ⟨hdust, hsquare⟩ := sortedProfile_dust_and_square hp hp1 hsum hs hL hQ
  exact ⟨sortedProfile p s, sortedProfile_mem_space hp hp1 hsum hs hL hQ, rfl,
    hdust, hsquare, MultipartiteCountableDual.value_eq_sortedProfile_limit hp hp1 hsum hs hL hQ⟩

end Erdos1017.MultipartiteProfiles
