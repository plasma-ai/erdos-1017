module

public import Erdos1017.Multipartite.MultipartiteProfiles
public import Mathlib.Data.Set.Card

/-!
# Sorting head sequences into the compact profile space

Heads are ordered by decreasing mass with index ties, and `sortedProfile` places
any summable normalized head sequence in the sorted compact profile space,
keeping its total mass, dust and square moment.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MultipartiteProfiles

open scoped BigOperators

/-- Larger heads precede smaller heads; original indices break equal-mass ties. -/
def headBefore (p : ℕ → ℝ) (i j : ℕ) : Prop :=
  p j < p i ∨ p i = p j ∧ i < j

theorem headBefore_irrefl (p : ℕ → ℝ) (i : ℕ) : ¬ headBefore p i i := by
  simp [headBefore]

theorem headBefore_trans (p : ℕ → ℝ) {i j k : ℕ}
    (hij : headBefore p i j) (hjk : headBefore p j k) : headBefore p i k := by
  rcases hij with hij | ⟨hij, hij'⟩ <;> rcases hjk with hjk | ⟨hjk, hjk'⟩
  · exact Or.inl (hjk.trans hij)
  · exact Or.inl (hjk ▸ hij)
  · exact Or.inl (hij ▸ hjk)
  · exact Or.inr ⟨hij.trans hjk, hij'.trans hjk'⟩

theorem headBefore_total (p : ℕ → ℝ) {i j : ℕ} (hij : i ≠ j) :
    headBefore p i j ∨ headBefore p j i := by
  rcases lt_trichotomy (p i) (p j) with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases lt_or_gt_of_ne hij with hij | hij
    · exact Or.inl (Or.inr ⟨h, hij⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hij⟩)
  · exact Or.inl (Or.inl h)

theorem headBefore_mass (p : ℕ → ℝ) {i j : ℕ} (hij : headBefore p i j) :
    p j ≤ p i := by
  rcases hij with hij | ⟨hij, _⟩
  · exact hij.le
  · exact hij.ge

/-- A positive head has only finitely many predecessors in a summable sequence. -/
theorem finite_headBefore {p : ℕ → ℝ} (hsum : Summable p) {i : ℕ} (hi : 0 < p i) :
    {j | headBefore p j i}.Finite := by
  have hfinite : {j | p i ≤ p j}.Finite := by
    simpa only [not_lt] using
      Filter.eventually_cofinite.mp (hsum.tendsto_cofinite_zero.eventually_lt_const hi)
  exact hfinite.subset (fun j hj => headBefore_mass p hj)

/-- The rank is used only on positive heads, where its predecessor set is finite. -/
def headRank (p : ℕ → ℝ) (i : ℕ) : ℕ := {j | headBefore p j i}.ncard

theorem headRank_lt {p : ℕ → ℝ} (hsum : Summable p) {i j : ℕ}
    (hj : 0 < p j) (hij : headBefore p i j) : headRank p i < headRank p j := by
  apply Set.ncard_lt_ncard (ht := finite_headBefore hsum hj)
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro k hk
    exact headBefore_trans p hk hij
  · intro heq
    have : i ∈ {k | headBefore p k i} := heq ▸ hij
    exact headBefore_irrefl p i this

theorem headRank_injective {p : ℕ → ℝ} (hsum : Summable p)
    {i j : ℕ} (hi : 0 < p i) (hj : 0 < p j) (hij : headRank p i = headRank p j) : i = j := by
  by_contra hne
  rcases headBefore_total p hne with h | h
  · exact (ne_of_lt (headRank_lt hsum hj h)) hij
  · exact (ne_of_gt (headRank_lt hsum hi h)) hij

/-- The ranks have no gaps before any positive head. -/
theorem exists_headRank {p : ℕ → ℝ} (hsum : Summable p) {i n : ℕ}
    (hi : 0 < p i) (hn : n < headRank p i) :
    ∃ j, 0 < p j ∧ headRank p j = n := by
  classical
  let S := (finite_headBefore hsum hi).toFinset
  have hS (j : ℕ) : j ∈ S ↔ headBefore p j i := by simp [S]
  have hpos (j : ℕ) (hj : j ∈ S) : 0 < p j := hi.trans_le (headBefore_mass p ((hS j).mp hj))
  have hsub : S.image (headRank p) ⊆ Finset.range (headRank p i) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (headRank_lt hsum hi ((hS j).mp hj))
  have hcard : (S.image (headRank p)).card = headRank p i := by
    rw [Finset.card_image_iff.mpr]
    · exact (Set.ncard_eq_toFinset_card _ (finite_headBefore hsum hi)).symm
    · intro j hj k hk heq
      exact headRank_injective hsum (hpos j hj) (hpos k hk) heq
  have heq : S.image (headRank p) = Finset.range (headRank p i) :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcard])
  have hnS : n ∈ S.image (headRank p) := heq.symm ▸ Finset.mem_range.mpr hn
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hnS
  exact ⟨j, hpos j hj, heq⟩

/-- Sort the positive support and place zeros only after it is exhausted. -/
def sortedHeads (p : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ i, 0 < p i ∧ headRank p i = n then p (Classical.choose h) else 0

theorem sortedHeads_headRank {p : ℕ → ℝ} (hsum : Summable p) {i : ℕ} (hi : 0 < p i) :
    sortedHeads p (headRank p i) = p i := by
  have hex : ∃ j, 0 < p j ∧ headRank p j = headRank p i := ⟨i, hi, rfl⟩
  rw [sortedHeads, dite_eq_left hex]
  have heq := headRank_injective hsum (Classical.choose_spec hex).1 hi
    (Classical.choose_spec hex).2
  rw [heq]

theorem sortedHeads_nonneg (p : ℕ → ℝ) (n : ℕ) : 0 ≤ sortedHeads p n := by
  unfold sortedHeads
  split_ifs with h
  · exact (Classical.choose_spec h).1.le
  · exact le_rfl

/-- Every positive sorted coordinate comes from a unique positive original head. -/
theorem sortedHeads_pos_iff {p : ℕ → ℝ} (hsum : Summable p) (n : ℕ) :
    0 < sortedHeads p n ↔ ∃ i, 0 < p i ∧ headRank p i = n := by
  constructor
  · intro hn
    by_contra h
    simp [sortedHeads, h] at hn
  · rintro ⟨i, hi, rfl⟩
    simpa [sortedHeads_headRank hsum hi] using hi

/-- The sorted positive support is decreasing, including the zero tail when
the original sequence has only finitely many positive entries. -/
theorem sortedHeads_antitone {p : ℕ → ℝ} (hsum : Summable p) : Antitone (sortedHeads p) := by
  intro m n hmn
  by_cases hn : 0 < sortedHeads p n
  · obtain ⟨j, hj, hjn⟩ := (sortedHeads_pos_iff hsum n).mp hn
    by_cases hmn' : m = n
    · simp [hmn']
    obtain ⟨i, hi, him⟩ := exists_headRank hsum (n := m) hj (by omega)
    rw [← him, ← hjn, sortedHeads_headRank hsum hi, sortedHeads_headRank hsum hj]
    by_cases hij : i = j
    · simp [hij]
    rcases headBefore_total p hij with h | h
    · exact headBefore_mass p h
    · have hlt := headRank_lt hsum hi h
      omega
  · have hz : sortedHeads p n = 0 := le_antisymm (le_of_not_gt hn) (sortedHeads_nonneg p n)
    rw [hz]
    exact sortedHeads_nonneg p m

/-- Sorting relabels the positive support, rather than permuting zero heads
through an infinite decreasing sequence. -/
def positiveHeadEquiv {p : ℕ → ℝ} (hsum : Summable p) :
    {i // 0 < p i} ≃ {n // 0 < sortedHeads p n} := by
  let f : {i // 0 < p i} → {n // 0 < sortedHeads p n} := fun i =>
    ⟨headRank p i, by simpa only [sortedHeads_headRank hsum i.2] using i.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Subtype.ext
    exact headRank_injective hsum i.2 j.2 (congrArg Subtype.val hij)
  · intro n
    obtain ⟨i, hi, hin⟩ := (sortedHeads_pos_iff hsum n).mp n.2
    exact ⟨⟨i, hi⟩, Subtype.ext hin⟩

theorem positiveHeadEquiv_mass {p : ℕ → ℝ} (hsum : Summable p) (i : {i // 0 < p i}) :
    sortedHeads p (positiveHeadEquiv hsum i) = p i :=
  sortedHeads_headRank hsum i.2

theorem eq_zero_of_not_pos {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) {i : ℕ}
    (hi : ¬ 0 < p i) : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i)

/-- Relabeling the positive support preserves any convergent series whose
summand vanishes at zero, including both moments used in the profile space. -/
theorem summable_sortedHeads_comp {p : ℕ → ℝ}
    (hsum : Summable p) (f : ℝ → ℝ) (hf : f 0 = 0)
    (hfsum : Summable (fun i => f (p i))) : Summable (fun n => f (sortedHeads p n)) := by
  have hsub : Summable (fun i : {i // 0 < p i} => f (p i)) := hfsum.subtype _
  have heq : (fun i : {i // 0 < p i} => f (p i)) =
      (fun i : {i // 0 < p i} => f (sortedHeads p (positiveHeadEquiv hsum i))) := by
    funext i
    rw [positiveHeadEquiv_mass]
  rw [heq] at hsub
  have hsorted : Summable (fun i : {n // 0 < sortedHeads p n} => f (sortedHeads p i)) :=
    (positiveHeadEquiv hsum).summable_iff.mp hsub
  apply (Function.Injective.summable_iff
    (g := (Subtype.val : {n // 0 < sortedHeads p n} → ℕ))
    (f := fun n => f (sortedHeads p n)) Subtype.val_injective ?_).mp hsorted
  intro n hn
  have hnot : ¬ 0 < sortedHeads p n := by simpa using hn
  rw [eq_zero_of_not_pos (sortedHeads_nonneg p) hnot, hf]

theorem tsum_sortedHeads_comp {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : Summable p) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑' n, f (sortedHeads p n)) = ∑' i, f (p i) := by
  have hpzero : Function.support (fun i => f (p i)) ⊆ {i | 0 < p i} := by
    intro i hi
    by_contra hn
    exact hi (by change f (p i) = 0; rw [eq_zero_of_not_pos hp hn, hf])
  have hqzero : Function.support (fun n => f (sortedHeads p n)) ⊆
      {n | 0 < sortedHeads p n} := by
    intro n hn
    by_contra hnot
    exact hn (by change f (sortedHeads p n) = 0
                 rw [eq_zero_of_not_pos (sortedHeads_nonneg p) hnot, hf])
  rw [← tsum_subtype_eq_of_support_subset hqzero, ← tsum_subtype_eq_of_support_subset hpzero]
  change (∑' n : {n // 0 < sortedHeads p n}, f (sortedHeads p n)) =
    ∑' i : {i // 0 < p i}, f (p i)
  calc
    (∑' n : {n // 0 < sortedHeads p n}, f (sortedHeads p n)) =
        ∑' i : {i // 0 < p i}, f (sortedHeads p (positiveHeadEquiv hsum i)) :=
      ((positiveHeadEquiv hsum).tsum_eq (fun n => f (sortedHeads p n))).symm
    _ = ∑' i : {i // 0 < p i}, f (p i) := by
      apply tsum_congr
      intro i
      rw [positiveHeadEquiv_mass]

theorem sortedHeads_summable {p : ℕ → ℝ} (hsum : Summable p) :
    Summable (sortedHeads p) :=
  summable_sortedHeads_comp hsum id rfl hsum

theorem tsum_sortedHeads {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) :
    (∑' n, sortedHeads p n) = ∑' i, p i :=
  tsum_sortedHeads_comp hp hsum id rfl

theorem tsum_sortedHeads_sq {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : Summable p) :
    (∑' n, (sortedHeads p n) ^ 2) = ∑' i, (p i) ^ 2 :=
  tsum_sortedHeads_comp hp hsum (fun x => x ^ 2) (by norm_num)

/-- Sorting retains the given total mass, with dust kept separate from heads. -/
def sortedProfile (p : ℕ → ℝ) (s : ℝ) : Profile :=
  (s + ∑' i, p i, sortedHeads p)

theorem sortedHeads_le_one {p : ℕ → ℝ} (hsum : Summable p)
    (hp : ∀ i, p i ≤ 1) (n : ℕ) : sortedHeads p n ≤ 1 := by
  by_cases hn : 0 < sortedHeads p n
  · obtain ⟨i, hi, hin⟩ := (sortedHeads_pos_iff hsum n).mp hn
    rw [← hin, sortedHeads_headRank hsum hi]
    exact hp i
  · exact (le_of_not_gt hn).trans zero_le_one

/-- Any summable normalized head sequence has a genuine representative in
the sorted compact profile space, even with infinitely many positive heads
and additional zero entries. -/
theorem sortedProfile_mem_space {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p) {s L : ℝ} (hs : 0 ≤ s)
    (hL : s + (∑' i, p i) ≤ L) (hQ : (∑' i, (p i) ^ 2) ≤ 1) :
    sortedProfile p s ∈ space L := by
  have hsq : Summable (fun i => (p i) ^ 2) := by
    apply hsum.of_nonneg_of_le (fun i => sq_nonneg _)
    intro i
    nlinarith [hp i, hp1 i]
  have hsorted := sortedHeads_summable hsum
  have hsortedSq := summable_sortedHeads_comp hsum (fun x => x ^ 2) (by norm_num) hsq
  refine ⟨⟨⟨add_nonneg hs (tsum_nonneg hp), sortedHeads_nonneg p⟩,
    ⟨hL, sortedHeads_le_one hsum hp1⟩⟩, sortedHeads_antitone hsum, ?_, ?_⟩
  · intro n
    change (∑ i ∈ Finset.range n, sortedHeads p i) ≤ s + ∑' i, p i
    have h := hsorted.sum_le_tsum (Finset.range n) (fun i _ => sortedHeads_nonneg p i)
    rw [tsum_sortedHeads hp hsum] at h
    linarith
  · intro n
    change (∑ i ∈ Finset.range n, (sortedHeads p i) ^ 2) ≤ 1
    have h := hsortedSq.sum_le_tsum (Finset.range n) (fun i _ => sq_nonneg _)
    rw [tsum_sortedHeads_sq hp hsum] at h
    exact h.trans hQ

/-- Sorting changes neither the actual dust mass nor the atomic square moment. -/
theorem sortedProfile_dust_and_square {p : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (hsum : Summable p) {s L : ℝ} (hs : 0 ≤ s)
    (hL : s + (∑' i, p i) ≤ L) (hQ : (∑' i, (p i) ^ 2) ≤ 1) :
    dust (sortedProfile p s) = s ∧
      (∑' i, ((sortedProfile p s).2 i) ^ 2) = ∑' i, (p i) ^ 2 := by
  constructor
  · rw [dust_eq_sub_tsum (sortedProfile_mem_space hp hp1 hsum hs hL hQ)]
    change s + (∑' i, p i) - (∑' i, sortedHeads p i) = s
    rw [tsum_sortedHeads hp hsum]
    ring
  · exact tsum_sortedHeads_sq hp hsum

end Erdos1017.MultipartiteProfiles
