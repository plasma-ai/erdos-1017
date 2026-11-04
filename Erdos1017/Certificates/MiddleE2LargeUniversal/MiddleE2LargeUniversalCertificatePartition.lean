module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateChecker
public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalContract

/-!
# Dyadic box partition for the large-atom certificate

This module defines containment of a point in a dyadic index box (`Contains`)
and index validity (`Valid`), and proves that the root box encloses the whole
point box, that a split keeps every parent member in a child, and that valid
indices give the endpoint guards of the interval checker.
-/

@[expose] public section

noncomputable section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

private theorem seg_even_endpoint (width : ℤ) (i k : ℕ) :
    width * ((2 * i : ℕ) : ℤ) / ((2 ^ (k + 1) : ℕ) : ℤ) =
      width * (i : ℤ) / ((2 ^ k : ℕ) : ℤ) := by
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, pow_succ]
  calc
    width * (2 * (i : ℤ)) / ((2 : ℤ) ^ k * 2) =
        (width * (i : ℤ)) * 2 / ((2 : ℤ) ^ k * 2) := by congr 1; ring
    _ = _ := Int.mul_ediv_mul_of_pos_left _ _ (by decide : (0 : ℤ) < 2)

/-- The actual floored integer endpoints of two dyadic children cover
their parent, including the common endpoint and every real member. -/
theorem seg_split_cover (off width : ℤ) (i k : ℕ) {x : ℝ}
    (hx : SMem x (seg off width i k)) :
    SMem x (seg off width (2 * i) (k + 1)) ∨
      SMem x (seg off width (2 * i + 1) (k + 1)) := by
  have hlo : (seg off width (2 * i) (k + 1)).lo = (seg off width i k).lo := by
    change off + _ = off + _
    rw [seg_even_endpoint]
  have hhi : (seg off width (2 * i + 1) (k + 1)).hi = (seg off width i k).hi := by
    change off + width * (((2 * i + 1) + 1 : ℕ) : ℤ) / ((2 ^ (k + 1) : ℕ) : ℤ) = _
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega, seg_even_endpoint]
    rfl
  have hmid : (seg off width (2 * i) (k + 1)).hi =
      (seg off width (2 * i + 1) (k + 1)).lo := rfl
  rcases le_total (x * (S : ℝ)) ((seg off width (2 * i) (k + 1)).hi : ℝ) with hm | hm
  · left
    constructor
    · rw [hlo]
      exact hx.1
    · exact hm
  · right
    constructor
    · rw [← hmid]
      exact hm
    · rw [hhi]
      exact hx.2

/-- Valid dyadic indices keep both integer endpoints within the original
closed segment, even when division rounds either endpoint down. -/
theorem seg_bounds (off width : ℤ) (i k : ℕ) (hw : 0 ≤ width) (hi : i < 2 ^ k) :
    off ≤ (seg off width i k).lo ∧ (seg off width i k).hi ≤ off + width := by
  have hD : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
    exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
  have hi' : (i : ℤ) + 1 ≤ ((2 ^ k : ℕ) : ℤ) := by
    exact_mod_cast Nat.succ_le_of_lt hi
  have hlo : 0 ≤ width * (i : ℤ) / ((2 ^ k : ℕ) : ℤ) :=
    Int.ediv_nonneg (mul_nonneg hw (Int.natCast_nonneg i)) hD.le
  have hhi : width * ((i : ℤ) + 1) / ((2 ^ k : ℕ) : ℤ) ≤ width :=
    Int.ediv_le_of_le_mul hD (mul_le_mul_of_nonneg_left hi' hw)
  constructor <;> dsimp only [seg] <;> omega

private theorem child_index_lt {i k : ℕ} (hi : i < 2 ^ k) :
    2 * i < 2 ^ (k + 1) ∧ 2 * i + 1 < 2 ^ (k + 1) := by
  rw [pow_succ]
  omega

namespace IBox

/-- A literal Point is enclosed in all four scaled coordinates of a box. -/
def Contains (B : IBox) (X : Point) : Prop :=
  SMem X.q B.qI ∧ SMem X.A B.AI ∧ SMem X.b B.bI ∧ SMem X.u B.uI

/-- Every stored coordinate index is below its current dyadic depth. -/
def Valid (B : IBox) : Prop :=
  B.iq < 2 ^ B.kq ∧ B.iA < 2 ^ B.kA ∧ B.ib < 2 ^ B.kb ∧ B.iu < 2 ^ B.ku

theorem root_valid : root.Valid := by norm_num [Valid, root]

/-- Both actual children preserve all four index bounds. -/
theorem valid_split {B : IBox} (hB : B.Valid) : B.split.1.Valid ∧ B.split.2.Valid := by
  obtain ⟨hq, hA, hb, hu⟩ := hB
  obtain ⟨hql, hqr⟩ := child_index_lt hq
  obtain ⟨hAl, hAr⟩ := child_index_lt hA
  obtain ⟨hbl, hbr⟩ := child_index_lt hb
  obtain ⟨hul, hur⟩ := child_index_lt hu
  unfold split
  split_ifs
  · exact ⟨⟨hql, hA, hb, hu⟩, ⟨hqr, hA, hb, hu⟩⟩
  · exact ⟨⟨hq, hAl, hb, hu⟩, ⟨hq, hAr, hb, hu⟩⟩
  · exact ⟨⟨hq, hA, hbl, hu⟩, ⟨hq, hA, hbr, hu⟩⟩
  · exact ⟨⟨hq, hA, hb, hul⟩, ⟨hq, hA, hb, hur⟩⟩

/-- Index validity gives the original q/A endpoint guards and the
nonnegative b/u coordinate bounds needed by the interval checker. -/
theorem endpoint_bounds {B : IBox} (hB : B.Valid) :
    qOff ≤ B.qI.lo ∧ B.qI.hi ≤ qOff + qW ∧
      0 ≤ B.AI.lo ∧ B.AI.hi ≤ aOff + aW ∧
      0 ≤ B.bI.lo ∧ B.bI.hi ≤ bW ∧ 0 ≤ B.uI.lo ∧ B.uI.hi ≤ bW := by
  obtain ⟨hq, hA, hb, hu⟩ := hB
  have hqBounds := seg_bounds qOff qW B.iq B.kq (by norm_num [qW]) hq
  have hABounds := seg_bounds aOff aW B.iA B.kA (by norm_num [aW]) hA
  have hbBounds := seg_bounds 0 bW B.ib B.kb (by norm_num [bW]) hb
  have huBounds := seg_bounds 0 bW B.iu B.ku (by norm_num [bW]) hu
  refine ⟨hqBounds.1, hqBounds.2, ?_, hABounds.2, hbBounds.1, ?_, huBounds.1, ?_⟩
  · exact le_trans (by norm_num [aOff]) hABounds.1
  · simpa only [bI, zero_add] using hbBounds.2
  · simpa only [uI, zero_add] using huBounds.2

/-- Splitting the actual least-depth coordinate preserves every parent
member in at least one child, including all dyadic boundary points. -/
theorem split_cover {B : IBox} {X : Point} (hX : B.Contains X) :
    B.split.1.Contains X ∨ B.split.2.Contains X := by
  obtain ⟨hq, hA, hb, hu⟩ := hX
  unfold split
  split_ifs
  · rcases seg_split_cover qOff qW B.iq B.kq hq with h | h
    · exact Or.inl ⟨h, hA, hb, hu⟩
    · exact Or.inr ⟨h, hA, hb, hu⟩
  · rcases seg_split_cover aOff aW B.iA B.kA hA with h | h
    · exact Or.inl ⟨hq, h, hb, hu⟩
    · exact Or.inr ⟨hq, h, hb, hu⟩
  · rcases seg_split_cover 0 bW B.ib B.kb hb with h | h
    · exact Or.inl ⟨hq, hA, h, hu⟩
    · exact Or.inr ⟨hq, hA, h, hu⟩
  · rcases seg_split_cover 0 bW B.iu B.ku hu with h | h
    · exact Or.inl ⟨hq, hA, hb, h⟩
    · exact Or.inr ⟨hq, hA, hb, h⟩

/-- The concrete scaled root encloses the entire closed Point box,
including both rational q endpoints and the floor/ceiling A/b/u endpoints. -/
theorem root_contains {X : Point} (hX : X.InBox) : root.Contains X := by
  obtain ⟨hqlo, hqhi, hAlo, hAhi, hblo, hbhi, hulo, huhi⟩ := hX
  norm_num [Contains, SMem, qI, AI, bI, uI, root, seg, qOff, qW, aOff, aW, bW, S]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith only [hqlo, hqhi, hAlo, hAhi, hblo, hbhi, hulo, huhi]

end IBox

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
