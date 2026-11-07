module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateChecker

/-!
# Composition of the large-atom cover from checked pieces

Each generated leaf piece states `cover d B = true` for one explicit dyadic box
and is proved by `coverC_sound` from bounded kernel evaluation of `coverC` on a
literal copy of the shape of the box's subtree, which runs the leaf test only at
the leaves of that subtree; each generated internal piece combines the two
explicit children of a box by `cover_of_split`, whose child boxes are checked
against `IBox.split` by definitional unfolding.
-/

@[expose] public section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

/-- Both closed halves close the box one level deeper. -/
theorem cover_of_split {n : ℕ} {B : IBox} (h1 : cover n B.split.1 = true)
    (h2 : cover n B.split.2 = true) : cover (n + 1) B = true := by
  rw [cover, h1, h2]
  simp

/-- The shape of a subtree of the cover: a leaf box, or a box split into its two halves. -/
inductive Cert where
  | leaf
  | node (l r : Cert)

/-- `cover` along the shape `c`: the leaf test runs only at the leaves of `c`, and every
other box is split. The depth `n` is fuel, as in `cover`. -/
def coverC : Cert → ℕ → IBox → Bool
  | .leaf, _, B => leafOK B
  | .node _ _, 0, _ => false
  | .node l r, n + 1, B => coverC l n B.split.1 && coverC r n B.split.2

/-- A shape that closes a box proves its cover. -/
theorem coverC_sound {c : Cert} {n : ℕ} {B : IBox} (h : coverC c n B = true) :
    cover n B = true := by
  induction c generalizing n B with
  | leaf => cases n <;> simp_all [coverC, cover]
  | node l r ihl ihr =>
    cases n with
    | zero => simp [coverC] at h
    | succ n =>
      rw [coverC, Bool.and_eq_true] at h
      exact cover_of_split (ihl h.1) (ihr h.2)

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
