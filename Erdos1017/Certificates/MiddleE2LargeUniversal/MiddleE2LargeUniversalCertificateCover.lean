module

public import Erdos1017.Certificates.MiddleE2LargeUniversal.MiddleE2LargeUniversalCertificateChecker

/-!
# Composition of the large-atom cover from checked pieces

Each generated leaf piece states `cover d B = true` for one explicit dyadic box
and is proved by bounded kernel evaluation; each generated internal piece
combines the two explicit children of a box by `cover_of_split`, whose child
boxes are checked against `IBox.split` by definitional unfolding.
-/

@[expose] public section

namespace Erdos1017.MiddleE2LargeUniversal.FixedPoint

/-- Both closed halves close the box one level deeper. -/
theorem cover_of_split {n : ℕ} {B : IBox} (h1 : cover n B.split.1 = true)
    (h2 : cover n B.split.2 = true) : cover (n + 1) B = true := by
  rw [cover, h1, h2]
  simp

end Erdos1017.MiddleE2LargeUniversal.FixedPoint
