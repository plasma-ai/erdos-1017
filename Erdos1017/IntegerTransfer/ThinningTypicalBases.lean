module

public import Erdos1017.IntegerTransfer.TransversalMoments
public import Erdos1017.IntegerTransfer.MultipartiteTypicalExtensions

/-!
# Typical bases for extension concentration

The typical original bases are those whose extension count is within a relative
tolerance of the counting prediction (`typicalBases`).
-/

@[expose] public section

noncomputable section

namespace Erdos1017.TransversalThinning

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A] {t u : ℕ}

/-- Original bases outside the deterministic regularity exception set. -/
def typicalBases (G : SimpleGraph (Fin (t + u) × A)) [DecidableRel G.Adj]
    (γ : ℝ) : Finset (Fin t → A) :=
  (MultipartiteExtension.bases G).filter (fun x =>
    |CliqueExtension.count (MultipartiteExtension.extensionRelation G) x -
      MultipartiteExtension.prediction G| < γ * MultipartiteExtension.prediction G)

end Erdos1017.TransversalThinning
