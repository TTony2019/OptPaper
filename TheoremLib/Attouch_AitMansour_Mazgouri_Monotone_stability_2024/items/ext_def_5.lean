import Mathlib

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- A strict contraction has a common Lipschitz constant in `[0,1)`.  Mathlib's
  `ContractingWith` is the canonical form of this notion; the paper's
  real-parameter definition is preserved verbatim (its real constant is used
  directly at the paper's call sites). -/
recall ContractingWith

/-- The paper's `IsContraction` with a *real* constant, used at the paper's
  call sites (`cor_2`).

  Deliberate deviation from Definition 2.1: the paper declares *every
  1-Lipschitz* operator to be a contraction, i.e. it allows the boundary
  constant `c ≤ 1` (and its proof of Corollary 4.2 indeed only uses
  non-expansiveness).  Here the constant is required to be strictly `< 1`,
  which is what the Lim lemma family (`ext_thm_1`, `ext_thm_2`) needs with its
  `λ ∈ [0,1)`.  Consequently `cor_2`'s hypothesis is *stronger* than the
  paper's, and the boundary case `c = 1` is not covered. -/
def ext_def_5 {X : Type*} [PseudoMetricSpace X] (T : X → X) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x y, dist (T x) (T y) ≤ c * dist x y

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
