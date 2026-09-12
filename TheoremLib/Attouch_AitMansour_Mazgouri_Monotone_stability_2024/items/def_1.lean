import Mathlib
import Foundation.Operator.Linear
import Foundation.FixedPoint.Nonexpansive

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-! Item `def_1`: monotonicity and Lipschitz notions for single-valued maps.
  All notions are supplied canonically by Foundation
  (`Foundation.FixedPoint.Nonexpansive`); this file recalls them.  The paper's
  `IsLipschitzContinuous A L` is mathlib's `LipschitzWith (Real.toNNReal L) A`
  (the paper assumes `L > 0`; a negative `L` is folded to `0` by `toNNReal`).
  The paper's `IsContraction` — Definition 2.1 declares *every 1-Lipschitz
  operator* to be a contraction, i.e. the constant satisfies `c ≤ 1` — is
  `ext_def_5` of this development, which keeps the real constant but asks for
  the strict `c < 1` needed by the Lim-lemma family (`ext_thm_1`, `ext_thm_2`,
  whose `λ ∈ [0,1)`).  Mathlib's `ContractingWith` is the strict version.
  Consumers relying on the paper's weaker reading: `cor_2` (see `ext_def_5`). -/

/-- For a linear operator, monotonicity (as recalled from Foundation's linear
  operator theory). -/
recall LinearMap.IsMonotone

/-- For a linear operator, strong monotonicity. -/
recall LinearMap.IsStronglyMonotone

/-- The paper's `IsCocoercive A β` is Foundation's
  `CocoerciveOn β Set.univ (fun x : Set.univ => A x)`. -/
recall CocoerciveOn

/-- A single-valued map `A:H→H` is monotone if `⟨Au-Av,u-v⟩ ≥ 0` for all
  `u,v∈H`.  Supplied canonically by Foundation. -/
recall IsMonotone

/-- A map `A:H→H` is `m`-strongly monotone (`m > 0`) if
  `⟨Au-Av,u-v⟩ ≥ m‖u-v‖²` for all `u,v∈H`.  Supplied canonically by Foundation. -/
recall IsStronglyMonotone

/-- The paper's `IsLipschitzContinuous A L` is mathlib's
  `LipschitzWith (Real.toNNReal L) A`; the paper's assumption `L > 0` is what
  keeps the two readings of `L` in agreement. -/
recall LipschitzWith

/-- Mathlib's strict contraction (`c < 1`); the paper's `IsContraction`
  (Definition 2.1, i.e. 1-Lipschitz, `c ≤ 1`) is `ext_def_5` instead. -/
recall ContractingWith

/-- If `A` is `m`-strongly monotone and `L`-Lipschitz, then `m ≤ L`.
  Supplied canonically by Foundation. -/
recall stronglyMonotone_lipschitz_implies_m_le_L

/-- Every `β`-cocoercive operator is `1/β`-Lipschitz continuous.
  Supplied canonically by Foundation. -/
recall cocoercive_implies_lipschitz

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
