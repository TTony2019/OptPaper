import Mathlib
import Foundation.SetValued.Yosida
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_5

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- For maximal monotone operators `A`, `B` and `λ, ρ > 0`,
  `d_{λ,ρ}(A,B) = λ sup_{u ∈ B(0,ρ)} ‖A_λ u - B_λ u‖`.  The Yosida maps are
  expressed through their canonical Foundation resolvent representatives.
  Supplied canonically by Foundation as `SetValuedOperator.resolventDistance`
  (defined in `Foundation/SetValued/Yosida.lean`). -/
recall SetValuedOperator.resolventDistance

/-- The paper's `d_{λ,ρ}`, supplied canonically by Foundation. -/
noncomputable abbrev def_7 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (_hρ : 0 < ρ) : ℝ :=
  SetValuedOperator.resolventDistance A B hA hB lam ρ hlam _hρ

/-- The resolvent form in the paper's defining display,
  `d_{λ,ρ}(A,B) = sup_{u ∈ B(0,ρ)} ‖J_λ^A u - J_λ^B u‖`.  Supplied canonically
  by Foundation as `SetValuedOperator.resolventDistance_eq_resolvent_sup`. -/
theorem def_7_resolvent_equivalence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    SetValuedOperator.resolventDistance A B hA hB lam ρ hlam hρ =
      sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧
        q = ‖SetValuedOperator.resolventMap A hA lam hlam u -
          SetValuedOperator.resolventMap B hB lam hlam u‖} :=
  SetValuedOperator.resolventDistance_eq_resolvent_sup A B hA hB lam ρ hlam hρ

/-- The Yosida form is definitionally the value of `d_{λ,ρ}`.  Supplied
  canonically by Foundation as `SetValuedOperator.resolventDistance_eq_yosida_sup`. -/
theorem def_7_yosida_equivalence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A B : SetValuedOperator H H)
    (hA : A.IsMaximalMonotone) (hB : B.IsMaximalMonotone)
    (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) :
    SetValuedOperator.resolventDistance A B hA hB lam ρ hlam hρ =
      lam * sSup {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧
        q = ‖(lam⁻¹ • (u - SetValuedOperator.resolventMap A hA lam hlam u)) -
          (lam⁻¹ • (u - SetValuedOperator.resolventMap B hB lam hlam u))‖} := rfl

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
