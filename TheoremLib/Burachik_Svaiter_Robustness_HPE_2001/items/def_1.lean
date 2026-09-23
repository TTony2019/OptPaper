import Foundation.SetValued.Enlargement

open scoped InnerProductSpace

namespace BurachikSvaiterRobustnessHPE2001

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

recall enlargement

/-- The identities and monotonicity properties of the epsilon-enlargement for nonnegative
parameters. -/
theorem enlargement_properties (T : SetValuedOperator H H)
    (hT : T.IsMaximalMonotone) :
    enlargement T 0 = T ∧
      (∀ x ε₁ ε₂, ε₁ ≤ ε₂ →
        enlargement T ε₁ x ⊆ enlargement T ε₂ x) ∧
      ∀ ε, 0 ≤ ε → ∀ x, T x ⊆ enlargement T ε x := by
  exact ⟨enlargement_zero_eq hT, fun x ε₁ ε₂ hε₁₂ =>
    enlargement_monotone T hε₁₂ x, fun ε hε x =>
      subset_enlargement_of_monotone hT.1 hε x⟩

end BurachikSvaiterRobustnessHPE2001
