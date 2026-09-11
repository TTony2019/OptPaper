import Foundation.SetValued.Monotone
import Foundation.SetValued.MaximalMonotone

open scoped InnerProductSpace

namespace BurachikSvaiterRobustnessHPE2001

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 1: the epsilon-enlargement of a set-valued operator. -/
def epsilonEnlargement (T : SetValuedOperator H H) (ε : ℝ) (_hε : 0 ≤ ε) :
    SetValuedOperator H H :=
  fun x ↦ {v | ∀ z w, w ∈ T z → inner ℝ (w - v) (z - x) ≥ -ε}

/-- The identities and monotonicity properties of the epsilon-enlargement for nonnegative
parameters. -/
theorem epsilonEnlargement_properties (T : SetValuedOperator H H)
    (hT : T.IsMaximalMonotone) :
    epsilonEnlargement T 0 (by positivity) = T ∧
      (∀ x ε₁ ε₂ (hε₁ : 0 ≤ ε₁) (hε₁₂ : ε₁ ≤ ε₂),
        epsilonEnlargement T ε₁ hε₁ x ⊆
          epsilonEnlargement T ε₂ (le_trans hε₁ hε₁₂) x) ∧
      ∀ ε (hε : 0 ≤ ε) x, T x ⊆ epsilonEnlargement T ε hε x := by
  refine ⟨?_, ?_, ?_⟩
  · funext x
    ext v
    constructor
    · intro hv
      apply mem_of_monotonically_related_to_graph hT
      intro z w hw
      have hzero : 0 ≤ inner ℝ (w - v) (z - x) := by
        simpa [epsilonEnlargement] using hv z w hw
      calc
        0 ≤ inner ℝ (w - v) (z - x) := hzero
        _ = inner ℝ (v - w) (x - z) := by
          rw [show w - v = -(v - w) by abel, show z - x = -(x - z) by abel,
            inner_neg_neg]
    · intro hv
      change ∀ z w, w ∈ T z → -(0 : ℝ) ≤ inner ℝ (w - v) (z - x)
      intro z w hw
      simpa using hT.1 w hw v hv
  · intro x ε₁ ε₂ hε₁ hε₁₂ v hv
    change ∀ z w, w ∈ T z → -ε₂ ≤ inner ℝ (w - v) (z - x)
    intro z w hw
    have hsource : -ε₁ ≤ inner ℝ (w - v) (z - x) := by
      simpa [epsilonEnlargement] using hv z w hw
    linarith
  · intro ε hε x v hv
    change ∀ z w, w ∈ T z → -ε ≤ inner ℝ (w - v) (z - x)
    intro z w hw
    exact le_trans (neg_nonpos.mpr hε) (hT.1 w hw v hv)

end BurachikSvaiterRobustnessHPE2001
