import Mathlib.Analysis.InnerProductSpace.Basic
import Foundation.SetValued.MaximalMonotone

/-!
# Enlargement of a set-valued operator

The epsilon-enlargement of a set-valued operator on a real Hilbert space. The
parameter is allowed to be any real number; applications that require a
nonnegative parameter carry that hypothesis separately.
-/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The epsilon-enlargement of a set-valued operator `T`. -/
def enlargement
    (T : SetValuedOperator H H)
    (ε : ℝ) : SetValuedOperator H H :=
  fun x ↦ {v | ∀ y, ∀ u ∈ T y,
    -ε ≤ ⟪u - v, y - x⟫_ℝ}

/-- Membership in an enlargement, in a form suitable for rewriting. -/
@[simp] theorem mem_enlargement_iff (T : SetValuedOperator H H) (ε : ℝ) (x v : H) :
    v ∈ enlargement T ε x ↔ ∀ y, ∀ u ∈ T y, -ε ≤ ⟪u - v, y - x⟫_ℝ :=
  Iff.rfl

/-- Enlargements are monotone with respect to their real parameter. -/
theorem enlargement_monotone (T : SetValuedOperator H H) {ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂) (x : H) : enlargement T ε₁ x ⊆ enlargement T ε₂ x := by
  intro v hv y u hu
  exact (neg_le_neg hε).trans (hv y u hu)

/-- A graph point of a monotone operator belongs to every nonnegative enlargement. -/
theorem subset_enlargement_of_monotone {T : SetValuedOperator H H}
    (hT : T.IsMonotone) {ε : ℝ} (hε : 0 ≤ ε) (x : H) :
    T x ⊆ enlargement T ε x := by
  intro v hv y u hu
  exact (neg_nonpos.mpr hε).trans (hT u hu v hv)

/-- The zero-enlargement of a maximal monotone operator is the operator itself. -/
theorem enlargement_zero_eq {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) : enlargement T 0 = T := by
  funext x
  ext v
  constructor
  · intro hv
    apply mem_of_monotonically_related_to_graph hT
    intro y u hu
    have h := hv y u hu
    have heq : inner ℝ (u - v) (y - x) = inner ℝ (v - u) (x - y) := by
      rw [show u - v = -(v - u) by abel, show y - x = -(x - y) by abel,
        inner_neg_neg]
    simpa [heq] using h
  · intro hv
    exact subset_enlargement_of_monotone hT.1 le_rfl x hv

/-- The zero-enlargement of a maximal monotone operator is contained in the operator. -/
theorem enlargement_zero_subset_of_maximal {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) {x v : H} (hv : v ∈ enlargement T 0 x) : v ∈ T x := by
  rw [enlargement_zero_eq hT] at hv
  exact hv
