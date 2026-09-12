import Mathlib
import Mathlib.Tactic
import Foundation.Convex.Basic
import Foundation.Convex.Subdifferential

open scoped InnerProductSpace

namespace Nesterov1983

open ERealFunction

/-- Foundation's canonical notion of positive homogeneity. -/
recall PositivelyHomogeneous

/-! The convex subdifferential (real-valued functions via the canonical coercion to `EReal`)
is supplied canonically by Foundation; recalled here for paper-local use. -/
recall ERealFunction.subdifferential

/-- Bridge between Foundation's subdifferential and the paper's supporting-inequality form
`∀ v, F u + ⟪l, v - u⟫_ℝ ≤ F v`. -/
lemma mem_convexSubdifferential_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (u l : E) :
    l ∈ subdifferential (fun y => (F y : EReal)) u ↔
      ∀ v, F u + inner ℝ l (v - u) ≤ F v := by
  constructor <;> intro h v
  · have hv := h v
    change (⟪v - u, l⟫_ℝ : EReal) + (F u : EReal) ≤ (F v : EReal) at hv
    norm_cast at hv
    simpa [real_inner_comm, add_comm] using hv
  · change (⟪v - u, l⟫_ℝ : EReal) + (F u : EReal) ≤ (F v : EReal)
    have hreal : ⟪v - u, l⟫_ℝ + F u ≤ F v := by
      simpa [real_inner_comm, add_comm] using h v
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact hreal

end Nesterov1983
