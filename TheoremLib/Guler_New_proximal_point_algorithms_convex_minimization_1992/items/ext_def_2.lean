import Mathlib.Tactic
import Foundation.Convex.Subdifferential
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1

open scoped InnerProductSpace

open ERealFunction

/-! The convex subdifferential (real-valued functions via the canonical coercion to `EReal`)
is supplied canonically by Foundation; recalled here for paper-local use. -/
recall ERealFunction.subdifferential

/-- Bridge between Foundation's subdifferential and the paper's supporting-inequality form
`∀ z, g z ≥ g x + ⟪w, z - x⟫_ℝ`. -/
lemma mem_convexSubdifferential_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (x w : H) :
    w ∈ subdifferential (fun y => (g y : EReal)) x ↔
      ∀ z, g z ≥ g x + inner ℝ w (z - x) := by
  constructor <;> intro h z
  · have hz := h z
    change (⟪z - x, w⟫_ℝ : EReal) + (g x : EReal) ≤ (g z : EReal) at hz
    norm_cast at hz
    simpa [real_inner_comm, add_comm] using hz
  · change (⟪z - x, w⟫_ℝ : EReal) + (g x : EReal) ≤ (g z : EReal)
    have hreal : ⟪z - x, w⟫_ℝ + g x ≤ g z := by
      simpa [real_inner_comm, add_comm] using h z
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact hreal

/-- The qualification under which the paper uses the subdifferential definition. -/
def IsProperConvexFunction {H : Type*} [AddCommMonoid H] [Module ℝ H]
    (g : H → ℝ) : Prop :=
  ERealFunction.IsProper (fun z => (g z : EReal)) ∧ ConvexOn ℝ Set.univ g
