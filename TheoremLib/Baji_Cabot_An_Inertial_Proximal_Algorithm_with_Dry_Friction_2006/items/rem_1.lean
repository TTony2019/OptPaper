import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.lem_1
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_4

/-!
# Remark 2.1
In the particular case where $A := \partial g$, conclusion (i) of Lemma 2.1 can be
slightly improved. Indeed, the subdifferential inequality yields:
$$\forall x \in H, \quad \Phi_{\partial g}(x) \geqslant g(x) - g(0) \geqslant
\sigma_{\partial g(0)}(x).$$
-/
open SetValuedOperator
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- The subdifferential of a convex function `g` at a point `x`:
`∂g(x) = {v | ∀ y, g(y) ≥ g(x) + ⟨v, y - x⟩}`. -/
def subderivative (g : H → EReal) : SetValuedOperator H H :=
  fun x => {v | ∀ y, g y ≥ g x + (inner ℝ v (y - x) : EReal)}

-- The defining subderivative inequality at `0` gives the pointwise lower bound for `PhiA`.
private theorem rem21_subderivative_phi_lower (g : H → ℝ) (x : H) :
    ((g x - g 0 : ℝ) : EReal) ≤
      PhiA (subderivative fun y => (g y : EReal)) x := by
  rw [PhiA]
  refine le_sInf ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv0 := hv (0 : H)
  have hv0' : ((g x + inner ℝ v ((0 : H) - x) : ℝ) : EReal) ≤ (g 0 : EReal) := by
    simpa [EReal.coe_add] using hv0
  have hreal : g x + inner ℝ v ((0 : H) - x) ≤ g 0 :=
    EReal.coe_le_coe_iff.mp hv0'
  have hinner : inner ℝ v ((0 : H) - x) = -inner ℝ v x := by
    simp
  rw [hinner] at hreal
  exact EReal.coe_le_coe (by linarith)

-- The defining subderivative inequality at `x` bounds the support function at `0`.
private theorem rem21_support_subderivative_zero_upper (g : H → ℝ) (x : H) :
    supportFunction ((subderivative fun y => (g y : EReal)) (0 : H)) x ≤
      ((g x - g 0 : ℝ) : EReal) := by
  rw [supportFunction]
  refine sSup_le ?_
  rintro _ ⟨z, hz, rfl⟩
  have hzx := hz x
  have hzx' : ((g 0 + inner ℝ z (x - (0 : H)) : ℝ) : EReal) ≤ (g x : EReal) := by
    simpa [EReal.coe_add] using hzx
  have hreal : g 0 + inner ℝ z (x - (0 : H)) ≤ g x :=
    EReal.coe_le_coe_iff.mp hzx'
  have hinner : inner ℝ z (x - (0 : H)) = inner ℝ z x := by
    simp
  rw [hinner] at hreal
  exact EReal.coe_le_coe (by linarith)

/-- Remark 2.1: improvement of Lemma 2.1 for A = ∂g. -/
theorem rem_2_1 (g : H → ℝ) (hg_conv : ConvexOn ℝ Set.univ g) (hg_lsc : LowerSemicontinuous g) :
    ∀ x,
      PhiA (subderivative fun y => (g y : EReal)) x ≥
        ((g x - g 0 : ℝ) : EReal) ∧
      ((g x - g 0 : ℝ) : EReal) ≥
        supportFunction ((subderivative fun y => (g y : EReal)) (0 : H)) x := by
  intro x
  constructor
  · exact rem21_subderivative_phi_lower g x
  · exact rem21_support_subderivative_zero_upper g x
