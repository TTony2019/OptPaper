import Mathlib.Tactic

/-! Closed convexity lemma of Sahu--Xu--Yao. -/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem squared_distance_constraint_isClosed_convex {C : Set H} (hClosed : IsClosed C)
    (hConvex : Convex ℝ C) (x y z : H) (a : ℝ) :
    IsClosed {v ∈ C | ‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a} ∧
      Convex ℝ {v ∈ C | ‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a} := by
  let w : H := (2 : ℝ) • (x - y) - z
  let b : ℝ := ‖x‖ ^ 2 - ‖y‖ ^ 2 + a
  let D : Set H := {v | inner ℝ w v ≤ b}
  have hconstraint : ∀ v : H,
      (‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a) ↔ v ∈ D := by
    intro v
    dsimp [D, w, b]
    rw [norm_sub_sq_real y v, norm_sub_sq_real x v]
    simp only [inner_sub_left, real_inner_smul_left]
    constructor <;> intro hv <;> linarith
  have hD_closed : IsClosed D := by
    dsimp [D]
    exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hD_convex : Convex ℝ D := by
    dsimp [D]
    simpa [Set.preimage, innerSL_apply_apply] using
      (convex_Iic b).is_linear_preimage (innerSL ℝ w).isLinear
  have htarget : {v ∈ C | ‖y - v‖ ^ 2 ≤ ‖x - v‖ ^ 2 + inner ℝ z v + a} = C ∩ D := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    exact and_congr Iff.rfl (hconstraint v)
  rw [htarget]
  exact ⟨hClosed.inter hD_closed, hConvex.inter hD_convex⟩
