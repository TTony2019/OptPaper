import Mathlib.Tactic
import Foundation.SetValued.Resolvent
import Foundation.FixedPoint.Nonexpansive

/-!
# Resolvent and solution set

The paper uses the resolvent `J_λ^A = (I + λA)⁻¹` of a maximal monotone
operator and the zero set `S = A⁻¹({0})`.
-/

open SetValuedOperator
open scoped Pointwise

recall SetValuedOperator.inverse
recall SetValuedOperator.zeros
recall SetValuedOperator.resolvent
recall SetValuedOperator.IsAtMostSingleValued

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The solution set `S := A⁻¹({0})` is the zero set of `A`. -/
def solutionSet (A : SetValuedOperator H H) : Set H :=
  SetValuedOperator.zeros A

/-- Formula (1.2): fixed points of the resolvent are exactly zeros of `A`. -/
theorem resolvent_fixed_iff_zero
    (A : SetValuedOperator H H) (_hA : SetValuedOperator.IsMaximalMonotone A)
    {lam : ℝ} (hlam : 0 < lam) (x : H) :
    x ∈ J[(lam • A)] x ↔ (0 : H) ∈ A x := by
  constructor
  · intro hx
    rw [SetValuedOperator.mem_resolvent_smul_iff] at hx
    dsimp [SetValuedOperator.identityAddScaled] at hx
    rcases hx with ⟨a, ha, hxa⟩
    have hsmul : lam • a = 0 := by
      calc
        lam • a = (x + lam • a) - x := by abel
        _ = x - x := by rw [hxa]
        _ = 0 := sub_self x
    have ha0 : a = 0 := by
      rcases smul_eq_zero.mp hsmul with hlam0 | ha0
      · exact (hlam.ne' hlam0).elim
      · exact ha0
    simpa [ha0] using ha
  · intro hzero
    rw [SetValuedOperator.mem_resolvent_smul_iff]
    dsimp [SetValuedOperator.identityAddScaled]
    exact ⟨0, hzero, by simp⟩

/-- The resolvent of a maximal monotone operator is single-valued. -/
theorem resolvent_is_at_most_single_valued
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    {lam : ℝ} (hlam : 0 < lam) :
    SetValuedOperator.IsAtMostSingleValued (J[(lam • A)]) := by
  intro x y₁ hy₁ y₂ hy₂
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hy₁ hy₂
  dsimp [SetValuedOperator.identityAddScaled] at hy₁ hy₂
  rcases hy₁ with ⟨a₁, ha₁, hx₁⟩
  rcases hy₂ with ⟨a₂, ha₂, hx₂⟩
  have hy_sub : y₁ - y₂ = lam • (a₂ - a₁) := by
    have hy₁_expr : y₁ = x - lam • a₁ := by
      calc
        y₁ = (y₁ + lam • a₁) - lam • a₁ := (add_sub_cancel_right _ _).symm
        _ = x - lam • a₁ := by rw [hx₁]
    have hy₂_expr : y₂ = x - lam • a₂ := by
      calc
        y₂ = (y₂ + lam • a₂) - lam • a₂ := (add_sub_cancel_right _ _).symm
        _ = x - lam • a₂ := by rw [hx₂]
    rw [hy₁_expr, hy₂_expr]
    calc
      (x - lam • a₁) - (x - lam • a₂) = lam • a₂ - lam • a₁ := by abel
      _ = lam • (a₂ - a₁) := by rw [smul_sub]
  have hmono : 0 ≤ inner ℝ (a₁ - a₂) (y₁ - y₂) := hA.1 a₁ ha₁ a₂ ha₂
  rw [hy_sub, real_inner_smul_right] at hmono
  have hinner : inner ℝ (a₁ - a₂) (a₂ - a₁) = -‖a₁ - a₂‖ ^ 2 := by
    have : a₂ - a₁ = -(a₁ - a₂) := by abel
    rw [this, inner_neg_right]
    simp
  rw [hinner] at hmono
  have hsq : ‖a₁ - a₂‖ ^ 2 = 0 := by
    nlinarith [hlam, sq_nonneg (‖a₁ - a₂‖)]
  have haeq : a₁ = a₂ := by
    have hnorm : ‖a₁ - a₂‖ = 0 := by
      nlinarith [norm_nonneg (a₁ - a₂), hsq]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact sub_eq_zero.mp (by simpa [haeq] using hy_sub)

/-- Any single-valued selection of the resolvent is nonexpansive. -/
theorem resolvent_selection_lipschitz
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    {lam : ℝ} (hlam : 0 < lam) (J : H → H)
    (hJ : ∀ x : H, J x ∈ J[(lam • A)] x) :
    LipschitzWith 1 J := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hxres : x ∈ SetValuedOperator.identityAddScaled A lam (J x) :=
    (SetValuedOperator.mem_resolvent_smul_iff A lam x (J x)).mp (hJ x)
  have hyres : y ∈ SetValuedOperator.identityAddScaled A lam (J y) :=
    (SetValuedOperator.mem_resolvent_smul_iff A lam y (J y)).mp (hJ y)
  dsimp [SetValuedOperator.identityAddScaled] at hxres hyres
  rcases hxres with ⟨a, ha, hxeq'⟩
  rcases hyres with ⟨b, hb, hyeq'⟩
  have hxeq : x = J x + lam • a := hxeq'.symm
  have hyeq : y = J y + lam • b := hyeq'.symm
  have hdiff : x - y = (J x - J y) + lam • (a - b) := by
    calc
      x - y = (J x + lam • a) - y := congrArg (· - y) hxeq
      _ = (J x + lam • a) - (J y + lam • b) :=
        congrArg ((J x + lam • a) - ·) hyeq
      _ = (J x - J y) + (lam • a - lam • b) := by abel
      _ = (J x - J y) + lam • (a - b) := by rw [smul_sub]
  have hfirm : ‖J x - J y‖ ^ 2 ≤ inner ℝ (J x - J y) (x - y) := by
    rw [hdiff, inner_add_right, real_inner_smul_right]
    have hmono : 0 ≤ inner ℝ (J x - J y) (a - b) := by
      have h := hA.1 a ha b hb
      rwa [real_inner_comm] at h
    have hself : inner ℝ (J x - J y) (J x - J y) = ‖J x - J y‖ ^ 2 := by
      simp
    rw [hself]
    nlinarith [mul_nonneg (le_of_lt hlam) hmono]
  have hcauchy : inner ℝ (J x - J y) (x - y) ≤ ‖J x - J y‖ * ‖x - y‖ := by
    exact real_inner_le_norm (J x - J y) (x - y)
  have hsq_le : ‖J x - J y‖ ^ 2 ≤ ‖J x - J y‖ * ‖x - y‖ := le_trans hfirm hcauchy
  have hnorm : ‖J x - J y‖ ≤ ‖x - y‖ := by
    by_cases hzero : ‖J x - J y‖ = 0
    · rw [hzero]
      exact norm_nonneg _
    · have hpos : 0 < ‖J x - J y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  simpa [dist_eq_norm, mul_comm] using hnorm

end Alvarez2004
