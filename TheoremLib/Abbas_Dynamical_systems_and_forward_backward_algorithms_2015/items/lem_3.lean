import Mathlib
import Foundation.FixedPoint.Nonexpansive

namespace AbbasDynamical2015

/-- Lemma 2.6: `Id - mu B` is nonexpansive for `0 < mu < 2 beta`. -/
theorem id_sub_cocoercive_nonexpansive {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (B : H → H) (beta mu : ℝ)
    (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)) (hmu : 0 < mu ∧ mu < 2 * beta) :
    LipschitzWith 1 (fun x : H ↦ x - mu • B x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hco : beta * ‖B x - B y‖ ^ 2 ≤ inner ℝ (x - y) (B x - B y) := by
    simpa using hB.ineq (⟨x, Set.mem_univ x⟩ : (Set.univ : Set H))
      (⟨y, Set.mem_univ y⟩ : (Set.univ : Set H))
  have hparam :
      mu * (mu * ‖B x - B y‖ ^ 2) ≤
        mu * ((2 * beta) * ‖B x - B y‖ ^ 2) := by
    have hq : mu * ‖B x - B y‖ ^ 2 ≤
        (2 * beta) * ‖B x - B y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hmu.2.le (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hq hmu.1.le
  have hco_mu :
      mu * (beta * ‖B x - B y‖ ^ 2) ≤
        mu * inner ℝ (x - y) (B x - B y) :=
    mul_le_mul_of_nonneg_left hco hmu.1.le
  have hrewrite :
      (x - mu • B x) - (y - mu • B y) =
        (x - y) - mu • (B x - B y) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hsq : ‖(x - mu • B x) - (y - mu • B y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    calc
      ‖(x - mu • B x) - (y - mu • B y)‖ ^ 2 =
          ‖(x - y) - mu • (B x - B y)‖ ^ 2 := by rw [hrewrite]
      _ = ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) (mu • (B x - B y)) +
          ‖mu • (B x - B y)‖ ^ 2 := by rw [norm_sub_sq_real]
      _ = ‖x - y‖ ^ 2 - 2 * mu * inner ℝ (x - y) (B x - B y) +
          mu ^ 2 * ‖B x - B y‖ ^ 2 := by
        rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hmu.1]
        ring
      _ ≤ ‖x - y‖ ^ 2 := by
        nlinarith [hparam, hco_mu]
  have hnorm : ‖(x - mu • B x) - (y - mu • B y)‖ ≤ ‖x - y‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  simpa [dist_eq_norm] using hnorm

end AbbasDynamical2015
