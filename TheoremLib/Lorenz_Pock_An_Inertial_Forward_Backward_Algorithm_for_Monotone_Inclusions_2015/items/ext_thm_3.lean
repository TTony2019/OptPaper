import Mathlib
import Foundation.SetValued.Monotone
import Foundation.Hilbert.WeakTopology
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.thm_2

open Filter

namespace LorenzPock

/-! The inertial proximal-point convergence estimate of §1.2, (4)--(5), also used as the
template for the proof of Theorem 2.

The estimate is established here by reduction to the Alvarez 2004 paper (reference [1] of
this paper), whose `Alvarez2004.theorem_3_1` is the corresponding result for the inexact
inertial proximal-point recurrence; the 2001 Alvarez--Attouch reference ([2]) enters the
present paper only as the source of the same statement. -/
theorem alvarez_attouch_inertial_proximal_estimate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (T : SetValuedOperator H H)
    (α ell : ℕ → ℝ) (x y : ℕ → H)
    (hmax : SetValuedOperator.IsMaximalMonotone T)
    (hzeros : (SetValuedOperator.zeros T).Nonempty)
    (hα : ∃ αbar : ℝ, αbar < 1 / 3 ∧ ∀ k, 0 ≤ α k ∧ α k ≤ αbar)
    (hell : ∀ k, 0 < ell k) (hα_mono : Monotone α) (hell_mono : Monotone ell)
    (hinertial : ∀ k, y k = x k + α k • (x k - x (k - 1)))
    (hiteration : ∀ k, ∃ t ∈ T (x (k + 1)), y k - x (k + 1) = ell k • t)
    (hsummable : Summable (fun k ↦ α k * ‖x k - x (k - 1)‖ ^ 2)) :
    ∃ z ∈ T.zeros, Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  choose t ht_mem ht_eq using hiteration
  have hrec_eq : ∀ k : ℕ, (ell k)⁻¹ • (x (k + 1) - y k) + t k = (0 : H) := by
    intro k
    rw [show x (k + 1) - y k = -(y k - x (k + 1)) by abel,
      smul_neg, ht_eq k, smul_smul, inv_mul_cancel₀ (hell k).ne']
    simp
  let recurrence : Alvarez2004.InexactProximalRecurrence T x y t (fun _ => 0) ell α (fun _ => 1) :=
    { y_def := hinertial
      equation := hrec_eq
      inclusion := by
        intro k
        simp only [inv_one, sub_self, zero_smul, one_smul, add_zero]
        rw [← Set.image_smul]
        exact ⟨t k, ht_mem k, by simp⟩ }
  rcases hα with ⟨αbar, hαbar, hαbound⟩
  let params : Alvarez2004.ParameterAssumptions x :=
    { lam := ell
      alpha := α
      rho := fun _ => 1
      lam_lower := ⟨ell 0, hell 0, fun k => hell_mono (Nat.zero_le k)⟩
      alpha_mem := by
        intro k
        refine ⟨(hαbound k).1, ?_⟩
        linarith [(hαbound k).2, hαbar]
      alpha_upper := ⟨αbar, by linarith, fun k => (hαbound k).2⟩
      alpha_summable := hsummable
      rho_lower := ⟨1, zero_lt_one, fun _ => le_rfl⟩
      rho_upper := ⟨(3 / 2 : ℝ), by norm_num, fun _ => by norm_num⟩ }
  have hzero_sum : Summable (fun k : ℕ ↦ ell k * ‖(0 : H)‖) := by
    simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hzero_weighted : Summable (fun k : ℕ ↦ ell k * ‖(0 : H)‖ * ‖y k‖) := by
    simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  rcases Alvarez2004.theorem_3_1 T hmax x y t (fun _ => 0) ell α (fun _ => 1)
    recurrence params rfl rfl rfl hzeros hzero_sum hzero_weighted with ⟨_, hz⟩
  exact hz

end LorenzPock
