import Mathlib.Tactic
import Foundation.SetValued.Monotone
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.thm_2
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.ext_def_1

/-!
# Remark 3
-/

open Filter
open scoped Topology

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Remark 3: summability of inertial displacements implies boundedness of `y^k`,
which realizes condition (3.3) from (3.1). -/
theorem remark_3_condition_33_from_312
    (x y eta : ℕ → H) (lam alpha : ℕ → ℝ) (xbar : H)
    (hy : ∀ k : ℕ, y k = x k + alpha k • (x k - x (k - 1)))
    (h31 : Summable fun k : ℕ ↦ lam k * ‖eta k‖)
    (h312 : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖)
    (hineq :
      ∀ k : ℕ,
        ‖x (k + 1) - xbar‖ ≤
          ‖x k - xbar‖ + alpha k * ‖x k - x (k - 1)‖ +
            lam k * ‖eta k‖)
    (hlam_nonneg : ∀ k : ℕ, 0 ≤ lam k) :
    (∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l)) ∧
      Bornology.IsBounded (Set.range y) ∧
      Summable (fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k‖) := by
  let d : ℕ → ℝ := fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ + lam k * ‖eta k‖
  have hd_summable : Summable d := Summable.add h312 h31
  let s : ℕ → ℝ := fun n : ℕ ↦ (Finset.range n).sum d
  have hd_hasSum : HasSum d (∑' k, d k) := Summable.hasSum hd_summable
  have hs_tendsto : Tendsto s atTop (𝓝 (∑' k, d k)) := by
    simpa [s, HasSum] using hd_hasSum.comp Filter.tendsto_finset_range
  let φ : ℕ → ℝ := fun k : ℕ ↦ ‖x k - xbar‖
  let ψ : ℕ → ℝ := fun k : ℕ ↦ φ k - s k
  have hpsi_nonincr : ∀ k, ψ (k + 1) ≤ ψ k := by
    intro k
    dsimp [ψ, φ, s, d]
    rw [Finset.sum_range_succ]
    linarith [hineq k]
  have hs_bddAbove : BddAbove (Set.range s) := hs_tendsto.bddAbove_range
  obtain ⟨Bu, hBu⟩ := hs_bddAbove
  have hs_le_Bu (k : ℕ) : s k ≤ Bu := hBu (Set.mem_range_self k)
  have hpsi_bdd_below : ∀ k, -Bu ≤ ψ k := by
    intro k
    dsimp [ψ, φ]
    have h_nonneg : 0 ≤ ‖x k - xbar‖ := norm_nonneg _
    linarith [hs_le_Bu k]
  have hpsi_anti : Antitone ψ := by
    exact antitone_nat_of_succ_le hpsi_nonincr
  have hpsi_bddBelow : BddBelow (Set.range ψ) := by
    refine ⟨-Bu, ?_⟩
    rintro z ⟨k, rfl⟩
    exact hpsi_bdd_below k
  set psiInf := ⨅ n, ψ n with hpsiInf_def
  have hψ_tendsto : Tendsto ψ atTop (𝓝 psiInf) := by
    simpa [psiInf] using tendsto_atTop_ciInf hpsi_anti hpsi_bddBelow
  have hφ_tendsto : Tendsto φ atTop (𝓝 (psiInf + (∑' k, d k))) := by
    have h_eq : φ = ψ + s := by
      ext k
      dsimp [ψ, φ, s]
      ring
    rw [h_eq]
    exact Filter.Tendsto.add hψ_tendsto hs_tendsto
  have h_goal1 : ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l) :=
    ⟨psiInf + (∑' k, d k), by simpa [φ] using hφ_tendsto⟩
  have hφ_bddAbove : BddAbove (Set.range φ) := hφ_tendsto.bddAbove_range
  obtain ⟨M, hM⟩ := hφ_bddAbove
  have hφk_le_M (k : ℕ) : ‖x k - xbar‖ ≤ M := hM (Set.mem_range_self k)
  have h_term_tendsto :
      Tendsto (fun k : ℕ => alpha k * ‖x k - x (k - 1)‖) atTop (𝓝 0) :=
    h312.tendsto_atTop_zero
  have h_abs_term_tendsto :
      Tendsto (fun k : ℕ => |alpha k * ‖x k - x (k - 1)‖|) atTop (𝓝 0) := by
    simpa [abs_zero] using h_term_tendsto.abs
  have h_abs_term_bdd :
      BddAbove (Set.range fun k : ℕ => |alpha k| * ‖x k - x (k - 1)‖) := by
    have htmp := h_abs_term_tendsto.bddAbove_range
    simpa [abs_mul, abs_of_nonneg (norm_nonneg _)] using htmp
  obtain ⟨B₁, hB₁⟩ := h_abs_term_bdd
  have h_alpha_term_bound (k : ℕ) : |alpha k| * ‖x k - x (k - 1)‖ ≤ B₁ :=
    hB₁ (Set.mem_range_self k)
  have hy_norm_bound (k : ℕ) : ‖y k‖ ≤ M + ‖xbar‖ + B₁ := by
    rw [hy k]
    calc
      ‖x k + alpha k • (x k - x (k - 1))‖
          ≤ ‖x k‖ + ‖alpha k • (x k - x (k - 1))‖ := norm_add_le _ _
      _ = ‖x k‖ + |alpha k| * ‖x k - x (k - 1)‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ = ‖(x k - xbar) + xbar‖ + |alpha k| * ‖x k - x (k - 1)‖ := by
        congr 1
        abel_nf
      _ ≤ ‖x k - xbar‖ + ‖xbar‖ + |alpha k| * ‖x k - x (k - 1)‖ := by
        have htri := norm_add_le (x k - xbar) xbar
        linarith
      _ ≤ M + ‖xbar‖ + B₁ := by
        linarith [hφk_le_M k, h_alpha_term_bound k]
  set C := M + ‖xbar‖ + B₁ with hC_def
  have h_range_y_bdd : Bornology.IsBounded (Set.range y) := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * C, ?_⟩
    rintro z ⟨i, rfl⟩ w ⟨j, rfl⟩
    have hdist : dist (y i) (y j) ≤ ‖y i‖ + ‖y j‖ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using norm_add_le (y i) (-y j)
    linarith [hdist, hy_norm_bound i, hy_norm_bound j]
  have h_lam_eta_nonneg (k : ℕ) : 0 ≤ lam k * ‖eta k‖ :=
    mul_nonneg (hlam_nonneg k) (norm_nonneg _)
  have h_term_nonneg (k : ℕ) : 0 ≤ lam k * ‖eta k‖ * ‖y k‖ :=
    mul_nonneg (h_lam_eta_nonneg k) (norm_nonneg _)
  have h_term_le (k : ℕ) : lam k * ‖eta k‖ * ‖y k‖ ≤ C * (lam k * ‖eta k‖) := by
    have hyC : ‖y k‖ ≤ C := hy_norm_bound k
    nlinarith [h_lam_eta_nonneg k]
  have h31_const : Summable (fun k : ℕ => C * (lam k * ‖eta k‖)) :=
    h31.mul_left C
  have h_summable_33 : Summable (fun k : ℕ => lam k * ‖eta k‖ * ‖y k‖) :=
    Summable.of_nonneg_of_le h_term_nonneg h_term_le h31_const
  exact ⟨h_goal1, h_range_y_bdd, h_summable_33⟩

end Alvarez2004
