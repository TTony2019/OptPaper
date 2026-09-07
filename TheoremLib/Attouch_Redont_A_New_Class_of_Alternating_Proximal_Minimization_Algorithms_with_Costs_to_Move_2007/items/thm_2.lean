import Mathlib
import TheoremLib.Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007.items.lem_1
import TheoremLib.Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007.items.ext_def_3

/-!
# Theorem 2.5: General Convergence with δ_n Factor

When β_n and μ_n are monotone sequences, using the adjusting factor δ_n we obtain
convergence of the weighted energy and summability of weighted cost terms.

This file formalizes the finite-valued specialization (`f`, `g`, and `c` are
real-valued); the paper's extended-real-valued generality requires a separate
`EReal` development.

Depends on: algo_1 (CA2), lem_1 (Lemma 2.3), ext_def_3 (δ_n).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set
open Filter
open scoped BigOperators Topology

noncomputable def weightedEnergy {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (c : X → Y → ℝ)
    (β μ δ : ℕ → ℝ) (Mf Mg : ℝ) (x : ℕ → X) (y : ℕ → Y) : ℕ → ℝ :=
  fun n => (μ n / δ n) * (f (x n) - Mf) +
    (β n / δ n) * (g (y n) - Mg) +
    ((β n * μ n) / δ n) * c (x n) (y n)

noncomputable def weightedCost {X Y : Type*} (h : X → X → ℝ) (k : Y → Y → ℝ)
    (α β μ ν δ : ℕ → ℝ) (x : ℕ → X) (y : ℕ → Y) : ℕ → ℝ :=
  fun n => (μ n / δ n) * α n * h (x n) (x (n+1)) +
    (β n / δ n) * ν n * k (y n) (y (n+1))

private lemma betamu_div_delta_nonincreasing (β μ : ℕ → ℝ)
    (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, (β (n+1) * μ (n+1)) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
      (β n * μ n) / deltaSeq β μ β_behavior μ_behavior n := by
  intro n
  unfold deltaSeq
  have hβn : 0 < β n := hβ_pos n
  have hβn1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμn : 0 < μ n := hμ_pos n
  have hμn1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
      have hprod : β (n+1) * μ (n+1) ≤ β n * μ n := by
        calc
          β (n+1) * μ (n+1) ≤ β n * μ (n+1) :=
            mul_le_mul_of_nonneg_right (hβ_prop n) (le_of_lt hμn1)
          _ ≤ β n * μ n :=
            mul_le_mul_of_nonneg_left (hμ_prop n) (le_of_lt hβn)
      simpa using hprod
  | .nonincreasing, .nondecreasing =>
      field_simp [hμn.ne.symm, hμn1.ne.symm]
      exact hβ_prop n
  | .nondecreasing, .nonincreasing =>
      field_simp [hβn.ne.symm, hβn1.ne.symm]
      exact hμ_prop n
  | .nondecreasing, .nondecreasing =>
      field_simp [hβn.ne.symm, hβn1.ne.symm, hμn.ne.symm, hμn1.ne.symm]
      exact le_rfl

/-- Theorem 2.5: Weighted energy and cost summability. -/
theorem theorem_2_5 {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β μ ν)
    (hyp : H21toH24 X Y f g h k c α β μ ν)
    (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_prop : β_behavior.toProp (β := β))
    (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∃ inf_f inf_g L : ℝ,
      (∀ x, f x ≥ inf_f) ∧
      (∀ y, g y ≥ inf_g) ∧
      Antitone (weightedEnergy f g c (fun n => β n) (fun n => μ n)
        (deltaSeq β μ β_behavior μ_behavior) inf_f inf_g alg.x alg.y) ∧
      Tendsto (weightedEnergy f g c β μ (deltaSeq β μ β_behavior μ_behavior)
        inf_f inf_g alg.x alg.y) atTop (𝓝 L) ∧
      Summable (weightedCost h k α β μ ν (deltaSeq β μ β_behavior μ_behavior)
        alg.x alg.y) := by
  rcases hyp.f_bdd_below with ⟨inf_f, hf⟩
  rcases hyp.g_bdd_below with ⟨inf_g, hg⟩
  let delta := deltaSeq β μ β_behavior μ_behavior
  have hdelta_pos : ∀ n, 0 < delta n := by
    intro n
    dsimp [delta]
    unfold deltaSeq
    match β_behavior, μ_behavior with
    | .nonincreasing, .nonincreasing => norm_num
    | .nonincreasing, .nondecreasing => exact hyp.mu_pos n
    | .nondecreasing, .nonincreasing => exact hyp.beta_pos n
    | .nondecreasing, .nondecreasing => exact mul_pos (hyp.beta_pos n) (hyp.mu_pos n)
  have hμd : ∀ n, μ (n+1) / delta (n+1) ≤ μ n / delta n := by
    simpa [delta] using
      mu_div_delta_nonincreasing β μ β_behavior μ_behavior hyp.beta_pos hyp.mu_pos
        hβ_prop hμ_prop
  have hβd : ∀ n, β (n+1) / delta (n+1) ≤ β n / delta n := by
    simpa [delta] using
      beta_div_delta_nonincreasing β μ β_behavior μ_behavior hyp.beta_pos hyp.mu_pos
        hβ_prop hμ_prop
  have hβμd : ∀ n, (β (n+1) * μ (n+1)) / delta (n+1) ≤
      (β n * μ n) / delta n := by
    simpa [delta] using
      betamu_div_delta_nonincreasing β μ β_behavior μ_behavior hyp.beta_pos hyp.mu_pos
        hβ_prop hμ_prop
  let E := weightedEnergy f g c β μ delta inf_f inf_g alg.x alg.y
  let W := weightedCost h k α β μ ν delta alg.x alg.y
  have hE_nonneg : ∀ n, 0 ≤ E n := by
    intro n
    have hf_n : 0 ≤ f (alg.x n) - inf_f := sub_nonneg.mpr (hf _)
    have hg_n : 0 ≤ g (alg.y n) - inf_g := sub_nonneg.mpr (hg _)
    have hc_n : 0 ≤ c (alg.x n) (alg.y n) := hyp.c_nonneg _ _
    have hμd_n : 0 ≤ μ n / delta n := div_nonneg (le_of_lt (hyp.mu_pos n))
      (le_of_lt (hdelta_pos n))
    have hβd_n : 0 ≤ β n / delta n := div_nonneg (le_of_lt (hyp.beta_pos n))
      (le_of_lt (hdelta_pos n))
    have hβμd_n : 0 ≤ (β n * μ n) / delta n := div_nonneg
      (mul_nonneg (le_of_lt (hyp.beta_pos n)) (le_of_lt (hyp.mu_pos n)))
      (le_of_lt (hdelta_pos n))
    dsimp [E, weightedEnergy]
    exact add_nonneg (add_nonneg (mul_nonneg hμd_n hf_n) (mul_nonneg hβd_n hg_n))
      (mul_nonneg hβμd_n hc_n)
  have hW_nonneg : ∀ n, 0 ≤ W n := by
    intro n
    have hμd_n : 0 ≤ μ n / delta n := div_nonneg (le_of_lt (hyp.mu_pos n))
      (le_of_lt (hdelta_pos n))
    have hβd_n : 0 ≤ β n / delta n := div_nonneg (le_of_lt (hyp.beta_pos n))
      (le_of_lt (hdelta_pos n))
    have ha_n : 0 ≤ α n := hyp.alpha_nonneg n
    have hv_n : 0 ≤ ν n := hyp.nu_nonneg n
    have hh_n : 0 ≤ h (alg.x n) (alg.x (n+1)) := hyp.h_nonneg _ _
    have hk_n : 0 ≤ k (alg.y n) (alg.y (n+1)) := hyp.k_nonneg _ _
    dsimp [W, weightedCost]
    exact add_nonneg (mul_nonneg (mul_nonneg hμd_n ha_n) hh_n)
      (mul_nonneg (mul_nonneg hβd_n hv_n) hk_n)
  have hE_step : ∀ n, E (n+1) + W n ≤ E n := by
    intro n
    have hraw := lemma_2_3 alg hyp n
    have hscaled := div_le_div_of_nonneg_right hraw (le_of_lt (hdelta_pos n))
    have hscaled' :
        (μ n / delta n) * f (alg.x (n+1)) +
          (β n / delta n) * g (alg.y (n+1)) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) +
          (μ n / delta n) * α n * h (alg.x n) (alg.x (n+1)) +
          (β n / delta n) * ν n * k (alg.y n) (alg.y (n+1)) ≤
        (μ n / delta n) * f (alg.x n) +
          (β n / delta n) * g (alg.y n) +
          ((β n * μ n) / delta n) * c (alg.x n) (alg.y n) := by
      calc
        _ = (μ n * f (alg.x (n+1)) + β n * g (alg.y (n+1)) +
            β n * μ n * c (alg.x (n+1)) (alg.y (n+1)) +
            μ n * α n * h (alg.x n) (alg.x (n+1)) +
            β n * ν n * k (alg.y n) (alg.y (n+1))) / delta n := by
              field_simp [ne_of_gt (hdelta_pos n)]
        _ ≤ (μ n * f (alg.x n) + β n * g (alg.y n) +
            β n * μ n * c (alg.x n) (alg.y n)) / delta n := hscaled
        _ = _ := by
              field_simp [ne_of_gt (hdelta_pos n)]
    have hshift :
        (μ n / delta n) * (f (alg.x (n+1)) - inf_f) +
          (β n / delta n) * (g (alg.y (n+1)) - inf_g) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) + W n ≤
        E n := by
      dsimp [E, W, weightedEnergy, weightedCost]
      calc
        _ = ((μ n / delta n) * f (alg.x (n+1)) +
            (β n / delta n) * g (alg.y (n+1)) +
            ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) +
            (μ n / delta n) * α n * h (alg.x n) (alg.x (n+1)) +
            (β n / delta n) * ν n * k (alg.y n) (alg.y (n+1))) -
            ((μ n / delta n) * inf_f + (β n / delta n) * inf_g) := by ring
        _ ≤ ((μ n / delta n) * f (alg.x n) +
            (β n / delta n) * g (alg.y n) +
            ((β n * μ n) / delta n) * c (alg.x n) (alg.y n)) -
            ((μ n / delta n) * inf_f + (β n / delta n) * inf_g) := by
              exact sub_le_sub_right hscaled' _
        _ = E n := by
              simp [E, weightedEnergy] <;> ring
    have hcoef : E (n+1) ≤
        (μ n / delta n) * (f (alg.x (n+1)) - inf_f) +
          (β n / delta n) * (g (alg.y (n+1)) - inf_g) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) := by
      have hf_n1 : 0 ≤ f (alg.x (n+1)) - inf_f := sub_nonneg.mpr (hf _)
      have hg_n1 : 0 ≤ g (alg.y (n+1)) - inf_g := sub_nonneg.mpr (hg _)
      have hc_n1 : 0 ≤ c (alg.x (n+1)) (alg.y (n+1)) := hyp.c_nonneg _ _
      have h1 := mul_le_mul_of_nonneg_right (hμd n) hf_n1
      have h2 := mul_le_mul_of_nonneg_right (hβd n) hg_n1
      have h3 := mul_le_mul_of_nonneg_right (hβμd n) hc_n1
      dsimp [E, weightedEnergy]
      nlinarith
    have hcoefW := add_le_add_left hcoef (W n)
    have hcoefW' : E (n+1) + W n ≤
        (μ n / delta n) * (f (alg.x (n+1)) - inf_f) +
          (β n / delta n) * (g (alg.y (n+1)) - inf_g) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) + W n := by
      nlinarith
    exact le_trans hcoefW' hshift
  have hE_succ : ∀ n, E (n+1) ≤ E n := by
    intro n
    exact le_trans (le_add_of_nonneg_right (hW_nonneg n)) (hE_step n)
  have hE_antitone : Antitone E := antitone_nat_of_succ_le hE_succ
  have hE_bdd : BddBelow (Set.range E) := by
    refine ⟨0, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hE_nonneg n
  let L : ℝ := ⨅ n, E n
  have hE_tendsto : Tendsto E atTop (𝓝 L) := by
    dsimp [L]
    exact tendsto_atTop_ciInf hE_antitone hE_bdd
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, W n
  have hS_mono : Monotone S := by
    refine monotone_nat_of_le_succ ?_
    intro N
    dsimp [S]
    rw [Finset.sum_range_succ]
    linarith [hW_nonneg N]
  have hS_tel : ∀ N, S N ≤ E 0 - E N := by
    intro N
    induction N with
    | zero => simp [S]
    | succ N ih =>
        rw [show S (N+1) = S N + W N by simp [S, Finset.sum_range_succ]]
        have htel := hE_step N
        have hdrop : W N ≤ E N - E (N+1) := by linarith
        calc
          S N + W N ≤ (E 0 - E N) + (E N - E (N+1)) := add_le_add ih hdrop
          _ = E 0 - E (N+1) := by ring
  have hS_bound : ∀ N, S N ≤ E 0 := by
    intro N
    have htel := hS_tel N
    linarith [hE_nonneg N]
  have hS_bdd : BddAbove (Set.range S) := by
    refine ⟨E 0, ?_⟩
    rintro z ⟨N, rfl⟩
    exact hS_bound N
  have hS_tendsto : Tendsto S atTop (𝓝 (⨆ N, S N)) :=
    tendsto_atTop_ciSup hS_mono hS_bdd
  have hW_sum : Summable W := by
    refine ⟨⨆ N, S N, ?_⟩
    exact (hasSum_iff_tendsto_nat_of_nonneg (fun n => hW_nonneg n) _).2 hS_tendsto
  exact ⟨inf_f, inf_g, L, hf, hg, hE_antitone, hE_tendsto, hW_sum⟩
