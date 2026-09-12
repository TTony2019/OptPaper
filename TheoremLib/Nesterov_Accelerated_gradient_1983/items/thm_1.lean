import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.algo_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_thm_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_thm_2

namespace Nesterov1983

/-- The number of gradient evaluations used to construct the first `n`
iterates of method (3)-(5). -/
def acceleratedGradientEvaluationCount {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (n : ℕ) : ℕ :=
  n

/-- The number of objective evaluations in the first `n` iterations: two
accepted-test values per iteration and one additional value per rejected trial. -/
def acceleratedFunctionEvaluationCount {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (n : ℕ) : ℕ :=
  2 * n + (Finset.range n).sum M.searchIndex

/-- The secant initialization is at least the reciprocal Lipschitz constant.
The nondegeneracy assumptions in the algorithm also force that constant to be
strictly positive. -/
theorem initialStep_ge_inv_L {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L : ℝ) (hC11 : IsC11 f L) (M : AcceleratedGradientMethod f) :
    0 < L ∧ 1 / L ≤ M.initialStep := by
  have hgrad : 0 < ‖gradient f M.y0 - gradient f M.z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm M.gradient_z_ne_gradient_y0))
  have hpoints : 0 < ‖M.y0 - M.z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm M.z_ne_y0))
  have hlip : ‖gradient f M.y0 - gradient f M.z‖ ≤ L * ‖M.y0 - M.z‖ := by
    simpa only [norm_sub_rev] using hC11.lipschitz M.z M.y0
  have hL : 0 < L := by nlinarith [hC11.nonneg]
  refine ⟨hL, ?_⟩
  rw [M.initialStep_eq]
  apply (div_le_div_iff₀ hL hgrad).2
  nlinarith

/-- The weights in the accelerated recurrence satisfy the usual quadratic
identity. -/
theorem weight_sq_sub_weight {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (k : ℕ) :
    M.weight (k + 1) ^ 2 - M.weight (k + 1) = M.weight k ^ 2 := by
  rw [M.update_weight]
  have hrad : 0 ≤ 4 * M.weight k ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (4 * M.weight k ^ 2 + 1) ^ 2 =
      4 * M.weight k ^ 2 + 1 := Real.sq_sqrt hrad
  nlinarith

/-- The accelerated weights grow at least linearly. -/
theorem weight_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) : ∀ k : ℕ,
    1 + (k : ℝ) / 2 ≤ M.weight k := by
  intro k
  induction k with
  | zero => simpa [M.weight_zero]
  | succ k ih =>
    rw [M.update_weight]
    have hk : 0 ≤ (k : ℝ) := by positivity
    have hw : 0 ≤ M.weight k := by linarith
    have hrad : 0 ≤ 4 * M.weight k ^ 2 + 1 := by positivity
    have hroot : 2 * M.weight k ≤ Real.sqrt (4 * M.weight k ^ 2 + 1) := by
      apply (Real.le_sqrt (by positivity) hrad).2
      nlinarith
    norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

/-- A trial step no larger than `L⁻¹` passes the line-search test. -/
theorem trial_step_accepts_of_le_invL {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L α : ℝ) (hC11 : IsC11 f L) (hL : 0 < L) (y : E)
    (hα : 0 < α) (hαL : α ≤ 1 / L) :
    (α / 2) * ‖gradient f y‖ ^ 2 ≤ f y - f (y - α • gradient f y) := by
  have hd := descent_lemma f L hC11 y (y - α • gradient f y)
  have hvec : y - α • gradient f y - y = (-α) • gradient f y := by
    calc
      y - α • gradient f y - y = -(α • gradient f y) := by abel
      _ = (-α) • gradient f y := (neg_smul α (gradient f y)).symm
  simp only [hvec, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul] at hd
  rw [norm_neg, Real.norm_eq_abs, abs_of_pos hα] at hd
  have hαL' : α * L ≤ 1 := (le_div_iff₀ hL).mp hαL
  have hnorm : 0 ≤ ‖gradient f y‖ ^ 2 := sq_nonneg _
  have haux := mul_le_mul_of_nonneg_right hαL'
    (mul_nonneg (le_of_lt hα) hnorm)
  ring_nf at hd haux ⊢
  nlinarith

/-- Every accepted dyadic step is at least half the reciprocal smoothness
constant.  The proof uses minimality of the line-search index. -/
private theorem method_step_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L : ℝ) (hC11 : IsC11 f L) (M : AcceleratedGradientMethod f) :
    ∀ k : ℕ, 1 / (2 * L) ≤ M.step k := by
  rcases initialStep_ge_inv_L f L hC11 M with ⟨hL, hinit⟩
  have hhalf_pos : 0 < 1 / (2 * L) := by positivity
  intro k
  induction k with
  | zero =>
      let previous := M.initialStep
      have hprevious : 1 / (2 * L) ≤ previous := by
        dsimp [previous]
        have : 1 / (2 * L) ≤ 1 / L := by
          field_simp
          linarith
        exact this.trans hinit
      rw [M.step_eq_dyadic_previous, if_pos rfl]
      change 1 / (2 * L) ≤ (2 : ℝ) ^ (-(M.searchIndex 0 : ℤ)) * previous
      by_cases hs : M.searchIndex 0 = 0
      · simpa [hs] using hprevious
      ·
        obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hs
        have htrial : (2 : ℝ) ^ (-(i : ℤ)) * previous =
            2 * ((2 : ℝ) ^ (-(M.searchIndex 0 : ℤ)) * previous) := by
          rw [hi]
          rw [show -((↑(i + 1) : ℤ)) = -(↑i : ℤ) - 1 by omega]
          rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring
        by_contra hnot
        push_neg at hnot
        have hprevious_pos : 0 < previous := lt_of_lt_of_le hhalf_pos hprevious
        have hβ_pos : 0 < (2 : ℝ) ^ (-(i : ℤ)) * previous := by positivity
        have hβ_le : (2 : ℝ) ^ (-(i : ℤ)) * previous ≤ 1 / L := by
          rw [htrial]
          exact le_of_lt <| calc
            2 * ((2 : ℝ) ^ (-(M.searchIndex 0 : ℤ)) * previous) <
                2 * (1 / (2 * L)) := by gcongr
            _ = 1 / L := by field_simp

        have hpass := trial_step_accepts_of_le_invL f L
          ((2 : ℝ) ^ (-(i : ℤ)) * previous) hC11 hL (M.y 0) hβ_pos hβ_le
        have hfail := M.minimal_searchIndex 0 i (by omega)
        simp only [if_pos] at hfail
        linarith
  | succ k ih =>
      let previous := M.step k
      have hprevious : 1 / (2 * L) ≤ previous := by simpa [previous] using ih
      rw [M.step_eq_dyadic_previous]
      simp only [Nat.succ_ne_zero, if_false]
      change 1 / (2 * L) ≤ (2 : ℝ) ^ (-(M.searchIndex (k + 1) : ℤ)) * previous
      by_cases hs : M.searchIndex (k + 1) = 0
      · simpa [hs] using hprevious
      · obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hs
        have htrial :
            (2 : ℝ) ^ (-(i : ℤ)) * previous =
              2 * ((2 : ℝ) ^ (-(M.searchIndex (k + 1) : ℤ)) * previous) := by
          rw [hi]
          rw [show -((↑(i + 1) : ℤ)) = -(↑i : ℤ) - 1 by omega]
          rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring
        by_contra hnot
        push_neg at hnot
        have hstep_pos : 0 < previous := lt_of_lt_of_le hhalf_pos hprevious
        have hβ_pos : 0 < (2 : ℝ) ^ (-(i : ℤ)) * previous := by positivity
        have hβ_le : (2 : ℝ) ^ (-(i : ℤ)) * previous ≤ 1 / L := by
          rw [htrial]
          exact le_of_lt <| calc
            2 * ((2 : ℝ) ^ (-(M.searchIndex (k + 1) : ℤ)) * previous) <
                2 * (1 / (2 * L)) := by gcongr
            _ = 1 / L := by field_simp
        have hpass := trial_step_accepts_of_le_invL f L
          ((2 : ℝ) ^ (-(i : ℤ)) * previous) hC11 hL (M.y (k + 1)) hβ_pos hβ_le
        have hfail := M.minimal_searchIndex (k + 1) i (by omega)
        simp only [Nat.succ_ne_zero, if_false] at hfail
        change _ < ((2 : ℝ) ^ (-(i : ℤ)) * previous) / 2 * _ at hfail
        have hfail' :
            f (M.y (k + 1)) - f (M.y (k + 1) -
                ((2 : ℝ) ^ (-(i : ℤ)) * previous) • gradient f (M.y (k + 1))) <
              ((2 : ℝ) ^ (-(i : ℤ)) * previous) / 2 * ‖gradient f (M.y (k + 1))‖ ^ 2 := by
          simpa [previous] using hfail
        linarith

/-- The line-search only halves the preceding step, so accepted steps are
nonincreasing. -/
private theorem method_step_succ_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L : ℝ) (hC11 : IsC11 f L) (M : AcceleratedGradientMethod f)
    (k : ℕ) : M.step (k + 1) ≤ M.step k := by
  have hstep_pos : 0 < M.step k := by
    have hhalf : 0 < 1 / (2 * L) := by
      rcases initialStep_ge_inv_L f L hC11 M with ⟨hL, _⟩
      positivity
    exact lt_of_lt_of_le hhalf (method_step_lower f L hC11 M k)
  rw [M.step_eq_dyadic_previous]
  simp only [Nat.succ_ne_zero, if_false]
  have hpow : 1 ≤ (2 : ℝ) ^ (M.searchIndex (k + 1) : ℤ) := by
    apply one_le_zpow₀
    · norm_num
    · exact_mod_cast Nat.zero_le (M.searchIndex (k + 1))
  have hfactor : (2 : ℝ) ^ (-(M.searchIndex (k + 1) : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    exact (inv_le_one₀ (by positivity)).2 hpow
  simpa [mul_comm] using mul_le_of_le_one_right (le_of_lt hstep_pos) hfactor

/-- The accepted step is the initial step divided by all dyadic line-search
factors used up to that iteration. -/
private theorem step_dyadic_product {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (n : ℕ) :
    M.step n = M.initialStep * (2 : ℝ) ^
      (-(((Finset.range (n + 1)).sum M.searchIndex : ℕ) : ℤ)) := by
  induction n with
  | zero =>
      rw [M.step_eq_dyadic_previous, if_pos rfl]
      simp [Finset.sum_range_succ]
      ring
  | succ n ih =>
      rw [M.step_eq_dyadic_previous, if_neg (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih]
      have hsum := Finset.sum_range_succ M.searchIndex (n + 1)
      rw [hsum, Int.natCast_add, neg_add_rev,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring

/-- The cumulative number of rejected dyadic trials is controlled by the
initial step and the smoothness constant. -/
private theorem search_sum_dyadic_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L : ℝ) (hC11 : IsC11 f L) (M : AcceleratedGradientMethod f)
    (n : ℕ) :
    (2 : ℝ) ^ (((Finset.range (n + 1)).sum M.searchIndex : ℕ) : ℤ) ≤
      2 * L * M.initialStep := by
  rcases initialStep_ge_inv_L f L hC11 M with ⟨hL, _⟩
  let S : ℤ := ↑((Finset.range (n + 1)).sum M.searchIndex)
  have hpow_pos : 0 < (2 : ℝ) ^ S := zpow_pos (by norm_num) _
  have hstep := method_step_lower f L hC11 M n
  have hcancel : M.step n * (2 : ℝ) ^ S = M.initialStep := by
    rw [step_dyadic_product]
    change (M.initialStep * (2 : ℝ) ^ (-S)) * (2 : ℝ) ^ S = M.initialStep
    rw [mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  have hscaled : (2 : ℝ) ^ S ≤ (2 * L) * (M.step n * (2 : ℝ) ^ S) := by
    have hmul := mul_le_mul_of_nonneg_right hstep (le_of_lt hpow_pos)
    have htwoL : 0 < 2 * L := by positivity
    calc
      (2 : ℝ) ^ S = (2 * L) * (1 / (2 * L) * (2 : ℝ) ^ S) := by field_simp
      _ ≤ (2 * L) * (M.step n * (2 : ℝ) ^ S) :=
        mul_le_mul_of_nonneg_left hmul (le_of_lt htwoL)
  calc
    (2 : ℝ) ^ (((Finset.range (n + 1)).sum M.searchIndex : ℕ) : ℤ) =
        (2 : ℝ) ^ S := by rfl
    _ ≤ (2 * L) * (M.step n * (2 : ℝ) ^ S) := hscaled
    _ = 2 * L * M.initialStep := by rw [hcancel]

/-- A real-valued form of the cumulative line-search bound.  This is useful
when translating rejected trials into the logarithmic evaluation estimate. -/
theorem search_sum_le_logb {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L : ℝ) (hC11 : IsC11 f L) (M : AcceleratedGradientMethod f)
    (n : ℕ) :
    (((Finset.range (n + 1)).sum M.searchIndex : ℕ) : ℝ) ≤
      Real.logb 2 (2 * L * M.initialStep) := by
  rcases initialStep_ge_inv_L f L hC11 M with ⟨hL, hinit⟩
  have hinit_pos : 0 < M.initialStep := by
    have : 0 < 1 / L := by positivity
    exact lt_of_lt_of_le this hinit
  have harg : 0 < 2 * L * M.initialStep := by positivity
  apply (Real.le_logb_iff_rpow_le (by norm_num) harg).2
  rw [Real.rpow_natCast]
  simpa only [zpow_natCast] using search_sum_dyadic_bound f L hC11 M n

/-- The momentum variable used in Nesterov's Lyapunov argument satisfies the
corresponding one-step recurrence. -/
private theorem accelerated_p_recurrence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ) :
    p (k + 1) - M.x (k + 1) = p k - M.x k +
      (M.weight (k + 1) * M.step (k + 1)) • gradient f (M.y (k + 1)) := by
  rw [hp (k + 1), hp k, M.update_x (k + 1), M.update_y k]
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  have hweight : 0 < M.weight (k + 1) := by
    have hw := weight_lower f M (k + 1)
    have hk : 0 ≤ (k : ℝ) := by positivity
    norm_num [Nat.cast_add, Nat.cast_one] at hw
    linarith
  have hne : M.weight (k + 1) ≠ 0 := ne_of_gt hweight
  apply (smul_right_injective E hne)
  simp only [smul_sub, smul_add, smul_smul]
  field_simp [hne]
  module

/-- The extrapolated point is separated from the preceding iterate by the
momentum vector divided by the next weight. -/
theorem accelerated_x_sub_y {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ) :
    M.x k - M.y (k + 1) = (M.weight (k + 1))⁻¹ • p k := by
  have hweight : 0 < M.weight (k + 1) := by
    have hw := weight_lower f M (k + 1)
    have hk : 0 ≤ (k : ℝ) := by positivity
    norm_num [Nat.cast_add, Nat.cast_one] at hw
    linarith
  have hne : M.weight (k + 1) ≠ 0 := ne_of_gt hweight
  rw [M.update_y, hp k]
  field_simp [hne]
  module

/-- Convexity at the minimizer together with acceptance of the trial step. -/
theorem accelerated_star_inequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hgrad : ∀ u, HasGradientAt f (gradient f u) u)
    (M : AcceleratedGradientMethod f) (xstar : E) (k : ℕ) :
    f (M.x (k + 1)) - f xstar + M.step (k + 1) / 2 * ‖gradient f (M.y (k + 1))‖ ^ 2 ≤
      inner ℝ (gradient f (M.y (k + 1))) (M.y (k + 1) - xstar) := by
  have hconvex := convex_firstOrder_inequality f hconv hgrad
    (M.y (k + 1)) xstar
  have haccepted := M.accepted (k + 1)
  rw [show xstar - M.y (k + 1) = -(M.y (k + 1) - xstar) by abel,
    inner_neg_right] at hconvex
  linarith

/-- The preceding-iterate form of the accepted-step inequality. -/
theorem accelerated_previous_inequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hgrad : ∀ u, HasGradientAt f (gradient f u) u)
    (M : AcceleratedGradientMethod f) (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ) :
    M.step (k + 1) / 2 * ‖gradient f (M.y (k + 1))‖ ^ 2 ≤
      f (M.x k) - f (M.x (k + 1)) -
        (M.weight (k + 1))⁻¹ * inner ℝ (gradient f (M.y (k + 1))) (p k) := by
  have hconvex := convex_firstOrder_inequality f hconv hgrad
    (M.y (k + 1)) (M.x k)
  have hxy := accelerated_x_sub_y f M p hp k
  rw [hxy, real_inner_smul_right] at hconvex
  have haccepted := M.accepted (k + 1)
  linarith

private theorem accelerated_energy_zero_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (M : AcceleratedGradientMethod f) (xstar : E)
    (hy0 : M.y 0 = M.y0)
    (hconv : ConvexOn ℝ Set.univ f) (hgrad : ∀ u, HasGradientAt f (gradient f u) u)
    (p : ℕ → E) (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) :
    2 * M.step 0 * M.weight 0 ^ 2 * (f (M.x 0) - f xstar) +
      ‖p 0 - M.x 0 + xstar‖ ^ 2 ≤ ‖M.y0 - xstar‖ ^ 2 := by
  have hconvex := convex_firstOrder_inequality f hconv hgrad M.y0 xstar
  have haccepted := M.accepted 0
  rw [M.update_x 0, hy0] at haccepted
  rw [hp 0, M.weight_zero, M.update_x 0, hy0]
  simp only [↓reduceIte, sub_self, zero_smul, zero_sub, one_pow, mul_one]
  have hnorm : ‖-(M.y0 - M.step 0 • gradient f M.y0) + xstar‖ ^ 2 =
      ‖M.y0 - xstar - M.step 0 • gradient f M.y0‖ ^ 2 := by
    rw [show -(M.y0 - M.step 0 • gradient f M.y0) + xstar =
      -(M.y0 - xstar - M.step 0 • gradient f M.y0) by abel, norm_neg]
  rw [hnorm, norm_sub_pow_two_real, real_inner_smul_right]
  rw [norm_smul, Real.norm_eq_abs]
  have hinitial : 0 < M.initialStep := by
    rw [M.initialStep_eq]
    apply div_pos
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm M.z_ne_y0))
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm M.gradient_z_ne_gradient_y0))
  have hstep : 0 < M.step 0 := by
    rw [M.step_eq_dyadic_previous, if_pos rfl]
    positivity
  rw [abs_of_pos hstep]
  rw [show xstar - M.y0 = -(M.y0 - xstar) by abel, inner_neg_right] at hconvex
  have hsymm : inner ℝ (M.y0 - xstar) (gradient f M.y0) =
      inner ℝ (gradient f M.y0) (M.y0 - xstar) := real_inner_comm _ _
  have hnorm_nonneg : 0 ≤ ‖gradient f M.y0‖ ^ 2 := sq_nonneg _
  have hbaseGap :
      f (M.y0 - M.step 0 • gradient f M.y0) - f xstar +
          M.step 0 / 2 * ‖gradient f M.y0‖ ^ 2 ≤
        inner ℝ (gradient f M.y0) (M.y0 - xstar) := by
    linarith
  have hsquare : (M.step 0 * ‖gradient f M.y0‖) ^ 2 =
      M.step 0 ^ 2 * ‖gradient f M.y0‖ ^ 2 := by ring
  rw [hsquare]
  nlinarith

private theorem accelerated_energy_succ_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ)
    (L : ℝ) (hC11 : IsC11 f L) (hconv : ConvexOn ℝ Set.univ f)
    (M : AcceleratedGradientMethod f) (xstar : E) (hmin : ∀ x, f xstar ≤ f x)
    (p : ℕ → E) (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ) :
    2 * M.step (k + 1) * M.weight (k + 1) ^ 2 *
        (f (M.x (k + 1)) - f xstar) + ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 ≤
      2 * M.step k * M.weight k ^ 2 * (f (M.x k) - f xstar) +
        ‖p k - M.x k + xstar‖ ^ 2 := by
  rcases initialStep_ge_inv_L f L hC11 M with ⟨hL, _⟩
  have hα : 0 < M.step (k + 1) := by
    have : 0 < 1 / (2 * L) := by positivity
    exact lt_of_lt_of_le this (method_step_lower f L hC11 M (k + 1))
  have ha : 0 < M.weight (k + 1) := by
    have hw := weight_lower f M (k + 1)
    have hk : 0 ≤ (k : ℝ) := by positivity
    norm_num [Nat.cast_add, Nat.cast_one] at hw
    linarith
  have hane : M.weight (k + 1) ≠ 0 := ne_of_gt ha
  have hxy := accelerated_x_sub_y f M p hp k
  have hq : p k - M.x k + xstar =
      (1 - (M.weight (k + 1))⁻¹) • p k + (xstar - M.y (k + 1)) := by
    calc
      p k - M.x k + xstar = p k - (M.x k - M.y (k + 1)) +
          (xstar - M.y (k + 1)) := by abel
      _ = p k - (M.weight (k + 1))⁻¹ • p k + (xstar - M.y (k + 1)) := by rw [hxy]
      _ = (1 - (M.weight (k + 1))⁻¹) • p k + (xstar - M.y (k + 1)) := by module
  have hinter : inner ℝ (gradient f (M.y (k + 1))) (p k - M.x k + xstar) =
      (1 - (M.weight (k + 1))⁻¹) * inner ℝ (gradient f (M.y (k + 1))) (p k) +
        inner ℝ (gradient f (M.y (k + 1))) (xstar - M.y (k + 1)) := by
    rw [hq, inner_add_right, real_inner_smul_right]
  have hrec := accelerated_p_recurrence f M p hp k
  have hnorm : ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 =
      ‖p k - M.x k + xstar‖ ^ 2 +
        2 * (M.weight (k + 1) - 1) * M.step (k + 1) *
          inner ℝ (gradient f (M.y (k + 1))) (p k) +
        2 * M.weight (k + 1) * M.step (k + 1) *
          inner ℝ (gradient f (M.y (k + 1))) (xstar - M.y (k + 1)) +
        M.weight (k + 1) ^ 2 * M.step (k + 1) ^ 2 * ‖gradient f (M.y (k + 1))‖ ^ 2 := by
    rw [show p (k + 1) - M.x (k + 1) + xstar =
        (p k - M.x k + xstar) +
          (M.weight (k + 1) * M.step (k + 1)) • gradient f (M.y (k + 1)) by
          rw [hrec]; abel]
    rw [norm_add_pow_two_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos ha hα)]
    have hs : inner ℝ (p k - M.x k + xstar) (gradient f (M.y (k + 1))) =
        inner ℝ (gradient f (M.y (k + 1))) (p k - M.x k + xstar) := real_inner_comm _ _
    rw [hs, hinter]
    field_simp [hane]
    ring
  have hstar := accelerated_star_inequality f hconv (fun u => hC11.hasGradientAt u) M xstar k
  have hprevious := accelerated_previous_inequality f hconv (fun u => hC11.hasGradientAt u) M p hp k
  have hwid := weight_sq_sub_weight f M k
  have hinv : M.weight (k + 1) * (M.weight (k + 1))⁻¹ = 1 := by field_simp
  have hcoef : 0 ≤ 2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1) := by
    rw [hwid]
    positivity
  have hpreviousMul :
      (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1) ^ 2 *
          ‖gradient f (M.y (k + 1))‖ ^ 2 ≤
        2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1) *
          ((f (M.x k) - f xstar) - (f (M.x (k + 1)) - f xstar)) -
        2 * (M.weight (k + 1) - 1) * M.step (k + 1) *
          inner ℝ (gradient f (M.y (k + 1))) (p k) := by
    calc
      (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1) ^ 2 *
          ‖gradient f (M.y (k + 1))‖ ^ 2 =
          (2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1)) *
            (M.step (k + 1) / 2 * ‖gradient f (M.y (k + 1))‖ ^ 2) := by ring
      _ ≤ (2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1)) *
            (f (M.x k) - f (M.x (k + 1)) -
              (M.weight (k + 1))⁻¹ * inner ℝ (gradient f (M.y (k + 1))) (p k)) :=
          mul_le_mul_of_nonneg_left hprevious hcoef
      _ = 2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * M.step (k + 1) *
            ((f (M.x k) - f xstar) - (f (M.x (k + 1)) - f xstar)) -
          2 * (M.weight (k + 1) - 1) * M.step (k + 1) *
            inner ℝ (gradient f (M.y (k + 1))) (p k) := by
          field_simp [hane]
          ring
  have hstar' : inner ℝ (gradient f (M.y (k + 1))) (xstar - M.y (k + 1)) ≤
      -(f (M.x (k + 1)) - f xstar) - M.step (k + 1) / 2 *
        ‖gradient f (M.y (k + 1))‖ ^ 2 := by
    rw [show xstar - M.y (k + 1) = -(M.y (k + 1) - xstar) by abel,
      inner_neg_right]
    linarith
  have hstarMul := mul_le_mul_of_nonneg_left hstar'
    (show 0 ≤ 2 * M.weight (k + 1) * M.step (k + 1) by positivity)
  have hmain :
      2 * M.step (k + 1) * M.weight (k + 1) ^ 2 *
          (f (M.x (k + 1)) - f xstar) + ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 ≤
        2 * M.step (k + 1) * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) *
          (f (M.x k) - f xstar) +
          ‖p k - M.x k + xstar‖ ^ 2 := by
    ring_nf at hnorm hpreviousMul hstarMul ⊢
    nlinarith [hnorm, hstarMul]
  have hgap : 0 ≤ f (M.x k) - f xstar := by linarith [hmin (M.x k)]
  have hstep := method_step_succ_le f L hC11 M k
  have hscale := mul_le_mul_of_nonneg_right hstep
    (mul_nonneg (sq_nonneg (M.weight k)) hgap)
  calc
    2 * M.step (k + 1) * M.weight (k + 1) ^ 2 *
        (f (M.x (k + 1)) - f xstar) + ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 ≤
      2 * M.step (k + 1) * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) *
        (f (M.x k) - f xstar) + ‖p k - M.x k + xstar‖ ^ 2 := hmain
    _ = 2 * M.step (k + 1) * M.weight k ^ 2 * (f (M.x k) - f xstar) +
        ‖p k - M.x k + xstar‖ ^ 2 := by rw [hwid]
    _ ≤ 2 * M.step k * M.weight k ^ 2 * (f (M.x k) - f xstar) +
        ‖p k - M.x k + xstar‖ ^ 2 := by nlinarith

/-- The rate and evaluation-complexity assertions of Theorem 1. -/
theorem accelerated_gradient_rate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (L : ℝ)
    (hC11 : IsC11 f L) (hconv : ConvexOn ℝ Set.univ f)
    (M : AcceleratedGradientMethod f) (xstar : E)
    (hy0 : M.y 0 = M.y0)
    (hmin : ∀ x, f xstar ≤ f x) :
    (∀ k, f (M.x k) - f xstar ≤ (4 * L * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2) ∧
    ∀ ε : ℝ, 0 < ε →
      let NG := Real.sqrt (4 * L * ‖M.y0 - xstar‖ ^ 2 / ε)
      let NF := 2 * NG + Real.logb 2 (2 * L * M.initialStep) + 1
      ∃ iterations gradientEvaluations functionEvaluations : ℕ,
        gradientEvaluations = acceleratedGradientEvaluationCount f M iterations ∧
        functionEvaluations = acceleratedFunctionEvaluationCount f M iterations ∧
        gradientEvaluations ≤ (Int.ceil NG).toNat ∧
        functionEvaluations ≤ (Int.ceil NF).toNat ∧
        f (M.x iterations) - f xstar ≤ ε := by
  let p : ℕ → E := fun n => (M.weight n - 1) •
    ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)
  have hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n) := fun _ => rfl
  have hL : 0 < L := (initialStep_ge_inv_L f L hC11 M).1
  have henergy : ∀ k, 2 * M.step k * M.weight k ^ 2 *
      (f (M.x k) - f xstar) + ‖p k - M.x k + xstar‖ ^ 2 ≤
        ‖M.y0 - xstar‖ ^ 2 := by
    intro k
    induction k with
    | zero =>
        exact accelerated_energy_zero_le f M xstar hy0 hconv
          (fun u => hC11.hasGradientAt u) p hp
    | succ k ih => exact (accelerated_energy_succ_le f L hC11 hconv M xstar hmin p hp k).trans ih
  have hrate : ∀ k, f (M.x k) - f xstar ≤
      (4 * L * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2 := by
    intro k
    have hgap : 0 ≤ f (M.x k) - f xstar := by linarith [hmin (M.x k)]
    have hstep : 1 / (2 * L) ≤ M.step k := method_step_lower f L hC11 M k
    have hweight : 1 + (k : ℝ) / 2 ≤ M.weight k := weight_lower f M k
    have hlower : 0 ≤ 1 + (k : ℝ) / 2 := by positivity
    have hweightSq : (1 + (k : ℝ) / 2) ^ 2 ≤ M.weight k ^ 2 := by nlinarith
    have henergy' : 2 * M.step k * M.weight k ^ 2 *
        (f (M.x k) - f xstar) ≤ ‖M.y0 - xstar‖ ^ 2 := by
      nlinarith [henergy k, sq_nonneg ‖p k - M.x k + xstar‖]
    have hscaledStep := mul_le_mul_of_nonneg_right hstep
      (mul_nonneg (sq_nonneg (M.weight k)) hgap)
    have hscaledWeight := mul_le_mul_of_nonneg_right hweightSq
      (mul_nonneg (le_of_lt (by positivity : 0 < 1 / (2 * L))) hgap)
    have hscaledWeight' : (1 + (k : ℝ) / 2) ^ 2 *
        (1 / (2 * L) * (f (M.x k) - f xstar)) ≤ M.weight k ^ 2 *
        (1 / (2 * L) * (f (M.x k) - f xstar)) := by
      convert hscaledWeight using 1 <;> field_simp <;> ring
    have hcoef : ((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar) ≤
        ‖M.y0 - xstar‖ ^ 2 := by
      have hbase : (1 + (k : ℝ) / 2) ^ 2 *
          (1 / (2 * L) * (f (M.x k) - f xstar)) ≤
          1 / (2 * L) * (M.weight k ^ 2 * (f (M.x k) - f xstar)) := by
        convert hscaledWeight' using 1 <;> ring
      have heq : ((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar) =
          2 * ((1 + (k : ℝ) / 2) ^ 2 *
            (1 / (2 * L) * (f (M.x k) - f xstar))) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      calc
        ((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar) =
            2 * ((1 + (k : ℝ) / 2) ^ 2 *
              (1 / (2 * L) * (f (M.x k) - f xstar))) := heq
        _ ≤ 2 * (1 / (2 * L) * (M.weight k ^ 2 * (f (M.x k) - f xstar))) := by
          gcongr
        _ ≤ 2 * (M.step k * (M.weight k ^ 2 * (f (M.x k) - f xstar))) := by
          gcongr
        _ ≤ ‖M.y0 - xstar‖ ^ 2 := by nlinarith [henergy']
    have hden : 0 < (k + 2 : ℝ) ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    calc
      (f (M.x k) - f xstar) * (k + 2 : ℝ) ^ 2 =
          (4 * L) * (((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar)) := by
            field_simp
      _ ≤ (4 * L) * ‖M.y0 - xstar‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = 4 * L * ‖M.y0 - xstar‖ ^ 2 := by ring
  constructor
  · exact hrate
  · intro ε hε
    dsimp
    let NG := Real.sqrt (4 * L * ‖M.y0 - xstar‖ ^ 2 / ε)
    let D := Real.logb 2 (2 * L * M.initialStep)
    have hC0 : 0 ≤ 4 * L * ‖M.y0 - xstar‖ ^ 2 := by positivity
    have hNG0 : 0 ≤ NG := Real.sqrt_nonneg _
    have hN0 : 0 ≤ Int.ceil NG := Int.ceil_nonneg hNG0
    let iterations := (Int.ceil NG).toNat
    have hNGle : NG ≤ (iterations : ℝ) := by
      rw [show (iterations : ℝ) = (Int.ceil NG : ℤ) by
        exact_mod_cast (Int.toNat_of_nonneg hN0)]
      exact Int.le_ceil NG
    have hsqNG : NG ^ 2 = 4 * L * ‖M.y0 - xstar‖ ^ 2 / ε := by
      dsimp [NG]
      exact Real.sq_sqrt (div_nonneg hC0 (le_of_lt hε))
    have haccuracy : f (M.x iterations) - f xstar ≤ ε := by
      have hden : 0 < (iterations + 2 : ℝ) ^ 2 := by positivity
      calc
        f (M.x iterations) - f xstar ≤
            (4 * L * ‖M.y0 - xstar‖ ^ 2) / (iterations + 2 : ℝ) ^ 2 :=
          hrate iterations
        _ ≤ ε := by
          apply (div_le_iff₀ hden).2
          have hsquares : NG ^ 2 ≤ (iterations : ℝ) ^ 2 :=
            (sq_le_sq₀ hNG0 (by positivity)).2 hNGle
          rw [hsqNG] at hsquares
          have hCiterations : 4 * L * ‖M.y0 - xstar‖ ^ 2 ≤
              ε * (iterations : ℝ) ^ 2 := by
            nlinarith [(div_le_iff₀ hε).mp hsquares]
          have hinc : (iterations : ℝ) ^ 2 ≤ (iterations + 2 : ℝ) ^ 2 := by
            nlinarith [show (0 : ℝ) ≤ iterations by positivity]
          exact hCiterations.trans (mul_le_mul_of_nonneg_left hinc (le_of_lt hε))
    have hD0 : 0 ≤ D := by
      have hsum := search_sum_le_logb f L hC11 M 0
      have hnonneg : (0 : ℝ) ≤
          (((Finset.range (0 + 1)).sum M.searchIndex : ℕ) : ℝ) := by positivity
      linarith [show (((Finset.range (0 + 1)).sum M.searchIndex : ℕ) : ℝ) ≤ D by
        simpa [D] using hsum]
    have hsubset : Finset.range iterations ⊆ Finset.range (iterations + 1) :=
      Finset.range_subset_range.2 (Nat.le_succ _)
    have hsumle : (Finset.range iterations).sum M.searchIndex ≤
        (Finset.range (iterations + 1)).sum M.searchIndex :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    have hsumR : (((Finset.range iterations).sum M.searchIndex : ℕ) : ℝ) ≤ D := by
      have hcast : (((Finset.range iterations).sum M.searchIndex : ℕ) : ℝ) ≤
          (((Finset.range (iterations + 1)).sum M.searchIndex : ℕ) : ℝ) := by
        exact_mod_cast hsumle
      exact hcast.trans (by simpa [D] using search_sum_le_logb f L hC11 M iterations)
    have hsumD : (Finset.range iterations).sum M.searchIndex ≤ (Int.ceil D).toNat := by
      have hceil : (((Finset.range iterations).sum M.searchIndex : ℕ) : ℤ) ≤ Int.ceil D := by
        exact_mod_cast hsumR.trans (Int.le_ceil D)
      exact (Int.le_toNat (Int.ceil_nonneg hD0)).2 hceil
    refine ⟨iterations, acceleratedGradientEvaluationCount f M iterations,
      acceleratedFunctionEvaluationCount f M iterations, rfl, rfl, ?_, ?_, haccuracy⟩
    · rfl
    · change 2 * iterations + (Finset.range iterations).sum M.searchIndex ≤
        (Int.ceil (2 * NG + D + 1)).toNat
      have harg : 0 ≤ 2 * NG + D + 1 := by positivity
      have hY : 0 ≤ Int.ceil (2 * NG + D + 1) := Int.ceil_nonneg harg
      refine (Int.le_toNat hY).2 ?_
      have hiter : (iterations : ℤ) = Int.ceil NG := Int.toNat_of_nonneg hN0
      have hiterR : (iterations : ℝ) = ((Int.ceil NG : ℤ) : ℝ) := by
        exact_mod_cast hiter
      have hltR :
          (((2 * iterations + (Finset.range iterations).sum M.searchIndex : ℕ) : ℤ) : ℝ) <
            ((Int.ceil (2 * NG + D + 1) : ℤ) : ℝ) + 1 := by
        have hceilR : ((Int.ceil NG : ℤ) : ℝ) < NG + 1 := Int.ceil_lt_add_one NG
        have hYle : 2 * NG + D + 1 ≤ ((Int.ceil (2 * NG + D + 1) : ℤ) : ℝ) := Int.le_ceil _
        have hsumR' : (∑ x ∈ Finset.range iterations, (M.searchIndex x : ℝ)) ≤ D := by
          simpa only [Nat.cast_sum] using hsumR
        push_cast
        linarith
      exact Int.lt_add_one_iff.1 (by exact_mod_cast hltR)

end Nesterov1983
