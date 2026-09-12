import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.def_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.def_3
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.algo_2
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.thm_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_3
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_thm_1
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_thm_2

namespace Nesterov1983

/-- The number of auxiliary minimization problems solved in the first `n`
iterations of method (11)-(13). -/
def compositeAuxiliarySolveCount {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ExtremalProblem m E)
    (T : E → ℝ → E) (M : CompositeAcceleratedMethod P T) (n : ℕ) : ℕ :=
  n + (Finset.range n).sum M.searchIndex

/-- The number of collections of component gradients evaluated in the first
`n` iterations of method (11)-(13). -/
def compositeGradientCollectionCount {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ExtremalProblem m E)
    (T : E → ℝ → E) (M : CompositeAcceleratedMethod P T) (n : ℕ) : ℕ :=
  n

/-- The number of vector-valued objective evaluations in the first `n`
iterations of method (11)-(13). -/
def compositeFunctionEvaluationCount {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ExtremalProblem m E)
    (T : E → ℝ → E) (M : CompositeAcceleratedMethod P T) (n : ℕ) : ℕ :=
  2 * n + (Finset.range n).sum M.searchIndex

/-- The quadratic identity for the weights of method (11)--(13). -/
private theorem composite_weight_sq_sub_weight {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ExtremalProblem m E)
    (T : E → ℝ → E) (M : CompositeAcceleratedMethod P T) (k : ℕ) :
    M.weight (k + 1) ^ 2 - M.weight (k + 1) = M.weight k ^ 2 := by
  rw [M.update_weight]
  have hrad : 0 ≤ 4 * M.weight k ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (4 * M.weight k ^ 2 + 1) ^ 2 =
      4 * M.weight k ^ 2 + 1 := Real.sq_sqrt hrad
  nlinarith

/-- The weights of method (11)--(13) grow at least linearly. -/
private theorem composite_weight_lower {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (P : ExtremalProblem m E)
    (T : E → ℝ → E) (M : CompositeAcceleratedMethod P T) : ∀ k : ℕ,
    1 + (k : ℝ) / 2 ≤ M.weight k := by
  intro k
  induction k with
  | zero => simp [M.weight_zero]
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

section CompositeFacts

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {P : ExtremalProblem m E} {T : E → ℝ → E}

private lemma A_eq_initialA_mul (M : CompositeAcceleratedMethod P T) (n : ℕ) :
    M.A n = M.initialA *
      (2 : ℝ) ^ (((Finset.range (n + 1)).sum M.searchIndex : ℕ) : ℤ) := by
  induction n with
  | zero =>
      rw [M.A_eq_doubling_previous 0, if_pos rfl]
      simp only [Finset.sum_range_one, zero_add]
      ring
  | succ n ih =>
      rw [M.A_eq_doubling_previous (n + 1), if_neg (by omega), Nat.add_sub_cancel, ih]
      have hS : (Finset.range (n + 1 + 1)).sum M.searchIndex =
          (Finset.range (n + 1)).sum M.searchIndex + M.searchIndex (n + 1) :=
        Finset.sum_range_succ M.searchIndex (n + 1)
      rw [hS, Nat.cast_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring

private lemma initialA_le_A (M : CompositeAcceleratedMethod P T) (h0 : 0 ≤ M.initialA) (n : ℕ) :
    M.initialA ≤ M.A n := by
  rw [A_eq_initialA_mul]
  have h1 : (1 : ℝ) ≤
      (2 : ℝ) ^ (((Finset.range (n + 1)).sum M.searchIndex : ℕ) : ℤ) :=
    one_le_zpow₀ (by norm_num) (by positivity)
  calc M.initialA = M.initialA * 1 := by ring
    _ ≤ M.initialA * _ := mul_le_mul_of_nonneg_left h1 h0

private lemma A_nonneg (M : CompositeAcceleratedMethod P T) (h0 : 0 ≤ M.initialA) (n : ℕ) :
    0 ≤ M.A n := le_trans h0 (initialA_le_A M h0 n)

private lemma A_mono (M : CompositeAcceleratedMethod P T) (h0 : 0 ≤ M.initialA) (n : ℕ) :
    M.A n ≤ M.A (n + 1) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (M.searchIndex (n + 1) : ℤ) :=
    one_le_zpow₀ (by norm_num) (by positivity)
  have hA := A_nonneg M h0 n
  calc M.A n = 1 * M.A n := by ring
    _ ≤ (2 : ℝ) ^ (M.searchIndex (n + 1) : ℤ) * M.A n :=
        mul_le_mul_of_nonneg_right h1 hA
    _ = M.A (n + 1) := by
        rw [M.A_eq_doubling_previous (n + 1), if_neg (by omega), Nat.add_sub_cancel]

private lemma searchIndex_eq_zero (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)}
    (hLower : HasAuxiliaryValueLowerBound P T Lbar) {k : ℕ}
    (hle : P.F Lbar ≤ (if k = 0 then M.initialA else M.A (k - 1))) :
    M.searchIndex k = 0 := by
  by_contra hne
  have hpos : 0 < M.searchIndex k := Nat.pos_of_ne_zero hne
  have hfail := M.minimal_searchIndex k 0 hpos
  have hfail' : auxiliaryValue P (M.y k) (if k = 0 then M.initialA else M.A (k - 1)) <
      P.F (fbar P (T (M.y k) (if k = 0 then M.initialA else M.A (k - 1)))) := by
    simpa using hfail
  simp only [fbar] at hfail'
  have hpass := hLower (M.y k) (if k = 0 then M.initialA else M.A (k - 1)) hle
  exact absurd hpass (not_le.mpr hfail')

private lemma lt_of_not_searchTest {Lbar : EuclideanSpace ℝ (Fin m)}
    (hLower : HasAuxiliaryValueLowerBound P T Lbar) {A : ℝ} {y : E}
    (h : ¬ P.F (fbar P (T y A)) ≤ auxiliaryValue P y A) : A < P.F Lbar := by
  by_contra hle
  exact h (hLower y A (le_of_not_gt hle))

private lemma A_lt_two_mul (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)}
    (hLower : HasAuxiliaryValueLowerBound P T Lbar)
    (h0 : 0 < M.initialA) (hF : M.initialA < P.F Lbar) (n : ℕ) :
    M.A n < 2 * P.F Lbar := by
  induction n with
  | zero =>
      rw [M.A_eq_doubling_previous 0, if_pos rfl]
      rcases Nat.eq_zero_or_pos (M.searchIndex 0) with hs | hs
      · simp only [hs, Nat.cast_zero, zpow_zero, one_mul]
        linarith
      · have hfail := M.minimal_searchIndex 0 (M.searchIndex 0 - 1) (by omega)
        have hfail' : auxiliaryValue P (M.y 0)
              ((2 : ℝ) ^ ((M.searchIndex 0 - 1 : ℕ) : ℤ) * M.initialA) <
            P.F (fbar P (T (M.y 0)
              ((2 : ℝ) ^ ((M.searchIndex 0 - 1 : ℕ) : ℤ) * M.initialA))) := by
          simpa using hfail
        have hlt := lt_of_not_searchTest hLower (not_le.mpr hfail')
        have hpow : (2 : ℝ) ^ (M.searchIndex 0 : ℤ) =
            2 * (2 : ℝ) ^ ((M.searchIndex 0 - 1 : ℕ) : ℤ) := by
          rw [show (M.searchIndex 0 : ℤ) = ((M.searchIndex 0 - 1 : ℕ) : ℤ) + 1 by omega,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring
        rw [hpow]
        nlinarith
  | succ n ih =>
      rw [M.A_eq_doubling_previous (n + 1), if_neg (by omega), Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos (M.searchIndex (n + 1)) with hs | hs
      · simp only [hs, Nat.cast_zero, zpow_zero, one_mul]
        exact ih
      · have hfail := M.minimal_searchIndex (n + 1) (M.searchIndex (n + 1) - 1) (by omega)
        have hfail' : auxiliaryValue P (M.y (n + 1))
              ((2 : ℝ) ^ ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) * M.A n) <
            P.F (fbar P (T (M.y (n + 1))
              ((2 : ℝ) ^ ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) * M.A n))) := by
          simpa using hfail
        have hlt := lt_of_not_searchTest hLower (not_le.mpr hfail')
        have hpow : (2 : ℝ) ^ (M.searchIndex (n + 1) : ℤ) =
            2 * (2 : ℝ) ^ ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) := by
          rw [show (M.searchIndex (n + 1) : ℤ) =
              ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) + 1 by omega,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring
        rw [hpow]
        nlinarith

private lemma one_lt_div_of_lt {a b : ℝ} (ha : 0 < a) (h : a < b) : 1 < b / a := by
  rw [lt_div_iff₀ ha]; linarith

/-- The total number of doublings of `A` performed by method (11)-(13) is bounded by
`⌈log₂(F(L̄)/A_{-1})⌉` (paper Theorem 2 (2a), doubling part). -/
theorem composite_searchIndex_sum_le (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)}
    (hLower : HasAuxiliaryValueLowerBound P T Lbar) (hApos : 0 < M.initialA) (N : ℕ) :
    (Finset.range N).sum M.searchIndex ≤
      (Int.ceil (max (Real.logb 2 (P.F Lbar / M.initialA)) 0)).toNat := by
  rcases N with _ | N
  · simp
  · by_cases hle : P.F Lbar ≤ M.initialA
    · have hzero : ∀ k, M.searchIndex k = 0 := by
        intro k
        refine searchIndex_eq_zero M hLower ?_
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simpa using hle
        · have hk' : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
          simp only [hk', if_false]
          exact le_trans hle (initialA_le_A M (le_of_lt hApos) (k - 1))
      have hsum0 : (Finset.range (N + 1)).sum M.searchIndex = 0 :=
        Finset.sum_eq_zero (fun k _ => hzero k)
      rw [hsum0]
      exact Nat.zero_le _
    · push_neg at hle
      have hlogpos : 0 < Real.logb 2 (P.F Lbar / M.initialA) := by
        apply Real.logb_pos (by norm_num)
        exact one_lt_div_of_lt hApos hle
      have hmax : max (Real.logb 2 (P.F Lbar / M.initialA)) 0 =
          Real.logb 2 (P.F Lbar / M.initialA) := max_eq_left (le_of_lt hlogpos)
      rw [hmax]
      have hS := A_eq_initialA_mul M N
      have hlt := A_lt_two_mul M hLower hApos hle N
      have hlog : (((Finset.range (N + 1)).sum M.searchIndex : ℕ) : ℝ) =
          Real.logb 2 (M.A N / M.initialA) := by
        rw [hS, mul_div_cancel_left₀ _ (ne_of_gt hApos)]
        rw [show (2 : ℝ) ^ (((Finset.range (N + 1)).sum M.searchIndex : ℕ) : ℤ) =
            (2 : ℝ) ^ ((((Finset.range (N + 1)).sum M.searchIndex : ℕ) : ℤ) : ℝ) from
          (Real.rpow_intCast 2 _).symm]
        rw [Real.logb_rpow (by norm_num) (by norm_num)]
        push_cast
        ring
      have hbound : (((Finset.range (N + 1)).sum M.searchIndex : ℕ) : ℝ) <
          Real.logb 2 (P.F Lbar / M.initialA) + 1 := by
        rw [hlog]
        have h1 : M.A N / M.initialA < 2 * P.F Lbar / M.initialA :=
          div_lt_div_of_pos_right hlt hApos
        have h2 : 2 * P.F Lbar / M.initialA = 2 * (P.F Lbar / M.initialA) := by ring
        rw [h2] at h1
        have h3 : 0 < P.F Lbar / M.initialA := div_pos (lt_trans hApos hle) hApos
        have h4 := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
          (div_pos (lt_of_lt_of_le hApos (initialA_le_A M (le_of_lt hApos) N)) hApos) h1
        rw [Real.logb_mul (by norm_num) (ne_of_gt h3)] at h4
        rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at h4
        linarith
      have hbound' : (∑ x ∈ Finset.range (N + 1), (M.searchIndex x : ℝ)) <
          Real.logb 2 (P.F Lbar / M.initialA) + 1 := by
        simpa only [Nat.cast_sum] using hbound
      have hceil : (((Finset.range (N + 1)).sum M.searchIndex : ℕ) : ℤ) ≤
          Int.ceil (Real.logb 2 (P.F Lbar / M.initialA)) := by
        have h1 : (↑((Finset.range (N + 1)).sum M.searchIndex : ℕ) : ℤ) - 1 <
            Int.ceil (Real.logb 2 (P.F Lbar / M.initialA)) := by
          rw [Int.lt_ceil]
          push_cast
          linarith [hbound']
        omega
      exact (Int.le_toNat (Int.ceil_nonneg (le_of_lt hlogpos))).2 hceil

private theorem cw_sq_sub (M : CompositeAcceleratedMethod P T) (k : ℕ) :
    M.weight (k + 1) ^ 2 - M.weight (k + 1) = M.weight k ^ 2 := by
  rw [M.update_weight]
  have hrad : 0 ≤ 4 * M.weight k ^ 2 + 1 := by positivity
  have hsqrt : Real.sqrt (4 * M.weight k ^ 2 + 1) ^ 2 = 4 * M.weight k ^ 2 + 1 :=
    Real.sq_sqrt hrad
  nlinarith

private theorem cw_lower (M : CompositeAcceleratedMethod P T) : ∀ k : ℕ,
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

private theorem cw_pos (M : CompositeAcceleratedMethod P T) (k : ℕ) : 0 < M.weight k :=
  lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 + (k : ℝ) / 2) (cw_lower M k)

private theorem cA_pos (M : CompositeAcceleratedMethod P T) (h0 : 0 < M.initialA) (n : ℕ) :
    0 < M.A n := by
  rw [A_eq_initialA_mul]
  exact mul_pos h0 (zpow_pos (by norm_num) _)

private theorem cx_sub_y (M : CompositeAcceleratedMethod P T) (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ) :
    M.x k - M.y (k + 1) = (M.weight (k + 1))⁻¹ • p k := by
  have hne : M.weight (k + 1) ≠ 0 := ne_of_gt (cw_pos M (k + 1))
  rw [M.update_y, hp k]
  field_simp [hne]
  module

private theorem cp_rec (M : CompositeAcceleratedMethod P T) (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ) :
    p (k + 1) - M.x (k + 1) = p k - M.x k +
      M.weight (k + 1) • (M.y (k + 1) - M.x (k + 1)) := by
  rw [hp (k + 1), hp k, M.update_y k]
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  have hne : M.weight (k + 1) ≠ 0 := ne_of_gt (cw_pos M (k + 1))
  apply (smul_right_injective E hne)
  simp only [smul_sub, smul_add, smul_smul]
  field_simp [hne]
  module

private theorem cstar (M : CompositeAcceleratedMethod P T)
    (hT : HasAuxiliaryMappingEstimates P T) (xstar : E) (hxstar : xstar ∈ P.Q) (k : ℕ)
    (hA : 0 < M.A (k + 1)) :
    P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar)) +
        M.A (k + 1) / 2 * ‖M.y (k + 1) - M.x (k + 1)‖ ^ 2 ≤
      M.A (k + 1) * inner ℝ (M.y (k + 1) - M.x (k + 1)) (M.y (k + 1) - xstar) := by
  have h10 := hT.2 xstar hxstar (M.y (k + 1)) (M.A (k + 1)) (le_of_lt hA)
  have hacc := M.accepted (k + 1)
  simp only [fbar] at hacc
  rw [← M.update_x (k + 1)] at h10 hacc
  rw [show xstar - M.y (k + 1) = -(M.y (k + 1) - xstar) by abel, inner_neg_right] at h10
  linarith

private theorem cprev (M : CompositeAcceleratedMethod P T)
    (hT : HasAuxiliaryMappingEstimates P T) (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (k : ℕ)
    (hA : 0 < M.A (k + 1)) :
    M.A (k + 1) / 2 * ‖M.y (k + 1) - M.x (k + 1)‖ ^ 2 ≤
      (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1))))) -
      (M.weight (k + 1))⁻¹ *
        (M.A (k + 1) * inner ℝ (M.y (k + 1) - M.x (k + 1)) (p k)) := by
  have hmem : M.x k ∈ P.Q := by
    rw [M.update_x k]; exact (hT.1 (M.y k) (M.A k)).1
  have h10 := hT.2 (M.x k) hmem (M.y (k + 1)) (M.A (k + 1)) (le_of_lt hA)
  have hacc := M.accepted (k + 1)
  simp only [fbar] at hacc
  rw [← M.update_x (k + 1)] at h10
  rw [← M.update_x (k + 1)] at hacc
  have hxy := cx_sub_y M p hp k
  rw [hxy, real_inner_smul_right] at h10
  have hterm : (M.weight (k + 1))⁻¹ *
        (M.A (k + 1) * inner ℝ (M.y (k + 1) - M.x (k + 1)) (p k)) =
      M.A (k + 1) * ((M.weight (k + 1))⁻¹ *
        inner ℝ (M.y (k + 1) - M.x (k + 1)) (p k)) := by ring
  rw [hterm]
  linarith

private theorem cenergy_zero (M : CompositeAcceleratedMethod P T)
    (hT : HasAuxiliaryMappingEstimates P T) (xstar : E) (hxstar : xstar ∈ P.Q)
    (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)) (hA : 0 < M.A 0) :
    2 * (M.A 0)⁻¹ * M.weight 0 ^ 2 *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x 0))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
      ‖p 0 - M.x 0 + xstar‖ ^ 2 ≤ ‖M.y0 - xstar‖ ^ 2 := by
  have h10 := hT.2 xstar hxstar (M.y 0) (M.A 0) (le_of_lt hA)
  have hacc := M.accepted 0
  simp only [fbar] at hacc
  rw [← M.update_x 0] at h10 hacc
  rw [M.y_zero] at h10 hacc
  rw [hp 0, M.weight_zero]
  simp only [↓reduceIte, sub_self, zero_smul, one_pow, mul_one, zero_sub]
  rw [show -M.x 0 + xstar = xstar - M.x 0 by abel]
  have hinner : inner ℝ (M.y0 - M.x 0) (xstar - M.y0) =
      - inner ℝ (M.y0 - M.x 0) (M.y0 - xstar) := by
    rw [show xstar - M.y0 = -(M.y0 - xstar) by abel, inner_neg_right]
  rw [hinner] at h10
  rw [mul_neg] at h10
  have hG : P.F (WithLp.toLp 2 (fun i => P.f i (M.x 0))) -
      P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
      M.A 0 * inner ℝ (M.y0 - M.x 0) (M.y0 - xstar) -
        (M.A 0 / 2) * ‖M.y0 - M.x 0‖ ^ 2 := by linarith
  have h2 : 2 * (M.A 0)⁻¹ *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x 0))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) ≤
      2 * inner ℝ (M.y0 - M.x 0) (M.y0 - xstar) - ‖M.y0 - M.x 0‖ ^ 2 := by
    have hne : M.A 0 ≠ 0 := ne_of_gt hA
    have hmul := mul_le_mul_of_nonneg_left hG (le_of_lt (inv_pos.mpr hA))
    have hsimp : (M.A 0)⁻¹ *
        (M.A 0 * inner ℝ (M.y0 - M.x 0) (M.y0 - xstar) -
          M.A 0 / 2 * ‖M.y0 - M.x 0‖ ^ 2) =
        inner ℝ (M.y0 - M.x 0) (M.y0 - xstar) - ‖M.y0 - M.x 0‖ ^ 2 / 2 := by
      field_simp
    rw [hsimp] at hmul
    linarith
  have hsq : ‖xstar - M.x 0‖ ^ 2 = ‖M.y0 - xstar‖ ^ 2 -
      2 * inner ℝ (M.y0 - xstar) (M.y0 - M.x 0) + ‖M.y0 - M.x 0‖ ^ 2 := by
    rw [show xstar - M.x 0 = -((M.y0 - xstar) - (M.y0 - M.x 0)) by abel, norm_neg,
      norm_sub_pow_two_real]
  rw [hsq]
  have hcomm : inner ℝ (M.y0 - xstar) (M.y0 - M.x 0) =
      inner ℝ (M.y0 - M.x 0) (M.y0 - xstar) := real_inner_comm _ _
  rw [hcomm]
  linarith

private theorem A_le_two_mul (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)}
    (hLower : HasAuxiliaryValueLowerBound P T Lbar)
    (h0 : 0 < M.initialA) (hF : M.initialA ≤ P.F Lbar) (n : ℕ) :
    M.A n ≤ 2 * P.F Lbar := by
  have hFpos : 0 < P.F Lbar := lt_of_lt_of_le h0 hF
  induction n with
  | zero =>
      rw [M.A_eq_doubling_previous 0, if_pos rfl]
      rcases Nat.eq_zero_or_pos (M.searchIndex 0) with hs | hs
      · simp only [hs, Nat.cast_zero, zpow_zero, one_mul]; linarith
      · have hfail := M.minimal_searchIndex 0 (M.searchIndex 0 - 1) (by omega)
        have hfail' : auxiliaryValue P (M.y 0)
              ((2 : ℝ) ^ ((M.searchIndex 0 - 1 : ℕ) : ℤ) * M.initialA) <
            P.F (fbar P (T (M.y 0)
              ((2 : ℝ) ^ ((M.searchIndex 0 - 1 : ℕ) : ℤ) * M.initialA))) := by
          simpa using hfail
        simp only [fbar] at hfail'
        have hlt := lt_of_not_searchTest hLower (not_le.mpr hfail')
        have hpow : (2 : ℝ) ^ (M.searchIndex 0 : ℤ) =
            2 * (2 : ℝ) ^ ((M.searchIndex 0 - 1 : ℕ) : ℤ) := by
          rw [show (M.searchIndex 0 : ℤ) = ((M.searchIndex 0 - 1 : ℕ) : ℤ) + 1 by omega,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring
        rw [hpow]
        nlinarith
  | succ n ih =>
      rw [M.A_eq_doubling_previous (n + 1), if_neg (by omega), Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos (M.searchIndex (n + 1)) with hs | hs
      · simp only [hs, Nat.cast_zero, zpow_zero, one_mul]; exact ih
      · have hfail := M.minimal_searchIndex (n + 1) (M.searchIndex (n + 1) - 1) (by omega)
        have hfail' : auxiliaryValue P (M.y (n + 1))
              ((2 : ℝ) ^ ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) * M.A n) <
            P.F (fbar P (T (M.y (n + 1))
              ((2 : ℝ) ^ ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) * M.A n))) := by
          simpa using hfail
        simp only [fbar] at hfail'
        have hlt := lt_of_not_searchTest hLower (not_le.mpr hfail')
        have hpow : (2 : ℝ) ^ (M.searchIndex (n + 1) : ℤ) =
            2 * (2 : ℝ) ^ ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) := by
          rw [show (M.searchIndex (n + 1) : ℤ) =
              ((M.searchIndex (n + 1) - 1 : ℕ) : ℤ) + 1 by omega,
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          norm_num
          ring
        rw [hpow]
        nlinarith

private theorem cenergy_succ (M : CompositeAcceleratedMethod P T)
    (hT : HasAuxiliaryMappingEstimates P T) (xstar : E) (hstar : xstar ∈ P.solutionSet)
    (p : ℕ → E)
    (hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n))
    (hApos : 0 < M.initialA) (k : ℕ) :
    2 * (M.A (k + 1))⁻¹ * M.weight (k + 1) ^ 2 *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
      ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 ≤
    2 * (M.A k)⁻¹ * M.weight k ^ 2 *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
      ‖p k - M.x k + xstar‖ ^ 2 := by
  have hxQ : xstar ∈ P.Q := (P.solution_iff xstar).mp hstar |>.1
  have hA1 : 0 < M.A (k + 1) := cA_pos M hApos (k + 1)
  have hA1ne : M.A (k + 1) ≠ 0 := ne_of_gt hA1
  have ha : 0 < M.weight (k + 1) := cw_pos M (k + 1)
  have hane : M.weight (k + 1) ≠ 0 := ne_of_gt ha
  let s : ℝ := (M.A (k + 1))⁻¹
  let v : E := M.y (k + 1) - M.x (k + 1)
  let g : E := (M.A (k + 1)) • v
  have hvs : (M.weight (k + 1) * s) • g = M.weight (k + 1) • v := by
    simp only [g, smul_smul]
    rw [mul_assoc, inv_mul_cancel₀ hA1ne, mul_one]
  have hrecS : p (k + 1) - M.x (k + 1) = p k - M.x k +
      (M.weight (k + 1) * s) • g := by
    rw [cp_rec M p hp k, hvs]
  have hgnorm : ‖g‖ ^ 2 = (M.A (k + 1)) ^ 2 * ‖v‖ ^ 2 := by
    simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos hA1]
    ring
  have hginner : ∀ w : E, inner ℝ g w = M.A (k + 1) * inner ℝ v w := by
    intro w
    simp only [g, real_inner_smul_left]
  have hstarS : P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar)) + s / 2 * ‖g‖ ^ 2 ≤
      inner ℝ g (M.y (k + 1) - xstar) := by
    have h := cstar M hT xstar hxQ k hA1
    rw [hgnorm, hginner (M.y (k + 1) - xstar)]
    have hs : s / 2 * ((M.A (k + 1)) ^ 2 * ‖v‖ ^ 2) =
        M.A (k + 1) / 2 * ‖v‖ ^ 2 := by
      simp only [s]
      field_simp
    rw [hs]
    exact h
  have hprevS : s / 2 * ‖g‖ ^ 2 ≤
      (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1))))) -
      (M.weight (k + 1))⁻¹ * inner ℝ g (p k) := by
    have h := cprev M hT p hp k hA1
    rw [hgnorm, hginner (p k)]
    have hs : s / 2 * ((M.A (k + 1)) ^ 2 * ‖v‖ ^ 2) =
        M.A (k + 1) / 2 * ‖v‖ ^ 2 := by
      simp only [s]
      field_simp
    rw [hs]
    exact h
  have hgap : 0 ≤ P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
      P.F (WithLp.toLp 2 (fun i => P.f i xstar)) := by
    rcases (P.solution_iff xstar).mp hstar with ⟨_, hmin⟩
    have hxQ' : M.x k ∈ P.Q := by
      rw [M.update_x k]; exact (hT.1 (M.y k) (M.A k)).1
    linarith [hmin (M.x k) hxQ']
  have hq : p k - M.x k + xstar =
      (1 - (M.weight (k + 1))⁻¹) • p k + (xstar - M.y (k + 1)) := by
    have hxy := cx_sub_y M p hp k
    calc
      p k - M.x k + xstar = p k - (M.x k - M.y (k + 1)) +
          (xstar - M.y (k + 1)) := by abel
      _ = p k - (M.weight (k + 1))⁻¹ • p k + (xstar - M.y (k + 1)) := by rw [hxy]
      _ = (1 - (M.weight (k + 1))⁻¹) • p k + (xstar - M.y (k + 1)) := by module
  have hinter : inner ℝ g (p k - M.x k + xstar) =
      (1 - (M.weight (k + 1))⁻¹) * inner ℝ g (p k) +
        inner ℝ g (xstar - M.y (k + 1)) := by
    rw [hq, inner_add_right, real_inner_smul_right]
  have hnorm : ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 =
      ‖p k - M.x k + xstar‖ ^ 2 +
        2 * (M.weight (k + 1) - 1) * s * inner ℝ g (p k) +
        2 * M.weight (k + 1) * s * inner ℝ g (xstar - M.y (k + 1)) +
        M.weight (k + 1) ^ 2 * s ^ 2 * ‖g‖ ^ 2 := by
    rw [show p (k + 1) - M.x (k + 1) + xstar =
        (p k - M.x k + xstar) + (M.weight (k + 1) * s) • g by
          rw [hrecS]; abel]
    rw [norm_add_pow_two_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (mul_pos ha (inv_pos.mpr hA1))]
    have hs : inner ℝ (p k - M.x k + xstar) g =
        inner ℝ g (p k - M.x k + xstar) := real_inner_comm _ _
    rw [hs, hinter]
    simp only [s]
    field_simp [hane]
    ring
  have hstar' : inner ℝ g (xstar - M.y (k + 1)) ≤
      -(P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar))) - s / 2 * ‖g‖ ^ 2 := by
    rw [show xstar - M.y (k + 1) = -(M.y (k + 1) - xstar) by abel, inner_neg_right]
    linarith
  have hwid := cw_sq_sub M k
  have hcoef : 0 ≤ 2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s := by
    rw [hwid]
    positivity
  have hpreviousMul :
      (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s ^ 2 * ‖g‖ ^ 2 ≤
        2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s *
          ((P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar))) -
           (P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar)))) -
        2 * (M.weight (k + 1) - 1) * s * inner ℝ g (p k) := by
    calc
      (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s ^ 2 * ‖g‖ ^ 2 =
          (2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s) *
            (s / 2 * ‖g‖ ^ 2) := by ring
      _ ≤ (2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s) *
            ((P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
              P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1))))) -
              (M.weight (k + 1))⁻¹ * inner ℝ g (p k)) :=
          mul_le_mul_of_nonneg_left hprevS hcoef
      _ = 2 * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) * s *
            ((P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
              P.F (WithLp.toLp 2 (fun i => P.f i xstar))) -
             (P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
              P.F (WithLp.toLp 2 (fun i => P.f i xstar)))) -
          2 * (M.weight (k + 1) - 1) * s * inner ℝ g (p k) := by
          field_simp [hane]
          ring
  have hstarMul := mul_le_mul_of_nonneg_left hstar'
    (show 0 ≤ 2 * M.weight (k + 1) * s by positivity)
  have hmain :
      2 * s * M.weight (k + 1) ^ 2 *
          (P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
          ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 ≤
        2 * s * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) *
          (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
          ‖p k - M.x k + xstar‖ ^ 2 := by
    ring_nf at hnorm hpreviousMul hstarMul ⊢
    nlinarith [hnorm, hstarMul]
  have hsle : s ≤ (M.A k)⁻¹ := by
    simp only [s]
    exact (inv_le_inv₀ hA1 (cA_pos M hApos k)).2 (A_mono M (le_of_lt hApos) k)
  have hscale := mul_le_mul_of_nonneg_right hsle
    (mul_nonneg (sq_nonneg (M.weight k)) hgap)
  calc
    2 * s * M.weight (k + 1) ^ 2 *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x (k + 1)))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
      ‖p (k + 1) - M.x (k + 1) + xstar‖ ^ 2 ≤
      2 * s * (M.weight (k + 1) ^ 2 - M.weight (k + 1)) *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
        ‖p k - M.x k + xstar‖ ^ 2 := hmain
    _ = 2 * s * M.weight k ^ 2 *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
        ‖p k - M.x k + xstar‖ ^ 2 := by rw [hwid]
    _ ≤ 2 * (M.A k)⁻¹ * M.weight k ^ 2 *
        (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
        ‖p k - M.x k + xstar‖ ^ 2 := by nlinarith

/-- The Lyapunov inequality of Theorem 2: `a_k²(F(f̄(x_k)) - F(f̄(x*))) ≤ F(L̄)‖y₀ - x*‖²`. -/
theorem composite_lyapunov (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)}
    (hT : HasAuxiliaryMappingEstimates P T) (hLower : HasAuxiliaryValueLowerBound P T Lbar)
    (xstar : E) (hstar : xstar ∈ P.solutionSet)
    (hApos : 0 < M.initialA) (hAle : M.initialA ≤ P.F Lbar) (k : ℕ) :
    M.weight k ^ 2 * (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar))) ≤ P.F Lbar * ‖M.y0 - xstar‖ ^ 2 := by
  let p : ℕ → E := fun n => (M.weight n - 1) •
    ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)
  have hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n) := fun _ => rfl
  have hxQ : xstar ∈ P.Q := (P.solution_iff xstar).mp hstar |>.1
  have henergy : ∀ j, 2 * (M.A j)⁻¹ * M.weight j ^ 2 *
      (P.F (WithLp.toLp 2 (fun i => P.f i (M.x j))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar))) +
        ‖p j - M.x j + xstar‖ ^ 2 ≤ ‖M.y0 - xstar‖ ^ 2 := by
    intro j
    induction j with
    | zero => exact cenergy_zero M hT xstar hxQ p hp (cA_pos M hApos 0)
    | succ j ih => exact (cenergy_succ M hT xstar hstar p hp hApos j).trans ih
  have hGap : 0 ≤ P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
      P.F (WithLp.toLp 2 (fun i => P.f i xstar)) := by
    rcases (P.solution_iff xstar).mp hstar with ⟨_, hmin⟩
    have hxQ' : M.x k ∈ P.Q := by
      rw [M.update_x k]; exact (hT.1 (M.y k) (M.A k)).1
    linarith [hmin (M.x k) hxQ']
  have hA2 : M.A k ≤ 2 * P.F Lbar := A_le_two_mul M hLower hApos hAle k
  have hne : M.A k ≠ 0 := ne_of_gt (cA_pos M hApos k)
  have h1 : 2 * (M.A k)⁻¹ *
      (M.weight k ^ 2 * (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar)))) ≤ ‖M.y0 - xstar‖ ^ 2 := by
    linarith [henergy k, sq_nonneg ‖p k - M.x k + xstar‖]
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (half_pos (cA_pos M hApos k)))
  have h3 : (M.A k / 2) * (2 * (M.A k)⁻¹ *
      (M.weight k ^ 2 * (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar))))) =
      M.weight k ^ 2 * (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar))) := by
    field_simp
  rw [h3] at h2
  calc
    M.weight k ^ 2 * (P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar))) ≤
        (M.A k / 2) * ‖M.y0 - xstar‖ ^ 2 := h2
    _ ≤ P.F Lbar * ‖M.y0 - xstar‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The initial points of method (11)-(13) give nonnegative secant slopes. -/
private theorem initialL_nonneg (M : CompositeAcceleratedMethod P T) :
    ∀ i, 0 ≤ M.initialL i := by
  intro i
  have hzne : 0 < ‖M.y0 - M.z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm M.z_ne_y0))
  rw [M.initialL_eq i]
  exact div_nonneg (norm_nonneg _) (le_of_lt hzne)

/-- `L̄₀ ≤ L̄` componentwise: the secant slopes `(11)` are bounded by the Lipschitz
constants.  This is where the `C^{1,1}` hypothesis is used. -/
private theorem initialL_le_Lbar (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)} (hC11 : ∀ i, IsC11 (P.f i) (Lbar i)) :
    ∀ i, M.initialL i ≤ Lbar i := by
  intro i
  have hzne : 0 < ‖M.y0 - M.z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm M.z_ne_y0))
  rw [M.initialL_eq i]
  exact (div_le_iff₀ hzne).2 ((hC11 i).lipschitz M.y0 M.z)

/-- The paper's implicit fact `A₋₁ = F(L̄₀) ≤ F(L̄)`: it follows from `L̄₀ ≤ L̄` and
monotonicity of `F` on the nonnegative orthant (the structural property of the
extremal problem `(8)` that the paper leaves implicit). -/
theorem composite_initialA_le (M : CompositeAcceleratedMethod P T)
    {Lbar : EuclideanSpace ℝ (Fin m)} (hC11 : ∀ i, IsC11 (P.f i) (Lbar i))
    (hFmono : ∀ u v : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ u i) → (∀ i, u i ≤ v i) →
      P.F u ≤ P.F v) :
    M.initialA ≤ P.F Lbar := by
  rw [M.initialA_eq]
  exact hFmono _ _ (initialL_nonneg M) (initialL_le_Lbar M hC11)

end CompositeFacts

/-- The rate and auxiliary-problem, gradient, and value-evaluation complexities of Theorem 2. -/
theorem composite_accelerated_rate {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (P : ExtremalProblem m E) (T : E → ℝ → E)
    (M : CompositeAcceleratedMethod P T) (xstar : E) (Lbar : EuclideanSpace ℝ (Fin m))
    (hstar : xstar ∈ P.solutionSet)
    (hC11 : ∀ i, IsC11 (P.f i) (Lbar i))
    (hT : HasAuxiliaryMappingEstimates P T)
    (hLower : HasAuxiliaryValueLowerBound P T Lbar)
    (hApos : 0 < M.initialA)
    (hFmono : ∀ u v : EuclideanSpace ℝ (Fin m), (∀ i, 0 ≤ u i) → (∀ i, u i ≤ v i) →
      P.F u ≤ P.F v) :
    (∀ k, P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) - P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
      (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2) ∧
    ∀ ε : ℝ, 0 < ε →
      let NG := Real.sqrt (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 / ε)
      let doublingAllowance := max (Real.logb 2 (P.F Lbar / M.initialA)) 0
      let NA := Int.ceil NG + Int.ceil doublingAllowance
      let NF := 2 * Int.ceil NG + Int.ceil doublingAllowance
      ∃ iterations auxiliarySolves gradientCollections functionEvaluations : ℕ,
        auxiliarySolves = compositeAuxiliarySolveCount P T M iterations ∧
        gradientCollections = compositeGradientCollectionCount P T M iterations ∧
        functionEvaluations = compositeFunctionEvaluationCount P T M iterations ∧
        auxiliarySolves ≤ NA.toNat ∧
        gradientCollections ≤ (Int.ceil NG).toNat ∧
        functionEvaluations ≤ NF.toNat ∧
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x iterations))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤ ε := by
  have hAle : M.initialA ≤ P.F Lbar := composite_initialA_le M hC11 hFmono
  have hgap_nonneg : ∀ k : ℕ,
      0 ≤ P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
        P.F (WithLp.toLp 2 (fun i => P.f i xstar)) := by
    intro k
    have hxQ : M.x k ∈ P.Q := by
      rw [M.update_x k]
      exact (hT.1 (M.y k) (M.A k)).1
    rcases (P.solution_iff xstar).mp hstar with ⟨_, hmin⟩
    linarith [hmin (M.x k) hxQ]
  have hrate : ∀ k : ℕ,
      P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) - P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
        (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2 := by
    intro k
    let gap := P.F (WithLp.toLp 2 (fun i => P.f i (M.x k))) -
      P.F (WithLp.toLp 2 (fun i => P.f i xstar))
    have hweight := composite_weight_lower P T M k
    have hbase : 0 ≤ 1 + (k : ℝ) / 2 := by positivity
    have hweight0 : 0 ≤ M.weight k := le_trans hbase hweight
    have hsq : (1 + (k : ℝ) / 2) ^ 2 ≤ M.weight k ^ 2 :=
      (sq_le_sq₀ hbase hweight0).2 hweight
    have hscaled : (1 + (k : ℝ) / 2) ^ 2 * gap ≤
        P.F Lbar * ‖M.y0 - xstar‖ ^ 2 := by
      calc
        (1 + (k : ℝ) / 2) ^ 2 * gap ≤ M.weight k ^ 2 * gap :=
          mul_le_mul_of_nonneg_right hsq (hgap_nonneg k)
        _ ≤ P.F Lbar * ‖M.y0 - xstar‖ ^ 2 :=
          composite_lyapunov M hT hLower xstar hstar hApos hAle k
    have hden : 0 < (k + 2 : ℝ) ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    norm_num [Nat.cast_add, Nat.cast_ofNat] at hscaled ⊢
    nlinarith
  constructor
  · exact hrate
  · intro ε hε
    dsimp
    let NG := Real.sqrt (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 / ε)
    let D := Int.ceil (max (Real.logb 2 (P.F Lbar / M.initialA)) 0)
    have hC0 : 0 ≤ 4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 := by
      have h0 := composite_lyapunov M hT hLower xstar hstar hApos hAle 0
      rw [M.weight_zero] at h0
      nlinarith [hgap_nonneg 0]
    have hNG0 : 0 ≤ NG := Real.sqrt_nonneg _
    have hN0 : 0 ≤ Int.ceil NG := Int.ceil_nonneg hNG0
    have hD0 : 0 ≤ D := by
      exact Int.ceil_nonneg (le_max_right _ _)
    let iterations := (Int.ceil NG).toNat
    have hNGle : NG ≤ (iterations : ℝ) := by
      rw [show (iterations : ℝ) = (Int.ceil NG : ℤ) by
        exact_mod_cast (Int.toNat_of_nonneg hN0)]
      exact (Int.le_ceil NG : NG ≤ (Int.ceil NG : ℝ))
    have hsqNG : NG ^ 2 = 4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 / ε := by
      dsimp [NG]
      exact Real.sq_sqrt (div_nonneg hC0 (le_of_lt hε))
    have haccuracy :
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x iterations))) -
          P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤ ε := by
      have hden : 0 < (iterations + 2 : ℝ) ^ 2 := by positivity
      calc
        P.F (WithLp.toLp 2 (fun i => P.f i (M.x iterations))) -
            P.F (WithLp.toLp 2 (fun i => P.f i xstar)) ≤
            (4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2) / (iterations + 2 : ℝ) ^ 2 := hrate iterations
        _ ≤ ε := by
          apply (div_le_iff₀ hden).2
          have hsquares : NG ^ 2 ≤ (iterations : ℝ) ^ 2 :=
            (sq_le_sq₀ hNG0 (by positivity)).2 hNGle
          rw [hsqNG] at hsquares
          have hCiterations : 4 * P.F Lbar * ‖M.y0 - xstar‖ ^ 2 ≤
              ε * (iterations : ℝ) ^ 2 := by
            nlinarith [(div_le_iff₀ hε).mp hsquares]
          have hiter0 : 0 ≤ (iterations : ℝ) := by positivity
          have hinc : (iterations : ℝ) ^ 2 ≤ (iterations + 2 : ℝ) ^ 2 := by
            nlinarith
          exact hCiterations.trans (mul_le_mul_of_nonneg_left hinc (le_of_lt hε))
    refine ⟨iterations, compositeAuxiliarySolveCount P T M iterations,
      compositeGradientCollectionCount P T M iterations,
      compositeFunctionEvaluationCount P T M iterations, rfl, rfl, rfl, ?_, ?_, ?_, haccuracy⟩
    · change iterations + (Finset.range iterations).sum M.searchIndex ≤
        (Int.ceil NG + D).toNat
      rw [Int.toNat_add hN0 hD0]
      exact Nat.add_le_add_left
        (by simpa [D] using composite_searchIndex_sum_le M hLower hApos iterations) _
    · rfl
    · change 2 * iterations + (Finset.range iterations).sum M.searchIndex ≤
        (2 * Int.ceil NG + D).toNat
      have htwoN : 0 ≤ 2 * Int.ceil NG := by omega
      rw [Int.toNat_add htwoN hD0]
      rw [Int.toNat_mul (by omega) hN0]
      exact Nat.add_le_add_left
        (by simpa [D] using composite_searchIndex_sum_le M hLower hApos iterations) _

end Nesterov1983
