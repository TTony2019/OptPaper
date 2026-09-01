import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Convex.ProximalOperator
import Foundation.Convex.Subdifferential
import Foundation.Hilbert.WeakTopology
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.algo_1

namespace AbbasDynamical2015

open Filter
open scoped Pointwise

private theorem fixed_backward_forward_prox_mem_solution_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu : ℝ) (hmu : 0 < mu)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (y : H)
    (hy : ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y -
      mu • B (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y) = y) :
    ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y ∈ S := by
  apply (hsolution _).2
  have hres := ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, hmu⟩ y
  have hdiff : y - ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y =
      -(mu • B (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y)) := by
    calc
      y - ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y =
          (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y -
            mu • B (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y)) -
            ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y := by rw [hy]
      _ = -(mu • B (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ y)) := by
        abel
  simpa only [hdiff, smul_neg, smul_smul, inv_mul_cancel₀ hmu.ne', one_smul] using hres

private theorem variable_relaxation_backward_forward_normal_form_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (h : ℕ → ℝ)
    (alg : VariableRelaxationBackwardForwardAlgorithm Phi hPhi B mu h) (k : ℕ) :
    alg.y (k + 1) = alg.y k - h k •
      (alg.y k - (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩
        (alg.y k) - mu • B (ERealFunction.scaledProximityOperator Phi hPhi
          ⟨mu, alg.mu_pos⟩ (alg.y k)))) := by
  rw [alg.forward_step k, alg.prox_step k]
  module

private theorem fixed_backward_forward_solution_implies_fixed_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (hmu : 0 < mu) (z : H)
    (hz : -B z ∈ ERealFunction.subdifferential Phi z) :
    ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
      (z - mu • B z) = z := by
  rw [eq_comm]
  apply (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
    (f := (⟨mu, hmu⟩ : ERealFunction.PosReal) • Phi)
    (ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu⟩) (z - mu • B z) z).2
  rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
  change (z - mu • B z) - z ∈ (mu : ℝ) • ERealFunction.subdifferential Phi z
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hmu.ne']
  have hrewrite : (mu : ℝ)⁻¹ • ((z - mu • B z) - z) = -B z := by
    calc
      (mu : ℝ)⁻¹ • ((z - mu • B z) - z) = (mu : ℝ)⁻¹ • (-(mu • B z)) := by
        congr 1
        module
      _ = -(((mu : ℝ)⁻¹ * mu) • (B z)) := by
        rw [smul_neg, smul_smul]
      _ = -B z := by
        rw [mul_smul, inv_smul_smul₀ hmu.ne']
  rwa [hrewrite]

private theorem forward_step_lipschitz_one_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (beta mu : ℝ) (hmu : 0 < mu ∧ mu < 2 * beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)) :
    LipschitzWith 1 (fun x : H ↦ x - mu • B x) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hBxy' : beta * ‖B x - B y‖ ^ 2 ≤ inner ℝ (x - y) (B x - B y) := by
    simpa using hB.ineq ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩
  have hsq : ‖(x - y) - mu • (B x - B y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hmu.1]
    have hinner : 2 * mu * beta * ‖B x - B y‖ ^ 2 ≤
        2 * mu * inner ℝ (x - y) (B x - B y) := by
      calc
        2 * mu * beta * ‖B x - B y‖ ^ 2 = (2 * mu) *
            (beta * ‖B x - B y‖ ^ 2) := by ring
        _ ≤ (2 * mu) * inner ℝ (x - y) (B x - B y) :=
          mul_le_mul_of_nonneg_left hBxy' (by linarith [hmu.1])
        _ = 2 * mu * inner ℝ (x - y) (B x - B y) := by ring
    have hcoef : 0 ≤ mu * (2 * beta - mu) * ‖B x - B y‖ ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hmu.1) (by linarith)) (sq_nonneg _)
    nlinarith
  rw [show (x - mu • B x) - (y - mu • B y) = (x - y) - mu • (B x - B y) by module]
  simpa using (sq_le_sq₀ (norm_nonneg ((x - y) - mu • (B x - B y)))
    (norm_nonneg (x - y))).mp hsq

private theorem backward_forward_sq_dist_le_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P B : H → H) (beta mu : ℝ) (hmu : 0 < mu ∧ mu < 2 * beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hP : FirmlyNonexpansive P) (p x : H)
    (hp : P p - mu • B (P p) = p) :
    ‖P x - mu • B (P x) - p‖ ^ 2 +
        ((2 * beta - mu) / (2 * beta)) * ‖x - (P x - mu • B (P x))‖ ^ 2 ≤
      ‖x - p‖ ^ 2 := by
  have hbeta : 0 < beta := by nlinarith [hmu.1, hmu.2]
  let a : H := mu • (B (P x) - B (P p))
  let u : H := (x - p) - (P x - P p)
  let r : H := x - (P x - mu • B (P x))
  let q : ℝ := 2 * beta / mu - 1
  have hq : 0 < q := by
    rw [sub_pos]
    exact (lt_div_iff₀ hmu.1).mpr (by linarith)
  have hforward : ‖P x - mu • B (P x) - p‖ ^ 2 + q * ‖a‖ ^ 2 ≤ ‖P x - P p‖ ^ 2 := by
    have hBxp' : beta * ‖B (P x) - B (P p)‖ ^ 2 ≤
        inner ℝ (P x - P p) (B (P x) - B (P p)) := by
      simpa using hB.ineq ⟨P x, Set.mem_univ (P x)⟩ ⟨P p, Set.mem_univ (P p)⟩
    have hqmul : q * (mu * ‖B (P x) - B (P p)‖) ^ 2 =
        (2 * beta * mu - mu ^ 2) * ‖B (P x) - B (P p)‖ ^ 2 := by
      dsimp [q]
      field_simp [hmu.1.ne']
    rw [show P x - mu • B (P x) - p =
        (P x - mu • B (P x)) - (P p - mu • B (P p)) by rw [hp],
      show (P x - mu • B (P x)) - (P p - mu • B (P p)) =
        (P x - P p) - mu • (B (P x) - B (P p)) by module,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hmu.1, hqmul]
    have hinner : 2 * mu * beta * ‖B (P x) - B (P p)‖ ^ 2 ≤
        2 * mu * inner ℝ (P x - P p) (B (P x) - B (P p)) := by
      calc
        2 * mu * beta * ‖B (P x) - B (P p)‖ ^ 2 = (2 * mu) *
            (beta * ‖B (P x) - B (P p)‖ ^ 2) := by ring
        _ ≤ (2 * mu) * inner ℝ (P x - P p) (B (P x) - B (P p)) :=
          mul_le_mul_of_nonneg_left hBxp' (by linarith [hmu.1])
        _ = 2 * mu * inner ℝ (P x - P p) (B (P x) - B (P p)) := by ring
    nlinarith
  have hfirm := (firmlyNonexpansive_iff_norm_sq_le_inner.mp hP) x p
  have hfirm' : ‖P x - P p‖ ^ 2 + ‖u‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
    rw [norm_sub_sq_real (x - p) (P x - P p)]
    nlinarith [show inner ℝ (P x - P p) (x - p) =
      inner ℝ (x - p) (P x - P p) by rw [real_inner_comm]]
  have hdefect : q * ‖a‖ ^ 2 + ‖u‖ ^ 2 ≤
      ‖x - p‖ ^ 2 - ‖P x - mu • B (P x) - p‖ ^ 2 := by
    nlinarith [hforward, hfirm']
  have hweighted := weighted_norm_add_sq_le q 1 hq zero_lt_one a u
  have hr : r = u + a := by
    calc
      r = x - (P p - mu • B (P p)) - (P x - P p) +
          mu • (B (P x) - B (P p)) := by
        dsimp [r]
        module
      _ = u + a := by
        rw [hp]
  have hweighted' : q * ‖r‖ ^ 2 ≤
      (q + 1) * (q * ‖a‖ ^ 2 + ‖u‖ ^ 2) := by
    calc
      q * ‖r‖ ^ 2 = q * 1 * ‖a + u‖ ^ 2 := by rw [hr, add_comm]; ring
      _ ≤ (q + 1) * (q * ‖a‖ ^ 2 + 1 * ‖u‖ ^ 2) := hweighted
      _ = (q + 1) * (q * ‖a‖ ^ 2 + ‖u‖ ^ 2) := by ring
  have hqone : 0 < q + 1 := by linarith
  have hratio : (2 * beta - mu) / (2 * beta) = q / (q + 1) := by
    dsimp [q]
    field_simp [hmu.1.ne', ne_of_gt hbeta]
    ring
  have hresidual : (q / (q + 1)) * ‖r‖ ^ 2 ≤ q * ‖a‖ ^ 2 + ‖u‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hqone).mpr (by nlinarith [hweighted'])
  rw [hratio]
  change ‖P x - mu • B (P x) - p‖ ^ 2 + (q / (q + 1)) * ‖r‖ ^ 2 ≤ _
  nlinarith

private theorem variable_relaxation_distance_and_residual_tendsto_local {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P B : H → H) (beta mu delta eps : ℝ) (h : ℕ → ℝ)
    (hmu : 0 < mu ∧ mu < 2 * beta) (heps : 0 < eps)
    (hdelta : delta = 1 / 2 + min 1 (beta / mu))
    (hsteps : ∀ k, eps ≤ h k ∧ h k ≤ delta - eps)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hP : FirmlyNonexpansive P) (x : ℕ → H)
    (hupdate : ∀ k, x (k + 1) = (1 - h k) • x k +
      h k • (P (x k) - mu • B (P (x k))))
    (p : H) (hp : P p - mu • B (P p) = p) :
    (∃ l : ℝ, Tendsto (fun k ↦ ‖x k - p‖) atTop (nhds l)) ∧
      Tendsto (fun k ↦ x k - (P (x k) - mu • B (P (x k)))) atTop (nhds 0) := by
  let T : H → H := fun z ↦ P z - mu • B (P z)
  let c : ℝ := (2 * beta - mu) / (2 * beta)
  let r : ℕ → H := fun n ↦ x n - T (x n)
  let d : ℕ → ℝ := fun n ↦ ‖x n - p‖ ^ 2
  let e : ℕ → ℝ := fun n ↦ ‖r n‖ ^ 2
  have hbeta : 0 < beta := by nlinarith [hmu.1, hmu.2]
  have hc : 0 < c := div_pos (by linarith) (by positivity)
  have hdelta_le : delta ≤ 1 + c := by
    rw [hdelta]
    by_cases hle : mu ≤ beta
    · rw [min_eq_left ((le_div_iff₀ hmu.1).mpr (by simpa using hle))]
      have hc_half : (1 / 2 : ℝ) ≤ c := by
        dsimp [c]
        apply (le_div_iff₀ (by positivity : 0 < 2 * beta)).2
        nlinarith
      linarith
    · have hlt : beta < mu := lt_of_not_ge hle
      rw [min_eq_right ((div_le_one₀ hmu.1).mpr hlt.le)]
      have hright : 1 + c = (4 * beta - mu) / (2 * beta) := by
        dsimp [c]
        field_simp [hbeta.ne']
        ring
      rw [hright]
      apply (le_div_iff₀ (by positivity : 0 < 2 * beta)).2
      have hprod : 0 ≤ (mu - beta) * (2 * beta - mu) :=
        mul_nonneg (by linarith) (by linarith)
      have hfrac : 2 * beta ^ 2 / mu ≤ 3 * beta - mu := by
        apply (div_le_iff₀ hmu.1).2
        nlinarith
      calc
        (1 / 2 + beta / mu) * (2 * beta) = beta + 2 * beta ^ 2 / mu := by ring
        _ ≤ 4 * beta - mu := by linarith
  have hcoef : ∀ n, eps ^ 2 ≤ h n * (1 + c - h n) := by
    intro n
    rcases hsteps n with ⟨hnlo, hnhi⟩
    rw [pow_two]
    exact mul_le_mul hnlo (by linarith [hdelta_le]) (le_of_lt heps)
      (le_trans (le_of_lt heps) hnlo)
  have hbase : ∀ n, ‖T (x n) - p‖ ^ 2 + c * e n ≤ d n := by
    intro n
    simpa [T, c, e, d] using backward_forward_sq_dist_le_local P B beta mu hmu hB hP p (x n) hp
  have hdecrease : ∀ n, d (n + 1) + h n * (1 + c - h n) * e n ≤ d n := by
    intro n
    have hb := hbase n
    have hrw : T (x n) - p = (x n - p) - r n := by
      dsimp [T, r]
      module
    rw [hrw, norm_sub_sq_real] at hb
    have hinter : (1 + c) * e n ≤ 2 * inner ℝ (x n - p) (r n) := by
      nlinarith
    change ‖x (n + 1) - p‖ ^ 2 + h n * (1 + c - h n) * e n ≤ ‖x n - p‖ ^ 2
    rw [hupdate n]
    have hupdate_rw :
        (1 - h n) • x n + h n • (P (x n) - mu • B (P (x n))) - p =
          (x n - p) - h n • (x n - T (x n)) := by
      dsimp [T]
      module
    rw [hupdate_rw, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by linarith [hsteps n |>.1])]
    rw [mul_pow]
    dsimp [r, e] at hinter ⊢
    have hmult := mul_le_mul_of_nonneg_left hinter (le_trans (le_of_lt heps) (hsteps n).1)
    nlinarith
  have hs : Summable (fun n ↦ eps ^ 2 * e n) := by
    apply ext_cor_1_summable_of_nonneg_le_diff _ d
    · intro n
      exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · intro n
      nlinarith [hdecrease n, hcoef n, sq_nonneg ‖r n‖]
    · intro n
      exact sq_nonneg _
  have hse : Summable e := by
    have hmul := Summable.mul_left (eps ^ 2)⁻¹ hs
    have hrewrite : (fun n ↦ (eps ^ 2)⁻¹ * (eps ^ 2 * e n)) = e := by
      funext n
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 heps.ne'), one_mul]
    exact hrewrite ▸ hmul
  have hrnorm : Tendsto (fun n ↦ ‖r n‖) atTop (nhds 0) := by
    simpa [Function.comp_def, e, Real.sqrt_sq_eq_abs, abs_of_nonneg] using
      (Real.continuous_sqrt.tendsto 0).comp hse.tendsto_atTop_zero
  have hres : Tendsto r atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hrnorm
  have hdanti : Antitone d := by
    apply antitone_nat_of_succ_le
    intro n
    have hn : 0 ≤ h n * (1 + c - h n) := by
      rcases hsteps n with ⟨hnlo, hnhi⟩
      exact mul_nonneg (le_trans (le_of_lt heps) hnlo) (by linarith [hdelta_le])
    nlinarith [hdecrease n, sq_nonneg ‖r n‖]
  have hdbdd : BddBelow (Set.range d) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact sq_nonneg _
  have hdist : Tendsto (fun n ↦ ‖x n - p‖) atTop
      (nhds (Real.sqrt (⨅ n, d n))) := by
    simpa [Function.comp_def, d, Real.sqrt_sq_eq_abs, abs_of_nonneg] using
      (Real.continuous_sqrt.tendsto (⨅ n, d n)).comp (tendsto_atTop_ciInf hdanti hdbdd)
  exact ⟨⟨_, hdist⟩, by simpa [r, T] using hres⟩

private theorem nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → H) (hT : LipschitzWith 1 T) (u : ℕ → H) (z : H)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) atTop
      (nhds (toWeakSpace ℝ H z)))
    (hres : Tendsto (fun n ↦ u n - T (u n)) atTop (nhds 0))
    (hbounded : ∃ C : ℝ, ∀ n, ‖u n - z‖ ≤ C) : T z = z := by
  rcases hbounded with ⟨C, hC⟩
  have hineq : ∀ n, ‖(u n - T (u n)) - (z - T z)‖ ^ 2 ≤
      2 * inner ℝ (u n - z) ((u n - T (u n)) - (z - T z)) := by
    intro n
    have hnonexp : ‖T (u n) - T z‖ ≤ ‖u n - z‖ := by
      simpa [dist_eq_norm] using hT.dist_le_mul (u n) z
    have hsq : ‖T (u n) - T z‖ ^ 2 ≤ ‖u n - z‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnonexp
    have hexpand := norm_sub_sq_real (u n - z) ((u n - T (u n)) - (z - T z))
    rw [show T (u n) - T z = (u n - z) - ((u n - T (u n)) - (z - T z)) by abel,
      hexpand] at hsq
    nlinarith
  have hleft : Tendsto (fun n ↦ ‖(u n - T (u n)) - (z - T z)‖ ^ 2) atTop
      (nhds (‖z - T z‖ ^ 2)) := by
    simpa only [zero_sub, norm_neg] using (hres.sub tendsto_const_nhds).norm.pow 2
  have hfixed : Tendsto (fun n ↦ inner ℝ (u n - z) (-(z - T z))) atTop (nhds 0) := by
    have hinner := (weakConvergence_iff_forall_tendsto_inner_right u z).1 hweak
      (-(z - T z))
    have hsub := hinner.sub (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ inner ℝ z (-(z - T z))) atTop (nhds (inner ℝ z (-(z - T z)))))
    simpa [inner_sub_left] using hsub
  have hsecond_abs : Tendsto (fun n ↦ |inner ℝ (u n - z) (u n - T (u n))|) atTop
      (nhds 0) := by
    refine squeeze_zero' (f := fun n ↦ |inner ℝ (u n - z) (u n - T (u n))|)
      (g := fun n ↦ C * ‖u n - T (u n)‖)
      (Filter.Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with n
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using hres.norm.const_mul C
  have hsecond : Tendsto (fun n ↦ inner ℝ (u n - z) (u n - T (u n))) atTop
      (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa using hsecond_abs
  have hright : Tendsto
      (fun n ↦ 2 * inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) atTop
      (nhds 0) := by
    have hsplit : (fun n ↦ inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) =
        fun n ↦ inner ℝ (u n - z) (-(z - T z)) + inner ℝ (u n - z) (u n - T (u n)) := by
      funext n
      rw [show ((u n - T (u n)) - (z - T z)) =
        (-(z - T z)) + (u n - T (u n)) by abel, inner_add_right]
    have hinner : Tendsto
        (fun n ↦ inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) atTop (nhds 0) := by
      simpa [hsplit] using hfixed.add hsecond
    simpa using hinner.const_mul 2
  have hnonpos : ‖z - T z‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hineq)
  have hzero : z - T z = 0 :=
    norm_eq_zero.mp (eq_zero_of_pow_eq_zero (le_antisymm hnonpos (sq_nonneg _)))
  exact (sub_eq_zero.mp hzero).symm

/-- Remark 3.3: varying relaxation parameters preserve weak convergence of BF iterates. -/
theorem variable_relaxation_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu : ℝ) (h : ℕ → ℝ) (beta delta eps : ℝ)
    (alg : VariableRelaxationBackwardForwardAlgorithm Phi hPhi B mu h)
    (heps : 0 < eps) (hsteps : ∀ k, eps ≤ h k ∧ h k ≤ delta - eps)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hdelta : delta = 1 / 2 + min 1 (beta / mu))
    (hS : S.Nonempty)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    :
    ∃ ybar, ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩ ybar ∈ S ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (alg.y k)) atTop
        (nhds (toWeakSpace ℝ H ybar)) := by
  let P : H → H := ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
  let T : H → H := fun y ↦ P y - mu • B (P y)
  have hP : FirmlyNonexpansive P := by
    simpa [P, ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
        (ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu.1⟩)
  have hTlip : LipschitzWith 1 T := by
    simpa [T, P, Function.comp_def] using
      (forward_step_lipschitz_one_local B beta mu hmu hB).comp
        (lipschitzWith_one_of_firmlyNonexpansive hP)
  have hC : (Function.fixedPoints T).Nonempty := by
    rcases hS with ⟨z, hz⟩
    refine ⟨z - mu • B z, ?_⟩
    have hzfix := fixed_backward_forward_solution_implies_fixed_local Phi hPhi B mu hmu.1 z
      ((hsolution z).1 hz)
    change T (z - mu • B z) = z - mu • B z
    dsimp [T, P]
    rw [hzfix]
  have hC₀ := hC
  obtain ⟨p₀, hp₀⟩ := hC₀
  have hupdate : ∀ n, alg.y (n + 1) = (1 - h n) • alg.y n + h n •
      (P (alg.y n) - mu • B (P (alg.y n))) := by
    intro n
    rw [alg.forward_step n, alg.prox_step n]
  have hseq₀ := variable_relaxation_distance_and_residual_tendsto_local
    P B beta mu delta eps h hmu heps hdelta hsteps hB hP alg.y hupdate p₀
    (by simpa [T] using hp₀)
  have hbounded : Bornology.IsBounded (Set.range alg.y) :=
    bounded_range_of_convergent_distance_to_point hseq₀.1
  have hdist : ∀ z ∈ Function.fixedPoints T, ∃ l : ℝ,
      Tendsto (fun n ↦ ‖alg.y n - z‖) atTop (nhds l) := by
    intro z hz
    exact (variable_relaxation_distance_and_residual_tendsto_local
      P B beta mu delta eps h hmu heps hdelta hsteps hB hP alg.y hupdate z
      (by simpa [T] using hz)).1
  have hcluster : ∀ z : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (alg.y n))
        (toWeakSpace ℝ H z) → z ∈ Function.fixedPoints T := by
    intro z hz
    rcases hz with ⟨phi, hphi, hphiweak⟩
    have hres : Tendsto (fun n ↦ alg.y (phi n) - T (alg.y (phi n))) atTop (nhds 0) := by
      simpa [T] using hseq₀.2.comp hphi.tendsto_atTop
    rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C, hCbound⟩
    have hsubbound : ∃ K : ℝ, ∀ n, ‖alg.y (phi n) - z‖ ≤ K := by
      refine ⟨C + ‖z‖, ?_⟩
      intro n
      calc
        ‖alg.y (phi n) - z‖ ≤ ‖alg.y (phi n)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ C + ‖z‖ := add_le_add (hCbound _ (Set.mem_range_self (phi n))) le_rfl
    have hphiweak' : Tendsto (fun n ↦ toWeakSpace ℝ H (alg.y (phi n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      simpa [Function.comp_def] using hphiweak
    exact nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local T hTlip
      (fun n ↦ alg.y (phi n)) z hphiweak' hres hsubbound
  rcases opial_lemma hC alg.y hdist hcluster with ⟨ybar, hybar, hyweak⟩
  exact ⟨ybar, fixed_backward_forward_prox_mem_solution_local Phi hPhi S B mu hmu.1
    hsolution ybar (by simpa [T, P] using hybar), hyweak⟩

end AbbasDynamical2015
