import Mathlib
import Foundation.FixedPoint.Nonexpansive
import Foundation.Convex.Subdifferential
import Foundation.Hilbert.WeakConvergence

namespace AbbasDynamical2015

open scoped Pointwise

/-- Relaxed forward-backward algorithm (106). -/
structure RelaxedForwardBackwardAlgorithm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu h : ℝ) where
  mu_pos : 0 < mu
  h_pos : 0 < h
  x : ℕ → H
  update : ∀ k, x (k + 1) =
    (1 - h) • x k + h • ERealFunction.scaledProximityOperator Phi hPhi
      ⟨mu, mu_pos⟩ (x k - mu • B (x k))

private theorem scaled_forward_backward_fixed_implies_solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (hmu : 0 < mu) (z : H)
    (hz : ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
      (z - mu • B z) = z) :
    -B z ∈ ERealFunction.subdifferential Phi z := by
  have hres := ERealFunction.scaledProximityOperator_residual_mem hPhi ⟨mu, hmu⟩
    (z - mu • B z)
  rw [hz] at hres
  have hrewrite : (mu : ℝ)⁻¹ • ((z - mu • B z) - z) = -B z := by
    calc
      (mu : ℝ)⁻¹ • ((z - mu • B z) - z) = (mu : ℝ)⁻¹ • (-(mu • B z)) := by
        congr 1
        module
      _ = -(((mu : ℝ)⁻¹ * mu) • (B z)) := by
        rw [smul_neg, smul_smul]
      _ = -B z := by
        rw [mul_smul, inv_smul_smul₀ hmu.ne']
  rw [hrewrite] at hres
  exact hres

private theorem scaled_forward_backward_solution_implies_fixed
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
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

private theorem forward_step_lipschitz_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
    have hbeta : 0 < beta := by nlinarith [hmu.1, hmu.2]
    have hinner : 2 * mu * beta * ‖B x - B y‖ ^ 2 ≤
        2 * mu * inner ℝ (x - y) (B x - B y) := by
      calc
        2 * mu * beta * ‖B x - B y‖ ^ 2 = (2 * mu) *
            (beta * ‖B x - B y‖ ^ 2) := by ring
        _ ≤ (2 * mu) * inner ℝ (x - y) (B x - B y) := by
          exact mul_le_mul_of_nonneg_left hBxy' (by linarith [hmu.1])
        _ = 2 * mu * inner ℝ (x - y) (B x - B y) := by ring
    have hcoef : 0 ≤ mu * (2 * beta - mu) * ‖B x - B y‖ ^ 2 := by
      exact mul_nonneg (mul_nonneg (le_of_lt hmu.1) (by linarith)) (sq_nonneg _)
    nlinarith
  rw [show (x - mu • B x) - (y - mu • B y) = (x - y) - mu • (B x - B y) by module]
  simpa using (sq_le_sq₀ (norm_nonneg ((x - y) - mu • (B x - B y)))
    (norm_nonneg (x - y))).mp hsq

private theorem forward_backward_sq_dist_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P B : H → H) (beta mu : ℝ) (hmu : 0 < mu ∧ mu < 2 * beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hP : FirmlyNonexpansive P) (p x : H)
    (hp : P (p - mu • B p) = p) :
    ‖P (x - mu • B x) - p‖ ^ 2 +
        ((2 * beta - mu) / (2 * beta)) * ‖x - P (x - mu • B x)‖ ^ 2 ≤
      ‖x - p‖ ^ 2 := by
  have hbeta : 0 < beta := by nlinarith [hmu.1, hmu.2]
  let a : H := mu • (B x - B p)
  let r : H := x - P (x - mu • B x)
  let q : ℝ := 2 * beta / mu - 1
  have hq : 0 < q := by
    dsimp [q]
    rw [sub_pos]
    exact (lt_div_iff₀ hmu.1).mpr (by linarith)
  have hforward : ‖(x - mu • B x) - (p - mu • B p)‖ ^ 2 ≤
      ‖x - p‖ ^ 2 - q * ‖a‖ ^ 2 := by
    have hBxp' : beta * ‖B x - B p‖ ^ 2 ≤ inner ℝ (x - p) (B x - B p) := by
      simpa using hB.ineq ⟨x, Set.mem_univ x⟩ ⟨p, Set.mem_univ p⟩
    have hqmul : q * (mu * ‖B x - B p‖) ^ 2 =
        (2 * beta * mu - mu ^ 2) * ‖B x - B p‖ ^ 2 := by
      dsimp [q]
      field_simp [hmu.1.ne']
    rw [show (x - mu • B x) - (p - mu • B p) = (x - p) - mu • (B x - B p) by module,
      norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hmu.1, hqmul]
    have hinner : 2 * mu * beta * ‖B x - B p‖ ^ 2 ≤
        2 * mu * inner ℝ (x - p) (B x - B p) := by
      calc
        2 * mu * beta * ‖B x - B p‖ ^ 2 = (2 * mu) *
            (beta * ‖B x - B p‖ ^ 2) := by ring
        _ ≤ (2 * mu) * inner ℝ (x - p) (B x - B p) := by
          exact mul_le_mul_of_nonneg_left hBxp' (by linarith [hmu.1])
        _ = 2 * mu * inner ℝ (x - p) (B x - B p) := by ring
    nlinarith
  have hfirm := (firmlyNonexpansive_iff_norm_sq_le_inner.mp hP)
    (x - mu • B x) (p - mu • B p)
  have hfirm' : ‖P (x - mu • B x) - p‖ ^ 2 + ‖r - a‖ ^ 2 ≤
      ‖(x - mu • B x) - (p - mu • B p)‖ ^ 2 := by
    have hpre : ‖P (x - mu • B x) - P (p - mu • B p)‖ ^ 2 +
        ‖(x - mu • B x) - (p - mu • B p) -
          (P (x - mu • B x) - P (p - mu • B p))‖ ^ 2 ≤
        ‖(x - mu • B x) - (p - mu • B p)‖ ^ 2 := by
      have hsquare := norm_sub_sq_real
        ((x - mu • B x) - (p - mu • B p))
        (P (x - mu • B x) - P (p - mu • B p))
      rw [hsquare]
      nlinarith [show inner ℝ (P (x - mu • B x) - P (p - mu • B p))
        ((x - mu • B x) - (p - mu • B p)) =
        inner ℝ ((x - mu • B x) - (p - mu • B p))
          (P (x - mu • B x) - P (p - mu • B p)) by rw [real_inner_comm]]
    rw [hp] at hpre
    have hdiff : (x - mu • B x) - (p - mu • B p) -
        (P (x - mu • B x) - p) = r - a := by
      dsimp [r, a]
      module
    rw [hdiff] at hpre
    exact hpre
  have hdefect : q * ‖a‖ ^ 2 + ‖r - a‖ ^ 2 ≤
      ‖x - p‖ ^ 2 - ‖P (x - mu • B x) - p‖ ^ 2 := by
    nlinarith [hforward, hfirm']
  have hweighted := weighted_norm_add_sq_le q 1 hq zero_lt_one a (r - a)
  have hr : r = a + (r - a) := by module
  have hweighted' : q * ‖r‖ ^ 2 ≤
      (q + 1) * (q * ‖a‖ ^ 2 + ‖r - a‖ ^ 2) := by
    calc
      q * ‖r‖ ^ 2 = q * 1 * ‖a + (r - a)‖ ^ 2 := by rw [← hr]; ring
      _ ≤ (q + 1) * (q * ‖a‖ ^ 2 + 1 * ‖r - a‖ ^ 2) := hweighted
      _ = (q + 1) * (q * ‖a‖ ^ 2 + ‖r - a‖ ^ 2) := by ring
  have hqone : 0 < q + 1 := by linarith
  have hratio : (2 * beta - mu) / (2 * beta) = q / (q + 1) := by
    dsimp [q]
    field_simp [hmu.1.ne', ne_of_gt hbeta]
    ring
  have hresidual : (q / (q + 1)) * ‖r‖ ^ 2 ≤ q * ‖a‖ ^ 2 + ‖r - a‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hqone).mpr (by nlinarith [hweighted'])
  rw [hratio]
  change ‖P (x - mu • B x) - p‖ ^ 2 + (q / (q + 1)) * ‖r‖ ^ 2 ≤ _
  nlinarith

private theorem forward_backward_distance_and_residual_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (P B : H → H) (beta mu h : ℝ) (hmu : 0 < mu ∧ mu < 2 * beta)
    (hh : 0 < h ∧ h ≤ 1)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hP : FirmlyNonexpansive P) (x : ℕ → H)
    (hupdate : ∀ n, x (n + 1) = (1 - h) • x n + h • P (x n - mu • B (x n)))
    (p : H) (hp : P (p - mu • B p) = p) :
    (∃ l : ℝ, Filter.Tendsto (fun n ↦ ‖x n - p‖) Filter.atTop (nhds l)) ∧
      Filter.Tendsto (fun n ↦ x n - P (x n - mu • B (x n))) Filter.atTop (nhds 0) := by
  let T : H → H := fun z ↦ P (z - mu • B z)
  let c : ℝ := (2 * beta - mu) / (2 * beta)
  let r : ℕ → H := fun n ↦ x n - T (x n)
  let d : ℕ → ℝ := fun n ↦ ‖x n - p‖ ^ 2
  let e : ℕ → ℝ := fun n ↦ ‖r n‖ ^ 2
  have hbeta : 0 < beta := by nlinarith [hmu.1, hmu.2]
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by positivity)
  have hk : 0 < h * (1 + c - h) := by
    exact mul_pos hh.1 (by nlinarith [hh.2, hc])
  have hbase : ∀ n, ‖T (x n) - p‖ ^ 2 + c * e n ≤ d n := by
    intro n
    simpa [T, c, e, d] using
      forward_backward_sq_dist_le P B beta mu hmu hB hP p (x n) hp
  have hdecrease : ∀ n, d (n + 1) + h * (1 + c - h) * e n ≤ d n := by
    intro n
    have hb := hbase n
    have hrw : T (x n) - p = (x n - p) - r n := by
      dsimp [T, r]
      module
    rw [hrw, norm_sub_sq_real] at hb
    have hinter : (1 + c) * e n ≤ 2 * inner ℝ (x n - p) (r n) := by
      nlinarith
    change ‖x (n + 1) - p‖ ^ 2 + h * (1 + c - h) * e n ≤ ‖x n - p‖ ^ 2
    rw [hupdate n]
    have hupdate_rw :
        (1 - h) • x n + h • P (x n - mu • B (x n)) - p =
          (x n - p) - h • (x n - T (x n)) := by
      dsimp [T]
      module
    rw [hupdate_rw, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hh.1]
    dsimp [r] at hinter ⊢
    nlinarith
  have hs : Summable (fun n ↦ h * (1 + c - h) * e n) := by
    apply ext_cor_1_summable_of_nonneg_le_diff _ d
    · intro n
      exact mul_nonneg (le_of_lt hk) (sq_nonneg _)
    · intro n
      linarith [hdecrease n]
    · intro n
      exact sq_nonneg _
  have hse : Summable e := by
    have hmul := Summable.mul_left (h * (1 + c - h))⁻¹ hs
    have hrewrite : (fun n ↦ (h * (1 + c - h))⁻¹ *
        (h * (1 + c - h) * e n)) = e := by
      funext n
      rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
    rw [hrewrite] at hmul
    exact hmul
  have hezero : Filter.Tendsto e Filter.atTop (nhds 0) := hse.tendsto_atTop_zero
  have hrnorm : Filter.Tendsto (fun n ↦ ‖r n‖) Filter.atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hezero
    simpa [Function.comp_def, e, Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
  have hres : Filter.Tendsto r Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hrnorm
  have hdanti : Antitone d := by
    apply antitone_nat_of_succ_le
    intro n
    have := hdecrease n
    have he : 0 ≤ e n := sq_nonneg _
    nlinarith
  have hdbdd : BddBelow (Set.range d) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact sq_nonneg _
  have hdtend : Filter.Tendsto d Filter.atTop (nhds (⨅ n, d n)) :=
    tendsto_atTop_ciInf hdanti hdbdd
  have hdist : Filter.Tendsto (fun n ↦ ‖x n - p‖) Filter.atTop
      (nhds (Real.sqrt (⨅ n, d n))) := by
    have hsqrt := (Real.continuous_sqrt.tendsto (⨅ n, d n)).comp hdtend
    simpa [Function.comp_def, d, Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
  exact ⟨⟨_, hdist⟩, by simpa [r, T] using hres⟩

private theorem nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → H) (hT : LipschitzWith 1 T) (u : ℕ → H) (z : H)
    (hweak : Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (u n)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)))
    (hres : Filter.Tendsto (fun n ↦ u n - T (u n)) Filter.atTop (nhds 0))
    (hbounded : ∃ C : ℝ, ∀ n, ‖u n - z‖ ≤ C) : T z = z := by
  rcases hbounded with ⟨C, hC⟩
  have hineq : ∀ n, ‖(u n - T (u n)) - (z - T z)‖ ^ 2 ≤
      2 * inner ℝ (u n - z) ((u n - T (u n)) - (z - T z)) := by
    intro n
    have hnonexp : ‖T (u n) - T z‖ ≤ ‖u n - z‖ := by
      simpa [dist_eq_norm] using hT.dist_le_mul (u n) z
    have hsq : ‖T (u n) - T z‖ ^ 2 ≤ ‖u n - z‖ ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnonexp
    have hexpand := norm_sub_sq_real (u n - z) ((u n - T (u n)) - (z - T z))
    rw [show T (u n) - T z = (u n - z) - ((u n - T (u n)) - (z - T z)) by abel,
      hexpand] at hsq
    nlinarith
  have hleft : Filter.Tendsto
      (fun n ↦ ‖(u n - T (u n)) - (z - T z)‖ ^ 2) Filter.atTop
      (nhds (‖z - T z‖ ^ 2)) := by
    have hdiff : Filter.Tendsto
        (fun n ↦ (u n - T (u n)) - (z - T z)) Filter.atTop
        (nhds (0 - (z - T z))) := hres.sub tendsto_const_nhds
    simpa only [zero_sub, norm_neg] using hdiff.norm.pow 2
  have hfixed : Filter.Tendsto (fun n ↦ inner ℝ (u n - z) (-(z - T z)))
      Filter.atTop (nhds 0) := by
    have hinner := (weakConvergence_iff_forall_tendsto_inner_right u z).1 hweak
      (-(z - T z))
    have hsub := hinner.sub
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ ↦ inner ℝ z (-(z - T z))) Filter.atTop
        (nhds (inner ℝ z (-(z - T z)))))
    simpa [inner_sub_left] using hsub
  have hsecond_abs : Filter.Tendsto
      (fun n ↦ |inner ℝ (u n - z) (u n - T (u n))|) Filter.atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n ↦ |inner ℝ (u n - z) (u n - T (u n))|)
      (g := fun n ↦ C * ‖u n - T (u n)‖)
      (Filter.Eventually.of_forall fun n ↦ abs_nonneg _) ?_ ?_
    · filter_upwards with n
      exact le_trans (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
    · simpa using hres.norm.const_mul C
  have hsecond : Filter.Tendsto
      (fun n ↦ inner ℝ (u n - z) (u n - T (u n))) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa using hsecond_abs
  have hright : Filter.Tendsto
      (fun n ↦ 2 * inner ℝ (u n - z) ((u n - T (u n)) - (z - T z)))
      Filter.atTop (nhds 0) := by
    have hsplit : (fun n ↦ inner ℝ (u n - z) ((u n - T (u n)) - (z - T z))) =
        fun n ↦ inner ℝ (u n - z) (-(z - T z)) +
          inner ℝ (u n - z) (u n - T (u n)) := by
      funext n
      rw [show ((u n - T (u n)) - (z - T z)) =
        (-(z - T z)) + (u n - T (u n)) by abel, inner_add_right]
    have hinner : Filter.Tendsto
        (fun n ↦ inner ℝ (u n - z) ((u n - T (u n)) - (z - T z)))
        Filter.atTop (nhds 0) := by
      rw [hsplit]
      simpa using hfixed.add hsecond
    simpa using hinner.const_mul 2
  have hnonpos : ‖z - T z‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hineq)
  have hzero : z - T z = 0 := by
    exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero (le_antisymm hnonpos (sq_nonneg _)))
  exact (sub_eq_zero.mp hzero).symm

/-- Under the paper's parameter restrictions, relaxed forward-backward iterates
converge weakly to `S`. -/
theorem relaxed_forward_backward_stepsize_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (mu h beta : ℝ)
    (alg : RelaxedForwardBackwardAlgorithm Phi hPhi B mu h)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hh : 0 < h ∧ h ≤ 1)
    (hS : S.Nonempty)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∃ z ∈ S, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (alg.x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z)) := by
  let T : H → H := fun z ↦ ERealFunction.scaledProximityOperator Phi hPhi
    ⟨mu, alg.mu_pos⟩ (z - mu • B z)
  have hfixed : Function.fixedPoints T = S := by
    ext z
    simp only [Function.mem_fixedPoints, Function.IsFixedPt]
    constructor
    · intro hz
      exact (hsolution z).2 (scaled_forward_backward_fixed_implies_solution Phi hPhi B mu
        alg.mu_pos z (by simpa [T] using hz))
    · intro hz
      exact scaled_forward_backward_solution_implies_fixed Phi hPhi B mu alg.mu_pos z
        ((hsolution z).1 hz)
  have hP : FirmlyNonexpansive
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩) := by
    have hg := ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, alg.mu_pos⟩
    simpa [ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero hg
  have hF : LipschitzWith 1 (fun z : H ↦ z - mu • B z) :=
    forward_step_lipschitz_one B beta mu hmu hB
  have hTlip : LipschitzWith 1 T := by
    have hPlip := lipschitzWith_one_of_firmlyNonexpansive hP
    simpa [T, Function.comp_def] using hPlip.comp hF
  have hC : (Function.fixedPoints T).Nonempty := by rwa [hfixed]
  obtain ⟨p₀, hp₀⟩ := hC
  have hp₀eq : T p₀ = p₀ := hp₀
  have hseq₀ := forward_backward_distance_and_residual_tendsto
    (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩) B beta mu h
    hmu hh hB hP alg.x alg.update p₀ (by simpa [T] using hp₀eq)
  have hbounded : Bornology.IsBounded (Set.range alg.x) :=
    bounded_range_of_convergent_distance_to_point hseq₀.1
  have hdist : ∀ z ∈ Function.fixedPoints T, ∃ l : ℝ,
      Filter.Tendsto (fun n ↦ ‖alg.x n - z‖) Filter.atTop (nhds l) := by
    intro z hz
    exact (forward_backward_distance_and_residual_tendsto
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩) B beta mu h
      hmu hh hB hP alg.x alg.update z (by simpa [T] using hz)).1
  have hcluster : ∀ z : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (alg.x n))
        (toWeakSpace ℝ H z) → z ∈ Function.fixedPoints T := by
    intro z hz
    rcases hz with ⟨phi, hphi, hphiweak⟩
    have hres : Filter.Tendsto (fun n ↦ alg.x (phi n) - T (alg.x (phi n)))
        Filter.atTop (nhds 0) := by
      simpa [T] using hseq₀.2.comp hphi.tendsto_atTop
    rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C, hCbound⟩
    have hsubbound : ∃ K : ℝ, ∀ n, ‖alg.x (phi n) - z‖ ≤ K := by
      refine ⟨C + ‖z‖, ?_⟩
      intro n
      calc
        ‖alg.x (phi n) - z‖ ≤ ‖alg.x (phi n)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ C + ‖z‖ := add_le_add (hCbound _ (Set.mem_range_self (phi n))) le_rfl
    have hphiweak' : Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ H (alg.x (phi n))) Filter.atTop
        (nhds (toWeakSpace ℝ H z)) := by
      simpa [Function.comp_def] using hphiweak
    have hfix : T z = z :=
      nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero T hTlip
        (fun n ↦ alg.x (phi n)) z hphiweak' hres hsubbound
    exact hfix
  rcases opial_lemma ⟨p₀, hp₀⟩ alg.x hdist hcluster with ⟨z, hz, hlim⟩
  exact ⟨z, by rwa [← hfixed], hlim⟩

end AbbasDynamical2015
