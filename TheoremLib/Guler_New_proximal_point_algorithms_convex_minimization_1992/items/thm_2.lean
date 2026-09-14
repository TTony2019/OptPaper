import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.cor_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_4

private theorem proximal_point_center_succ {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (alg : ProximalPointAlgorithm f) :
    ∀ i, alg.nu (i + 1) = alg.nu i -
      (alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
        (alg.y i - alg.x (i + 1)) := by
  intro i
  have hcurvpos : ∀ n, 0 < alg.curvature n := by
    intro n
    induction n with
    | zero => simpa [alg.initial_curvature] using alg.A_pos
    | succ n ih =>
        rw [alg.curvature_step]
        exact mul_pos (sub_pos.mpr (alg.alpha_mem n).2) ih
  have hαsq : 0 < alg.alpha i ^ 2 := by
    rw [alg.alpha_eq]
    exact mul_pos (mul_pos (sub_pos.mpr (alg.alpha_mem i).2) (hcurvpos i))
      (alg.lam_pos i)
  have hαne : alg.alpha i ≠ 0 := by
    intro h
    simp [h] at hαsq
  have hdenne : alg.curvature (i + 1) * alg.lam i ≠ 0 :=
    ne_of_gt (mul_pos (hcurvpos (i + 1)) (alg.lam_pos i))
  have hrel : alg.alpha i ^ 2 = alg.curvature (i + 1) * alg.lam i := by
    rw [alg.alpha_eq, alg.curvature_step]
  have hinv : 1 / alg.alpha i =
      alg.alpha i / (alg.curvature (i + 1) * alg.lam i) := by
    rw [← hrel]
    field_simp [hαne]
  rw [alg.nu_step, hinv]
  module

private theorem proximal_point_estimate_quadratic_representation {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → ℝ)
    (alg : ProximalPointAlgorithm f) : ∀ i u,
    estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y
      (fun j => alg.x (j + 1)) i u =
    estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y
      (fun j => alg.x (j + 1)) i (alg.nu i) +
      (alg.curvature i / 2) * ‖u - alg.nu i‖ ^ 2 := by
  let φ := estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y
    (fun j => alg.x (j + 1))
  have hcenter := proximal_point_center_succ f alg
  have hcurvpos : ∀ n, 0 < alg.curvature n := by
    intro n
    induction n with
    | zero => simpa [alg.initial_curvature] using alg.A_pos
    | succ n ih =>
        rw [alg.curvature_step]
        exact mul_pos (sub_pos.mpr (alg.alpha_mem n).2) ih
  intro i
  induction i with
  | zero =>
      intro u
      simp [estimateQuadratic, alg.initial_center, alg.initial_curvature]
  | succ i ih =>
      intro u
      have hrel : alg.alpha i ^ 2 = alg.curvature (i + 1) * alg.lam i := by
        rw [alg.alpha_eq, alg.curvature_step]
      change φ (i + 1) u = φ (i + 1) (alg.nu (i + 1)) +
        (alg.curvature (i + 1) / 2) * ‖u - alg.nu (i + 1)‖ ^ 2
      rw [show φ (i + 1) u =
          (1 - alg.alpha i) * φ i u + alg.alpha i *
            (f (alg.x (i + 1)) + inner ℝ ((1 / alg.lam i) •
              (alg.y i - alg.x (i + 1))) (u - alg.x (i + 1))) by rfl]
      rw [show φ (i + 1) (alg.nu (i + 1)) =
          (1 - alg.alpha i) * φ i (alg.nu (i + 1)) + alg.alpha i *
            (f (alg.x (i + 1)) + inner ℝ ((1 / alg.lam i) •
              (alg.y i - alg.x (i + 1)))
                (alg.nu (i + 1) - alg.x (i + 1))) by rfl]
      have ihu : φ i u = φ i (alg.nu i) +
          (alg.curvature i / 2) * ‖u - alg.nu i‖ ^ 2 := ih u
      have ihν : φ i (alg.nu (i + 1)) = φ i (alg.nu i) +
          (alg.curvature i / 2) * ‖alg.nu (i + 1) - alg.nu i‖ ^ 2 :=
        ih (alg.nu (i + 1))
      rw [ihu, ihν, alg.curvature_step, hcenter i]
      have hden : alg.curvature (i + 1) * alg.lam i ≠ 0 :=
        ne_of_gt (mul_pos (hcurvpos (i + 1)) (alg.lam_pos i))
      have hcurvne : alg.curvature (i + 1) ≠ 0 := ne_of_gt (hcurvpos (i + 1))
      have hlamne : alg.lam i ≠ 0 := ne_of_gt (alg.lam_pos i)
      have hδ : alg.nu i -
          (alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
            (alg.y i - alg.x (i + 1)) - alg.nu i =
          -(alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
            (alg.y i - alg.x (i + 1)) := by
        module
      have huδ : u - (alg.nu i -
          (alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
            (alg.y i - alg.x (i + 1))) =
          (u - alg.nu i) +
            (alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
              (alg.y i - alg.x (i + 1)) := by
        module
      have hνδ : alg.nu i -
          (alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
            (alg.y i - alg.x (i + 1)) - alg.x (i + 1) =
          (alg.nu i - alg.x (i + 1)) -
            (alg.alpha i / (alg.curvature (i + 1) * alg.lam i)) •
              (alg.y i - alg.x (i + 1)) := by
        module
      have hqu : inner ℝ (alg.y i - alg.x (i + 1)) u -
          inner ℝ (alg.y i - alg.x (i + 1)) (alg.x (i + 1)) =
          inner ℝ (alg.y i - alg.x (i + 1)) (u - alg.nu i) +
            inner ℝ (alg.y i - alg.x (i + 1))
              (alg.nu i - alg.x (i + 1)) := by
        rw [inner_sub_right, inner_sub_right]
        ring
      rw [hδ, huδ, hνδ]
      simp_rw [norm_smul, norm_add_sq_real, inner_smul_left, inner_sub_right,
        inner_smul_right]
      simp_rw [norm_smul]
      simp only [Real.norm_eq_abs, real_inner_self_eq_norm_sq,
        starRingEnd_apply, star_trivial]
      rw [hqu]
      field_simp [hden, hcurvne, hlamne]
      repeat' rw [sq_abs]
      have hinner : inner ℝ (u - alg.nu i) (alg.y i - alg.x (i + 1)) =
          inner ℝ (alg.y i - alg.x (i + 1)) (u - alg.nu i) :=
        real_inner_comm _ _
      rw [hinner]
      ring_nf
      field_simp [hcurvne, hlamne]
      ring_nf
      field_simp [hcurvne, hlamne]
      ring_nf
      have hcurvstep : alg.curvature (1 + i) =
          (1 - alg.alpha i) * alg.curvature i := by
        simpa [Nat.add_comm] using alg.curvature_step i
      have hcurvstep' : alg.curvature (i + 1) =
          (1 - alg.alpha i) * alg.curvature i := alg.curvature_step i
      have hcurvine : alg.curvature i ≠ 0 := ne_of_gt (hcurvpos i)
      have hαsubne : 1 - alg.alpha i ≠ 0 :=
        ne_of_gt (sub_pos.mpr (alg.alpha_mem i).2)
      field_simp [hcurvine, hαsubne]
      have hrel' : alg.alpha i ^ 2 =
          (1 - alg.alpha i) * alg.curvature i * alg.lam i := by
        rw [hrel, hcurvstep']
      rw [show alg.alpha i ^ 3 = alg.alpha i * (alg.alpha i ^ 2) by ring]
      simp_rw [hrel']
      field_simp [hcurvne]
      simp only [hcurvstep]
      field_simp [hcurvine, hαsubne]
      try simp_rw [hrel']
      simp only [inner_sub_right]
      ring

/-- Theorem 2.2: the global rate estimate for the proximal point algorithm.

The displayed rate with the upper bound on `beta_k` is obtained by multiplying
that bound by the initial certificate.  We therefore make explicit the sign
condition used in this step (`hC`).  Without it, the estimate-sequence argument
still gives the exact bound with `betaSequence`, but replacing `betaSequence` by
an upper bound reverses the inequality when the certificate is negative. -/
theorem proximal_point_global_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ)
    (alg : ProximalPointAlgorithm f) (z : H) (k : ℕ) (hk : 1 ≤ k)
    (hz : IsFeasible (fun x => (f x : EReal)) z)
    (hC : 0 ≤ f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) :
    f (alg.x k) - f z + ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) ≤
      (f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) /
        (1 + (Real.sqrt alg.A / 2) * ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) ^ 2 := by
  have hz' : (f z : EReal) < ⊤ := hz
  clear hz'
  let β : ℕ → ℝ := betaSequence alg.alpha
  have hcurv : ∀ i, alg.curvature i = β i * alg.A := by
    intro i
    induction i with
    | zero => simp [β, betaSequence, alg.initial_curvature]
    | succ i ih =>
        rw [alg.curvature_step, ih]
        simp only [β, betaSequence, Finset.prod_range_succ]
        ring
  have hrec : ∀ i, alg.alpha i ^ 2 =
      (1 - alg.alpha i) * alg.A * β i * alg.lam i := by
    intro i
    rw [alg.alpha_eq, hcurv]
    ring
  have hcurvpos : ∀ i, 0 < alg.curvature i := by
    intro i
    induction i with
    | zero => simpa [alg.initial_curvature] using alg.A_pos
    | succ i ih =>
        rw [alg.curvature_step]
        exact mul_pos (sub_pos.mpr (alg.alpha_mem i).2) ih
  have hαIoc : ∀ i, alg.alpha i ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    have hi := hrec i
    have hright : 0 < (1 - alg.alpha i) * alg.A * β i * alg.lam i := by
      calc
        (1 - alg.alpha i) * alg.A * β i * alg.lam i =
            (1 - alg.alpha i) * alg.curvature i * alg.lam i := by
              rw [hcurv i]
              ring
        _ > 0 := mul_pos (mul_pos (sub_pos.mpr (alg.alpha_mem i).2) (hcurvpos i))
          (alg.lam_pos i)
    constructor
    · have hsq : 0 < alg.alpha i ^ 2 := by rw [hi]; exact hright
      exact lt_of_le_of_ne (alg.alpha_mem i).1 (Ne.symm (sq_pos_iff.mp hsq))
    · exact le_of_lt (alg.alpha_mem i).2
  have hβupper : β k ≤
      1 / (1 + (Real.sqrt alg.A / 2) *
        ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) ^ 2 := by
    simpa [β] using
      (betaSequence_bounds alg.A alg.A_pos alg.lam alg.alpha k hαIoc alg.lam_pos
        (by simpa [β] using hrec)).2
  -- In (2.7) the proximal point at update `i` is `x (i + 1)`.
  let φ := estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y
    (fun i => alg.x (i + 1))
  have hstep : ∀ i u, φ (i + 1) u - f u ≤
      (1 - alg.alpha i) * (φ i u - f u) := by
    intro i u
    simpa [φ] using
      estimateQuadratic_step_le f alg.A (alg.x 0) alg.alpha alg.lam alg.y
        (fun i => alg.x (i + 1))
        alg.f_convex alg.alpha_mem alg.x_step i u
  have hbeta : φ k z - f z ≤ β k * (φ 0 z - f z) := by
    simpa [β] using betaSequence_estimate alg.alpha φ f hstep alg.alpha_mem k z
  have hinitial : φ 0 z - f z =
      f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2 := by
    simp [φ, estimateQuadratic]
    ring
  have hbeta_initial : φ k z - f z ≤ β k *
      (f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) := by
    rw [← hinitial]
    exact hbeta
  have hcenter := proximal_point_center_succ f alg
  have hquad := proximal_point_estimate_quadratic_representation f alg
  let params : EstimateQuadraticParameters := {
    A := alg.A
    alpha := alg.alpha
    lam := alg.lam
    y := alg.y
    p := fun i => alg.x (i + 1)
    nu := alg.nu
    curvature := alg.curvature
    phi := φ
    phi_star := fun i => φ i (alg.nu i)
    curvature_zero := alg.initial_curvature
    curvature_succ := alg.curvature_step
    curvature_eq_beta := hcurv
    quadratic_representation := by
      intro i u
      exact hquad i u
    center_minimizes := by
      intro i u
      change estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y
        (fun j => alg.x (j + 1)) i (alg.nu i) ≤
        estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y
          (fun j => alg.x (j + 1)) i u
      rw [hquad i u]
      exact le_add_of_nonneg_right (mul_nonneg (by linarith [hcurvpos i]) (sq_nonneg _))
    center_succ := hcenter }
  have hupdate : ∀ i u, params.phi (i + 1) u =
      (1 - params.alpha i) * params.phi i u + params.alpha i *
        (f (params.p i) + inner ℝ ((1 / params.lam i) •
          (params.y i - params.p i)) (u - params.p i)) := by
    intro i u
    rfl
  have hstar : ∀ i, f (alg.x i) ≤ params.phi_star i := by
    intro i
    induction i with
    | zero =>
        change f (alg.x 0) ≤ φ 0 (alg.nu 0)
        simp [φ, estimateQuadratic, alg.initial_center]
    | succ i ih =>
        have hαeq : alg.alpha i ^ 2 =
            params.curvature (i + 1) * params.lam i := by
          change alg.alpha i ^ 2 = alg.curvature (i + 1) * alg.lam i
          rw [alg.alpha_eq, alg.curvature_step]
        have hbound := estimateQuadratic_minimum_lower_bound_choice f params i (alg.x i)
          alg.f_convex (alg.lam_pos i) (alg.alpha_mem i) (hcurvpos (i + 1)) ih
          (alg.x_step i) (hupdate i) (alg.y_step i)
        exact (tuned_proximal_step_bound f (x := alg.x i) (ν := alg.nu i)
          (y := alg.y i) (xnext := alg.x (i + 1)) (lam := alg.lam i)
          (A_next := alg.curvature (i + 1)) (φnext := params.phi_star (i + 1))
          (α := alg.alpha i) (alg.lam_pos i) (hcurvpos (i + 1))
          (alg.y_step i) hαeq (alg.x_step i) hbound).2.trans
            (tuned_proximal_step_bound f (x := alg.x i) (ν := alg.nu i)
              (y := alg.y i) (xnext := alg.x (i + 1)) (lam := alg.lam i)
              (A_next := alg.curvature (i + 1)) (φnext := params.phi_star (i + 1))
              (α := alg.alpha i) (alg.lam_pos i) (hcurvpos (i + 1))
              (alg.y_step i) hαeq (alg.x_step i) hbound).1
  have hstar_res : ∀ i, params.phi_star (i + 1) ≥ f (alg.x (i + 1)) +
      ‖alg.y i - alg.x (i + 1)‖ ^ 2 / (2 * alg.lam i) := by
    intro i
    have hαeq : alg.alpha i ^ 2 =
        params.curvature (i + 1) * params.lam i := by
      change alg.alpha i ^ 2 = alg.curvature (i + 1) * alg.lam i
      rw [alg.alpha_eq, alg.curvature_step]
    have hbound := estimateQuadratic_minimum_lower_bound_choice f params i (alg.x i)
      alg.f_convex (alg.lam_pos i) (alg.alpha_mem i) (hcurvpos (i + 1)) (hstar i)
      (alg.x_step i) (hupdate i) (alg.y_step i)
    exact (tuned_proximal_step_bound f (x := alg.x i) (ν := alg.nu i)
      (y := alg.y i) (xnext := alg.x (i + 1)) (lam := alg.lam i)
      (A_next := alg.curvature (i + 1)) (φnext := params.phi_star (i + 1))
      (α := alg.alpha i) (alg.lam_pos i) (hcurvpos (i + 1))
      (alg.y_step i) hαeq (alg.x_step i) hbound).1
  have hleft : f (alg.x k) - f z +
      ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) ≤ φ k z - f z := by
    have hres := hstar_res (k - 1)
    rw [Nat.sub_add_cancel hk] at hres
    have hmin := params.center_minimizes k z
    have hsum : f (alg.x k) +
        ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) ≤ φ k z :=
      hres.trans hmin
    linarith
  have hrate : f (alg.x k) - f z +
      ‖alg.y (k - 1) - alg.x k‖ ^ 2 / (2 * alg.lam (k - 1)) ≤ β k *
        (f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) :=
    hleft.trans hbeta_initial
  calc
    f (alg.x k) - f z + ‖alg.y (k - 1) - alg.x k‖ ^ 2 /
        (2 * alg.lam (k - 1)) ≤ β k *
          (f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) := hrate
    _ ≤ (1 / (1 + (Real.sqrt alg.A / 2) *
        ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) ^ 2) *
          (f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hβupper hC
    _ = (f (alg.x 0) - f z + (alg.A / 2) * ‖z - alg.x 0‖ ^ 2) /
        (1 + (Real.sqrt alg.A / 2) *
          ∑ j ∈ Finset.range k, Real.sqrt (alg.lam j)) ^ 2 := by
      simp only [div_eq_mul_inv]
      ring
