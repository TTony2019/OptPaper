## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/thm_1.lean`

## Lean statement
```lean
theorem inertial_forward_backward_strong_convergence (A : H → H) (B : SetValuedOperator H H)
    (alpha : ℝ) (hA : CocoerciveOn alpha Set.univ (fun x : Set.univ ↦ A x))
    (hB : B.IsMaximalMonotone) (alg : InertialForwardBackward A B)
    (hInertiaBounded : Bornology.IsBounded (Set.range alg.inertia))
    (hSteps : 0 < liminf alg.stepSize atTop ∧
      liminf alg.stepSize atTop ≤ limsup alg.stepSize atTop ∧
        limsup alg.stepSize atTop < 2 * alpha)
    (hStepLt : ∀ n, 1 ≤ n → alg.stepSize n < 2 * alpha)
    (hInitialOmegaQ : operatorSumZeroSet A B ⊆ inertialForwardBackwardQ alg.x alg.x0 1)
    (hOmega : (operatorSumZeroSet A B).Nonempty)
    (hOmegaChebyshev : IsChebyshev (operatorSumZeroSet A B)) :
    Tendsto alg.x atTop
      (nhds (projectionPoint (operatorSumZeroSet A B) hOmegaChebyshev alg.x0))
```

## Statement explanation
The declaration is a strong-convergence theorem for an inertial forward-backward algorithm solving a monotone inclusion in a real Hilbert space $H$. The inclusion is

$$
0\in A x+B x,
$$

where $A:H\to H$ is a single-valued operator and $B:H\rightrightarrows H$ is a set-valued operator. The zero set is denoted

$$
Z=\mathrm{operatorSumZeroSet} A B
=\{u\in H:0\in A u+B u\}.
$$

The hypotheses are as follows. The real number $\alpha$ is the cocoercivity parameter: $A$ is $\alpha$-cocoercive on all of $H$, expressed by `CocoerciveOn alpha Set.univ (fun x : Set.univ ↦ A x)`. The operator $B$ is assumed maximal monotone. The object `alg` is an inertial forward-backward algorithm for $A$ and $B$; in the proof it supplies the sequences

$$
x_n=\text{alg.x }n,\qquad y_n=\text{alg.y }n,\qquad z_n=\text{alg.z }n,
$$

the initial point $x_0=\text{alg.x0}$, the inertia coefficients $\theta_n=\text{alg.inertia }n$, and the step sizes $r_n=\text{alg.stepSize }n$. The algorithm identities used in the proof are:

$$
y_n=x_n+\theta_n(x_n-x_{n-1})\quad (n\ge 1),
$$

$$
z_n\in J[(r_n B)](y_n-r_n A y_n)\quad (n\ge 1),
$$

and $x_{n+1}$ is the metric projection of $x_0$ onto the intersection of the inertial set $C_n$ and the half-space $Q_n$, where

$$
C_n=\left\{u:\|z_n-u\|^2\le \|x_n-u\|^2
-2\theta_n\langle x_n-u,x_{n-1}-x_n\rangle
+\theta_n^2\|x_{n-1}-x_n\|^2\right\},
$$

$$
Q_n=\left\{u:\langle u-x_n,x_0-x_n\rangle\le 0\right\}.
$$

The inertia sequence is bounded,

$$
\sup_n|\theta_n|<\infty,
$$

and the step sizes satisfy

$$
0<\liminf_n r_n,\qquad
\liminf_n r_n\le \limsup_n r_n,\qquad
\limsup_n r_n<2\alpha,
$$

together with the pointwise condition

$$
r_n<2\alpha\quad(n\ge 1).
$$

There is also an initial feasibility condition

$$
Z\subseteq Q_1,
$$

the zero set $Z$ is nonempty, and $Z$ is Chebyshev, so that the metric projection of any point onto $Z$ is uniquely defined. The conclusion is strong convergence of the algorithm iterates to the metric projection of the initial point onto the zero set:

$$
x_n\longrightarrow
\mathrm{projectionPoint} Z\,(\text{Chebyshev witness})\,x_0
\quad\text{strongly in }H.
$$

In ordinary language: under cocoercivity of $A$, maximal monotonicity of $B$, bounded inertia, suitable step-size bounds, and an initial half-space feasibility condition, the inertial forward-backward iterates converge norm-strongly to the unique point of $Z$ closest to the initial point $x_0$.

## Lean proof
```lean
by
  have hbase : operatorSumZeroSet A B ⊆
      inertialForwardBackwardC alg.x alg.z alg.inertia 1 ∩
        inertialForwardBackwardQ alg.x alg.x0 1 := by
    intro u hu
    refine ⟨operatorSumZeroSet_subset_inertialForwardBackwardC A B alpha hA hB alg hStepLt
      1 (by omega) hu, hInitialOmegaQ hu⟩
  have hCQ_closed_convex : ∀ n : ℕ,
      IsClosed (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n) ∧
        Convex ℝ (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
          inertialForwardBackwardQ alg.x alg.x0 n) := by
    intro n
    rcases inertialForwardBackwardC_isClosed_convex A B alg n with ⟨hCclosed, hCconvex⟩
    rcases inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n with ⟨hQclosed, hQconvex⟩
    exact ⟨hCclosed.inter hQclosed, hCconvex.inter hQconvex⟩
  have hfeasible : ∀ n : ℕ, 1 ≤ n → operatorSumZeroSet A B ⊆
      inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ n hn ih =>
      intro u hu
      have huCQ := ih hu
      have hne : (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
          inertialForwardBackwardQ alg.x alg.x0 n).Nonempty := ⟨u, huCQ⟩
      have hp_eq : alg.x (n + 1) =
          projectionPoint (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
            inertialForwardBackwardQ alg.x alg.x0 n)
            (isChebyshev_of_nonempty_isClosed_convex hne
              (hCQ_closed_convex n).1 (hCQ_closed_convex n).2) alg.x0 :=
        projection_eq_of_mem_setValuedProjector_closed_convex hne
          (hCQ_closed_convex n).1 (hCQ_closed_convex n).2 (alg.projection_step n hn)
      have hvariational :=
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex hne
          (hCQ_closed_convex n).1 (hCQ_closed_convex n).2).mp hp_eq
      refine ⟨operatorSumZeroSet_subset_inertialForwardBackwardC A B alpha hA hB alg hStepLt
        (n + 1) (by omega) hu, ?_⟩
      simpa [inertialForwardBackwardQ] using hvariational.2 u huCQ
  have hx_next_mem_CQ : ∀ n : ℕ, 1 ≤ n → alg.x (n + 1) ∈
      inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n hn
    obtain ⟨u, hu⟩ := hOmega
    have hne : (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n).Nonempty := ⟨u, hfeasible n hn hu⟩
    exact (mem_setValuedProjector_iff.mp (alg.projection_step n hn)).1
  have hx_mem_Q : ∀ n : ℕ, alg.x n ∈ inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n
    simp [inertialForwardBackwardQ]
  have hx_is_projection_Q : ∀ n : ℕ,
      alg.x n = projectionPoint (inertialForwardBackwardQ alg.x alg.x0 n)
        (isChebyshev_of_nonempty_isClosed_convex ⟨alg.x n, hx_mem_Q n⟩
          (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).1
          (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).2) alg.x0 := by
    intro n
    apply (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).2).mpr
    constructor
    · exact hx_mem_Q n
    · intro v hv
      simpa [inertialForwardBackwardQ] using hv
  let q : H := projectionPoint (operatorSumZeroSet A B) hOmegaChebyshev alg.x0
  let d : ℕ → ℝ := fun n => ‖alg.x n - alg.x0‖
  have hqOmega : q ∈ operatorSumZeroSet A B :=
    projectionPoint_mem _ hOmegaChebyshev _
  have hqQ : ∀ n : ℕ, q ∈ inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [inertialForwardBackwardQ, alg.initial_zero]
    · exact (hfeasible n (Nat.one_le_iff_ne_zero.mpr hn) hqOmega).2
  have hdist_le : ∀ n : ℕ, d n ≤ ‖q - alg.x0‖ := by
    intro n
    have hpyth := metric_projection_pythagorean
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).2
      alg.x0 q (hqQ n)
    rw [← hx_is_projection_Q n, norm_sub_rev alg.x0 (alg.x n)] at hpyth
    rw [norm_sub_rev alg.x0 q] at hpyth
    dsimp [d]
    nlinarith [sq_nonneg ‖q - alg.x n‖, norm_nonneg (alg.x n - alg.x0),
      norm_nonneg (q - alg.x0)]
  have hstep_sq : ∀ n : ℕ, 1 ≤ n →
      ‖alg.x (n + 1) - alg.x n‖ ^ 2 + d n ^ 2 ≤ d (n + 1) ^ 2 := by
    intro n hn
    have hpyth := metric_projection_pythagorean
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex alg.x alg.x0 n).2
      alg.x0 (alg.x (n + 1)) (hx_next_mem_CQ n hn).2
    rw [← hx_is_projection_Q n, norm_sub_rev alg.x0 (alg.x n),
      norm_sub_rev alg.x0 (alg.x (n + 1))] at hpyth
    simpa [d, norm_sub_rev] using hpyth
  have hmono : Monotone d := by
    apply monotone_nat_of_le_succ
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [d]
      rw [alg.initial_zero]
      simp
    · have hs := hstep_sq n (Nat.one_le_iff_ne_zero.mpr hn)
      nlinarith [sq_nonneg ‖alg.x (n + 1) - alg.x n‖,
        norm_nonneg (alg.x n - alg.x0), norm_nonneg (alg.x (n + 1) - alg.x0)]
  have hdbdd : BddAbove (Set.range d) := by
    refine ⟨‖q - alg.x0‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hdist_le n
  have hd : Tendsto d atTop (nhds (⨆ n, d n)) :=
    tendsto_atTop_ciSup hmono hdbdd
  have hx_bounded : Bornology.IsBounded (Set.range alg.x) :=
    bounded_range_of_convergent_distance_to_point ⟨_, hd⟩
  have hd_shift : Tendsto (fun n => d (n + 1)) atTop (nhds (⨆ n, d n)) := by
    simpa using hd.comp (tendsto_add_atTop_nat 1)
  have hdiff_zero : Tendsto (fun n => d (n + 1) ^ 2 - d n ^ 2) atTop (nhds 0) := by
    simpa using (hd_shift.pow 2).sub (hd.pow 2)
  have hinc_sq_zero : Tendsto (fun n => ‖alg.x (n + 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.x (n + 1) - alg.x n‖ ^ 2)
      (g := fun n => d (n + 1) ^ 2 - d n ^ 2) ?_ ?_ hdiff_zero
    · filter_upwards with n
      exact sq_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hs := hstep_sq n hn
      nlinarith
  have hinc_zero : Tendsto (fun n => ‖alg.x (n + 1) - alg.x n‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hinc_sq_zero
    convert hsqrt using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le.mp hInertiaBounded)
  have hM_nonneg : 0 ≤ M := by
    have := hM (alg.inertia 1) (Set.mem_range_self 1)
    exact le_trans (norm_nonneg _) this
  have hinc_prev_zero : Tendsto (fun n => ‖alg.x n - alg.x (n - 1)‖) atTop (nhds 0) := by
    apply (hinc_zero.comp (tendsto_sub_atTop_nat 1)).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    change ‖alg.x ((n - 1) + 1) - alg.x (n - 1)‖ = ‖alg.x n - alg.x (n - 1)‖
    rw [Nat.sub_add_cancel hn]
  have hyx_zero : Tendsto (fun n => ‖alg.y n - alg.x n‖) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.y n - alg.x n‖)
      (g := fun n => M * ‖alg.x n - alg.x (n - 1)‖) ?_ ?_ ?_
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [alg.inertial_step (n := n) hn]
      have hvec : (alg.x n + alg.inertia n • (alg.x n - alg.x (n - 1))) - alg.x n =
          alg.inertia n • (alg.x n - alg.x (n - 1)) := by abel
      rw [hvec, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mem_range_self _)) (norm_nonneg _)
    · simpa using hinc_prev_zero.const_mul M
  have hznext_sq_le : ∀ n : ℕ, 1 ≤ n →
      ‖alg.z n - alg.x (n + 1)‖ ^ 2 ≤
        ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
          2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
            M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2 := by
    intro n hn
    apply inertial_residual_sq_le_of_abs_inertia
      (by simpa [Real.norm_eq_abs] using hM (alg.inertia n) (Set.mem_range_self n))
    simpa [inertialForwardBackwardC] using (hx_next_mem_CQ n hn).1
  have hcross_zero : Tendsto (fun n =>
      2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖)
      atTop (nhds 0) := by
    have hraw : Tendsto (fun n =>
        2 * M * ‖alg.x (n + 1) - alg.x n‖ * ‖alg.x n - alg.x (n - 1)‖)
        atTop (nhds 0) := by
      simpa using ((hinc_zero.const_mul (2 * M)).mul hinc_prev_zero)
    refine hraw.congr' ?_
    filter_upwards with n
    rw [norm_sub_rev (alg.x n) (alg.x (n + 1)), norm_sub_rev (alg.x n) (alg.x (n - 1))]
  have hlast_zero : Tendsto (fun n =>
      M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
    have hraw : Tendsto (fun n => M ^ 2 * ‖alg.x n - alg.x (n - 1)‖ ^ 2)
        atTop (nhds 0) := by
      simpa using (hinc_prev_zero.pow 2).const_mul (M ^ 2)
    refine hraw.congr' ?_
    filter_upwards with n
    rw [norm_sub_rev]
  have hrhs_zero : Tendsto (fun n =>
      ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
        2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
          M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
    have hraw : Tendsto (fun n =>
        ‖alg.x (n + 1) - alg.x n‖ ^ 2 +
          2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
            M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) atTop (nhds 0) := by
      simpa [add_assoc] using ((hinc_zero.pow 2).add hcross_zero).add hlast_zero
    refine hraw.congr' ?_
    filter_upwards with n
    rw [norm_sub_rev (alg.x n) (alg.x (n + 1))]
  have hznext_sq_zero : Tendsto (fun n => ‖alg.z n - alg.x (n + 1)‖ ^ 2)
      atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.x (n + 1)‖ ^ 2)
      (g := fun n => ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
        2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
          M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) ?_ ?_ hrhs_zero
    · filter_upwards with n
      exact sq_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hznext_sq_le n hn
  have hznext_zero : Tendsto (fun n => ‖alg.z n - alg.x (n + 1)‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hznext_sq_zero
    convert hsqrt using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  have hzx_zero : Tendsto (fun n => ‖alg.z n - alg.x n‖) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.x n‖)
      (g := fun n => ‖alg.z n - alg.x (n + 1)‖ + ‖alg.x (n + 1) - alg.x n‖) ?_ ?_
        (by simpa using hznext_zero.add hinc_zero)
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      calc
        ‖alg.z n - alg.x n‖ = ‖(alg.z n - alg.x (n + 1)) +
            (alg.x (n + 1) - alg.x n)‖ := by congr 1 <;> abel
        _ ≤ ‖alg.z n - alg.x (n + 1)‖ + ‖alg.x (n + 1) - alg.x n‖ := norm_add_le _ _
  have hzy_zero : Tendsto (fun n => ‖alg.z n - alg.y n‖) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.y n‖)
      (g := fun n => ‖alg.z n - alg.x n‖ + ‖alg.y n - alg.x n‖) ?_ ?_
        (by simpa using hzx_zero.add hyx_zero)
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      calc
        ‖alg.z n - alg.y n‖ = ‖(alg.z n - alg.x n) + (alg.x n - alg.y n)‖ := by
          congr 1 <;> abel
        _ ≤ ‖alg.z n - alg.x n‖ + ‖alg.x n - alg.y n‖ := norm_add_le _ _
        _ = ‖alg.z n - alg.x n‖ + ‖alg.y n - alg.x n‖ := by
          congr 1
          exact norm_sub_rev _ _
  let eps : ℝ := (liminf alg.stepSize atTop) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith [hSteps.1]
  have heps_alpha : eps ≤ 2 * alpha := by
    dsimp [eps]
    linarith [hSteps.2.1, hSteps.2.2]
  let T : H → H := fun x => Classical.choose
    (positive_resolvent_nonempty B hB heps (x - eps • A x))
  have hT : IsForwardBackwardSelection A B eps T := by
    intro x
    exact Classical.choose_spec
      (positive_resolvent_nonempty B hB heps (x - eps • A x))
  have hT_nonexp : LipschitzWith 1 T :=
    (forward_backward_nonexpansive_and_fixedPoints A B hB alpha eps heps heps_alpha hA T hT).1
  have hT_fix : Function.fixedPoints T = operatorSumZeroSet A B :=
    (forward_backward_nonexpansive_and_fixedPoints A B hB alpha eps heps heps_alpha hA T hT).2
  have hEventually : ∀ᶠ n in atTop, eps ≤ alg.stepSize n := by
    filter_upwards [Filter.eventually_lt_of_lt_liminf (u := alg.stepSize) (b := eps) (by
      change (liminf alg.stepSize atTop) / 2 < liminf alg.stepSize atTop
      linarith [hSteps.1])
      (isBoundedUnder_of_eventually_ge (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact (alg.stepSize_pos (n := n) hn).le))] with n hn
    exact hn.le
  classical
  let R : ℕ → H → H := fun n x =>
    if x = alg.y n then alg.z n
    else
      if hn : 1 ≤ n then
        Classical.choose (positive_resolvent_nonempty B hB (alg.stepSize_pos (n := n) hn)
          (x - alg.stepSize n • A x))
      else
        Classical.choose (positive_resolvent_nonempty B hB (by norm_num : (0 : ℝ) < 1) x)
  have hR : ∀ n, 1 ≤ n → ∀ x, R n x ∈ J[(alg.stepSize n • B)]
      (x - alg.stepSize n • A x) := by
    intro n hn x
    by_cases hx : x = alg.y n
    · subst x
      simpa [R] using alg.resolvent_step (n := n) hn
    · simpa [R, hx, hn] using Classical.choose_spec
        (positive_resolvent_nonempty B hB (alg.stepSize_pos (n := n) hn)
          (x - alg.stepSize n • A x))
  have hT_y_zero : Tendsto (fun n => ‖alg.y n - T (alg.y n)‖) atTop (nhds 0) := by
    have hupper_zero : Tendsto (fun n => 2 * ‖alg.y n - alg.z n‖) atTop (nhds 0) := by
      simpa [norm_sub_rev] using hzy_zero.const_mul 2
    refine squeeze_zero' (f := fun n => ‖alg.y n - T (alg.y n)‖)
      (g := fun n => 2 * ‖alg.y n - alg.z n‖) ?_ ?_ hupper_zero
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards [hEventually, eventually_ge_atTop 1] with n hn hn'
      have hbound := forward_backward_fixedPoints_and_residual_bound
        A B hB alpha hA (alg.stepSize n) eps heps hn (R n) T (hR n hn') hT
      simpa [R, norm_sub_rev] using hbound.2 (alg.y n)
  have hresidual_norm : Tendsto (fun n => ‖alg.x n - T (alg.x n)‖) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 2 * ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.y n)‖)
        atTop (nhds 0) := by
      simpa [norm_sub_rev] using (hyx_zero.const_mul 2).add hT_y_zero
    refine squeeze_zero' (f := fun n => ‖alg.x n - T (alg.x n)‖)
      (g := fun n => 2 * ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.y n)‖) ?_ ?_ hupper
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      calc
        ‖alg.x n - T (alg.x n)‖ ≤ ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.x n)‖ := by
          rw [← sub_add_sub_cancel (alg.x n) (alg.y n) (T (alg.x n))]
          exact norm_add_le _ _
        _ ≤ ‖alg.x n - alg.y n‖ +
            (‖alg.y n - T (alg.y n)‖ + ‖T (alg.y n) - T (alg.x n)‖) := by
          gcongr
          rw [← sub_add_sub_cancel (alg.y n) (T (alg.y n)) (T (alg.x n))]
          exact norm_add_le _ _
        _ ≤ ‖alg.x n - alg.y n‖ +
            (‖alg.y n - T (alg.y n)‖ + ‖alg.y n - alg.x n‖) := by
          gcongr
          simpa using hT_nonexp.norm_sub_le (alg.y n) (alg.x n)
        _ = 2 * ‖alg.x n - alg.y n‖ + ‖alg.y n - T (alg.y n)‖ := by
          rw [norm_sub_rev (alg.y n) (alg.x n)]
          ring
  have hresidual : Tendsto (fun n => alg.x n - T (alg.x n)) atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hresidual_norm
  have hclusterOmega : ∀ w : H,
      IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H w) →
        w ∈ operatorSumZeroSet A B := by
    intro w hw
    rcases hw with ⟨phi, hphi, hweak⟩
    have hresidual_phi : Tendsto (fun k => alg.x (phi k) - T (alg.x (phi k))) atTop (nhds 0) :=
      hresidual.comp hphi.tendsto_atTop
    have hfixed_nonempty : (fixedPointSetOn (Set.univ : Set H) T).Nonempty := by
      obtain ⟨u, hu⟩ := hOmega
      refine ⟨u, ?_⟩
      rw [mem_fixedPointSetOn_iff]
      refine ⟨Set.mem_univ _, ?_⟩
      have hufixed : u ∈ Function.fixedPoints T := by
        rw [hT_fix]
        exact hu
      exact hufixed
    have hweak_closed : IsSeqClosed ((toWeakSpace ℝ H) '' (Set.univ : Set H)) :=
      ((isClosed_iff_weak_image_isClosed_of_convex convex_univ).mp isClosed_univ).isSeqClosed
    have hT_lipschitz : LipschitzOnWith 1 T (Set.univ : Set H) := by
      apply isNonexpansiveOn_restrict_iff_lipschitzOnWith_one.mp
      intro a ha b hb
      simpa using hT_nonexp.norm_sub_le a b
    have hdem := browder_demiclosedness_principle hweak_closed hT_lipschitz
      (fun _ => Set.mem_univ _) hweak hresidual_phi
    have hwfixed : w ∈ fixedPointSetOn (Set.univ : Set H) T := by
      rw [mem_fixedPointSetOn_iff]
      refine ⟨mem_of_tendsto_weakly_of_isClosed_convex isClosed_univ convex_univ
        (fun _ => Set.mem_univ _) hweak, ?_⟩
      exact (sub_eq_zero.mp (hdem.trans rfl)).symm
    rw [mem_fixedPointSetOn_iff] at hwfixed
    have hwfixed' : w ∈ Function.fixedPoints T := hwfixed.2
    rw [hT_fix] at hwfixed'
    exact hwfixed'
  have hclusterEq : ∀ w : H,
      IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H w) → w = q := by
    intro w hw
    rcases hw with ⟨phi, hphi, hweak_phi⟩
    have hwOmega : w ∈ operatorSumZeroSet A B := hclusterOmega w ⟨phi, hphi, hweak_phi⟩
    have hinner_raw :=
      (weakConvergence_iff_forall_tendsto_inner_right (fun k => alg.x (phi k)) w).1
        hweak_phi (w - alg.x0)
    have hinner : Tendsto (fun k => inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0))
        atTop (nhds (‖w - alg.x0‖ ^ 2)) := by
      have hsub := hinner_raw.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 (w - alg.x0)) atTop
          (nhds (inner ℝ alg.x0 (w - alg.x0))) )
      convert hsub using 1
      · ext k
        rw [inner_sub_left]
      · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have hbound : ∀ k, inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0) ≤
        ‖q - alg.x0‖ * ‖w - alg.x0‖ := by
      intro k
      calc
        inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0) ≤
            ‖alg.x (phi k) - alg.x0‖ * ‖w - alg.x0‖ :=
          real_inner_le_norm _ _
        _ ≤ ‖q - alg.x0‖ * ‖w - alg.x0‖ :=
          mul_le_mul_of_nonneg_right (hdist_le (phi k)) (norm_nonneg _)
    have hsq_le : ‖w - alg.x0‖ ^ 2 ≤ ‖q - alg.x0‖ * ‖w - alg.x0‖ :=
      le_of_tendsto hinner (Filter.Eventually.of_forall hbound)
    have hw_le : ‖w - alg.x0‖ ≤ ‖q - alg.x0‖ := by
      by_cases hwzero : ‖w - alg.x0‖ = 0
      · rw [hwzero]
        exact norm_nonneg _
      · have hwpos : 0 < ‖w - alg.x0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwzero)
        nlinarith
    have hqbest := projectionPoint_isBestApproximation (operatorSumZeroSet A B)
      hOmegaChebyshev alg.x0
    have hq_le : ‖q - alg.x0‖ ≤ ‖w - alg.x0‖ := by
      have hinf := Metric.infDist_le_dist_of_mem (x := alg.x0) hwOmega
      have hqinf : dist alg.x0 q = Metric.infDist alg.x0 (operatorSumZeroSet A B) := hqbest.2
      simpa [dist_eq_norm, norm_sub_rev] using hqinf.trans_le hinf
    have hdist_eq : ‖w - alg.x0‖ = ‖q - alg.x0‖ := le_antisymm hw_le hq_le
    apply eq_projectionPoint_of_isBestApproximation (operatorSumZeroSet A B) hOmegaChebyshev
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
    refine ⟨hwOmega, ?_⟩
    calc
      dist alg.x0 w = ‖w - alg.x0‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ = ‖q - alg.x0‖ := hdist_eq
      _ = dist alg.x0 q := by rw [dist_eq_norm, norm_sub_rev]
      _ = Metric.infDist alg.x0 (operatorSumZeroSet A B) := hqbest.2
  have hweak : Tendsto (fun n => toWeakSpace ℝ H (alg.x n)) atTop
      (nhds (toWeakSpace ℝ H q)) := by
    have huniq : ∀ y z : H,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H z) → y = z := by
      intro y z hy hz
      calc
        y = q := hclusterEq y hy
        _ = z := (hclusterEq z hz).symm
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint alg.x).2
        ⟨hx_bounded, huniq⟩ with ⟨w, hw⟩
    have hwcluster : IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n))
        (toWeakSpace ℝ H w) := ⟨id, strictMono_id, by simpa using hw⟩
    have hwq : w = q := hclusterEq w hwcluster
    simpa [hwq] using hw
  have hL_le : (⨆ n, d n) ≤ ‖q - alg.x0‖ :=
    le_of_tendsto hd (Filter.Eventually.of_forall hdist_le)
  have hinner_raw :=
    (weakConvergence_iff_forall_tendsto_inner_right alg.x q).1 hweak (q - alg.x0)
  have hinner : Tendsto (fun n => inner ℝ (alg.x n - alg.x0) (q - alg.x0)) atTop
      (nhds (‖q - alg.x0‖ ^ 2)) := by
    have hsub := hinner_raw.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 (q - alg.x0)) atTop
        (nhds (inner ℝ alg.x0 (q - alg.x0))) )
    convert hsub using 1
    · ext n
      rw [inner_sub_left]
    · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hupper : Tendsto (fun n => d n * ‖q - alg.x0‖) atTop
      (nhds ((⨆ n, d n) * ‖q - alg.x0‖)) :=
    hd.mul tendsto_const_nhds
  have hsq_le : ‖q - alg.x0‖ ^ 2 ≤ (⨆ n, d n) * ‖q - alg.x0‖ := by
    apply le_of_tendsto_of_tendsto hinner hupper
    filter_upwards with n
    calc
      inner ℝ (alg.x n - alg.x0) (q - alg.x0) ≤
          ‖alg.x n - alg.x0‖ * ‖q - alg.x0‖ := real_inner_le_norm _ _
      _ = d n * ‖q - alg.x0‖ := rfl
  have hq_le_L : ‖q - alg.x0‖ ≤ (⨆ n, d n) := by
    by_cases hqzero : ‖q - alg.x0‖ = 0
    · rw [hqzero]
      calc
        0 = d 0 := by simp [d, alg.initial_zero]
        _ ≤ ⨆ n, d n := le_ciSup hdbdd 0
    · have hqpos : 0 < ‖q - alg.x0‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hqzero)
      nlinarith
  have hL : (⨆ n, d n) = ‖q - alg.x0‖ := le_antisymm hL_le hq_le_L
  have hnorm : Tendsto (fun n => ‖alg.x n - alg.x0‖) atTop (nhds ‖q - alg.x0‖) := by
    simpa [d, hL] using hd
  have hweak_sub : Tendsto (fun n => toWeakSpace ℝ H (alg.x n - alg.x0)) atTop
      (nhds (toWeakSpace ℝ H (q - alg.x0))) := by
    apply (weakConvergence_iff_forall_tendsto_inner_right
      (fun n => alg.x n - alg.x0) (q - alg.x0)).2
    intro u
    have hraw := (weakConvergence_iff_forall_tendsto_inner_right alg.x q).1 hweak u
    have hsub := hraw.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 u) atTop
        (nhds (inner ℝ alg.x0 u)))
    simpa [inner_sub_left] using hsub
  have hstrong_sub : Tendsto (fun n => alg.x n - alg.x0) atTop (nhds (q - alg.x0)) :=
    (tendsto_iff_tendsto_weakly_and_tendsto_norm (fun n => alg.x n - alg.x0)
      (q - alg.x0)).2 ⟨hweak_sub, hnorm⟩
  simpa only [sub_add_cancel] using hstrong_sub.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => alg.x0) atTop (nhds alg.x0))
```

## Proof explanation
The proof is a long convergence argument. It first builds the nested feasibility sets $C_n\cap Q_n$, then proves the distance sequence $d_n=\|x_n-x_0\|$ is monotone and bounded, then shows the inertial and resolvent residuals vanish, then identifies all weak cluster points as the projection point $q$, then upgrades weak convergence to strong convergence. The tactics `intro`, `rcases`, `obtain`, and `refine` are used to introduce hypotheses, decompose conjunctions, and build proof terms; `rw`, `simp`, and `simpa` rewrite definitions and algebraic identities; `linarith`, `nlinarith`, `omega`, `ring`, and `abel` handle arithmetic and inequalities; `squeeze_zero'` applies the squeeze theorem for convergence to zero.

First, the proof establishes that every element of $Z$ lies in $C_n\cap Q_n$ for every $n\ge 1$. For $n=1$, this is `hbase`: the inclusion $Z\subseteq C_1$ follows from the private lemma `operatorSumZeroSet_subset_inertialForwardBackwardC`. That lemma says that, under the cocoercivity of $A$, maximal monotonicity of $B$, and the step-size condition $r_n<2\alpha$ for $n\ge 1$, the zero set $Z$ is contained in the inertial set $C_n$. The inclusion $Z\subseteq Q_1$ is exactly the hypothesis `hInitialOmegaQ`.

Second, for every $n$, the intersection $C_n\cap Q_n$ is closed and convex. The lemma `inertialForwardBackwardC_isClosed_convex` states that the inertial set $C_n$ is closed and convex. The lemma `inertialForwardBackwardQ_isClosed_convex` states that the half-space $Q_n$ is closed and convex. The proof therefore intersects these two closed convex sets, using that the intersection of closed sets is closed and the intersection of convex sets is convex.

Third, the proof proves by induction on $n\ge 1$ that

$$
Z\subseteq C_n\cap Q_n.
$$

The base case is $n=1$. In the induction step, assume $u\in Z$ and $u\in C_n\cap Q_n$. Let

$$
K_n=C_n\cap Q_n.
$$

By the induction hypothesis, $K_n$ is nonempty. The algorithm supplies $x_{n+1}$ as a metric projection of $x_0$ onto $K_n$, expressed by `alg.projection_step n hn`. The lemma `projection_eq_of_mem_setValuedProjector_closed_convex` converts membership in the set-valued projector into equality with the chosen projection point:

$$
x_{n+1}=P_{K_n}(x_0).
$$

The lemma `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` gives the variational characterization of projection onto a nonempty closed convex set: a point $p$ is the projection of $x_0$ onto $K_n$ if and only if $p\in K_n$ and for every $v\in K_n$,

$$
\langle v-p,x_0-p\rangle\le 0.
$$

Applying this with $p=x_{n+1}$ and $v=u$, and using $u\in K_n$, gives

$$
\langle u-x_{n+1},x_0-x_{n+1}\rangle\le 0.
$$

This is exactly the statement that $u\in Q_{n+1}$. Also $u\in C_{n+1}$ follows again from `operatorSumZeroSet_subset_inertialForwardBackwardC`, now with index $n+1$. Thus the induction step is complete.

Fourth, the proof records some basic properties of $x_n$ relative to $Q_n$. It shows

$$
x_n\in Q_n
$$

for every $n$, because substituting $u=x_n$ into the definition of $Q_n$ gives the inner product $0\le 0$. It also shows that $x_n$ is the metric projection of $x_0$ onto $Q_n$. Indeed, the variational characterization of projection requires $x_n\in Q_n$ and, for every $v\in Q_n$,

$$
\langle v-x_n,x_0-x_n\rangle\le 0,
$$

which is precisely the defining inequality of $Q_n$.

Fifth, the proof introduces

$$
q=P_Z(x_0),
$$

the projection point of $x_0$ onto $Z$, and the distance sequence

$$
d_n=\|x_n-x_0\|.
$$

Since $q\in Z$, the already-established feasibility $Z\subseteq C_n\cap Q_n$ gives $q\in Q_n$ for all $n\ge 1$; for $n=0$, the half-space condition is automatic. The proof then uses the Pythagorean inequality for metric projections, stated by `metric_projection_pythagorean`: if $C$ is nonempty closed convex, $p=P_C(x)$, and $y\in C$, then

$$
\|y-p\|^2+\|x-p\|^2\le \|x-y\|^2.
$$

Applying this with $C=Q_n$, $p=x_n$, $x=x_0$, and $y=q$ gives

$$
d_n\le \|q-x_0\|.
$$

Applying it with $y=x_{n+1}$, which lies in $Q_n$, gives

$$
\|x_{n+1}-x_n\|^2+d_n^2\le d_{n+1}^2.
$$

Hence $d_n\le d_{n+1}$, so $d$ is monotone. Since it is also bounded above by $\|q-x_0\|$, it converges to its supremum:

$$
d_n\to \sup_n d_n.
$$

The lemma `bounded_range_of_convergent_distance_to_point` then implies that the range of $x_n$ is bounded, because the distances $\|x_n-x_0\|$ converge.

Sixth, the proof shows that successive differences and inertial/resolvent residuals tend to zero. From

$$
d_{n+1}^2-d_n^2\to 0
$$

and

$$
\|x_{n+1}-x_n\|^2\le d_{n+1}^2-d_n^2,
$$

the squeeze theorem gives

$$
\|x_{n+1}-x_n\|^2\to 0,
$$

and by continuity of the square root,

$$
\|x_{n+1}-x_n\|\to 0.
$$

Shifting indices gives

$$
\|x_n-x_{n-1}\|\to 0.
$$

The inertia sequence is bounded, so there is $M\ge 0$ such that $|\theta_n|\le M$ for all $n$. The algorithm identity

$$
y_n=x_n+\theta_n(x_n-x_{n-1})
$$

then yields

$$
\|y_n-x_n\|\le M\|x_n-x_{n-1}\|\to 0.
$$

Thus the inertial point $y_n$ is asymptotically close to $x_n$.

Next the proof controls $z_n$. Since $x_{n+1}\in C_n$, the definition of $C_n$ gives

$$
\|z_n-x_{n+1}\|^2
\le \|x_n-x_{n+1}\|^2
-2\theta_n\langle x_n-x_{n+1},x_{n-1}-x_n\rangle
+\theta_n^2\|x_{n-1}-x_n\|^2.
$$

The lemma `inertial_residual_sq_le_of_abs_inertia` replaces the signed inertial term by a positive bound using $|\theta_n|\le M$:

$$
\|z_n-x_{n+1}\|^2
\le \|x_n-x_{n+1}\|^2
+2M\|x_n-x_{n+1}\|\|x_{n-1}-x_n\|
+M^2\|x_{n-1}-x_n\|^2.
$$

The right-hand side tends to $0$, because each of its three terms tends to $0$. Therefore

$$
\|z_n-x_{n+1}\|^2\to 0,
$$

and hence

$$
\|z_n-x_{n+1}\|\to 0.
$$

Using the triangle inequality,

$$
\|z_n-x_n\|\le \|z_n-x_{n+1}\|+\|x_{n+1}-x_n\|\to 0.
$$

Another triangle inequality gives

$$
\|z_n-y_n\|\le \|z_n-x_n\|+\|x_n-y_n\|\to 0.
$$

So the three sequences $x_n$, $y_n$, and $z_n$ are asymptotically identical.

Seventh, the proof constructs an auxiliary nonexpansive forward-backward map with a small fixed step size. Let

$$
\varepsilon=\frac{\liminf_n r_n}{2}.
$$

The hypothesis $0<\liminf r_n$ gives $\varepsilon>0$, and the step-size hypotheses give $\varepsilon\le 2\alpha$. For each $x$, the lemma `positive_resolvent_nonempty` supplies a point in the resolvent $J[(\varepsilon B)](x-\varepsilon A x)$. The proof chooses one such point and calls it $T x$. Thus

$$
T x\in J[(\varepsilon B)](x-\varepsilon A x),
$$

so $T$ is a forward-backward selection with constant step $\varepsilon$. The theorem `forward_backward_nonexpansive_and_fixedPoints` then says that $T$ is $1$-Lipschitz and that

$$
\mathrm{fixedPoints} T=Z.
$$

Because $\varepsilon<\liminf r_n$, eventually the algorithmic step sizes satisfy $\varepsilon\le r_n$. The proof defines a variable-step selection $R_n$ such that

$$
R_n x\in J[(r_n B)](x-r_n A x)
$$

for $n\ge 1$, with the special value $R_n(y_n)=z_n$ supplied by the algorithm’s resolvent step. The theorem `forward_backward_fixedPoints_and_residual_bound` compares a selection at step $r_n$ with the selection $T$ at step $\varepsilon$: since $0<\varepsilon\le r_n$, it gives

$$
\|x-T x\|\le 2\|x-R_n x\|
$$

for every $x$. Applying this to $x=y_n$ and using $R_n(y_n)=z_n$ gives

$$
\|y_n-T y_n\|\le 2\|y_n-z_n\|.
$$

The right-hand side tends to $0$, so $y_n-T y_n\to 0$. Since $T$ is nonexpansive and $y_n-x_n\to 0$, the triangle inequality gives

$$
\|x_n-T x_n\|\to 0.
$$

Thus the original iterates are asymptotically fixed points of the nonexpansive map $T$.

Eighth, the proof identifies weak sequential cluster points. If a subsequence $x_{\phi(k)}$ converges weakly to some $w$, then along that subsequence the residual $x_{\phi(k)}-T x_{\phi(k)}$ still tends to $0$. The Browder demiclosedness principle, `browder_demiclosedness_principle`, says that if a sequence in a set $D$ converges weakly to $x$, the operator $T$ is $1$-Lipschitz on $D$, and $x_n-T x_n\to u$, then

$$
x-T x=u.
$$

Here $D=H$, $u=0$, so $w-T w=0$. Hence $w$ is a fixed point of $T$. Since $\mathrm{fixedPoints} T=Z$, every weak sequential cluster point $w$ of $x_n$ belongs to $Z$. The proof also uses `isClosed_iff_weak_image_isClosed_of_convex` on the whole space to know that the weak image of $H$ is sequentially closed, and `mem_of_tendsto_weakly_of_isClosed_convex` to record weak closedness of the whole space.

Ninth, the proof shows that there is at most one weak sequential cluster point, and that it must equal $q=P_Z(x_0)$. If $w$ is a weak cluster point, then by the previous paragraph $w\in Z$. Along a weakly convergent subsequence,

$$
x_{\phi(k)}\rightharpoonup w.
$$

The criterion `weakConvergence_iff_forall_tendsto_inner_right` says that weak convergence is equivalent to convergence of all inner products against a fixed vector. Applying it to $u=w-x_0$ gives

$$
\langle x_{\phi(k)}-x_0,w-x_0\rangle\to \|w-x_0\|^2.
$$

On the other hand, by Cauchy-Schwarz and the bound $d_{\phi(k)}\le \|q-x_0\|$,

$$
\langle x_{\phi(k)}-x_0,w-x_0\rangle
\le \|x_{\phi(k)}-x_0\|\|w-x_0\|
\le \|q-x_0\|\|w-x_0\|.
$$

Passing to the limit gives

$$
\|w-x_0\|^2\le \|q-x_0\|\|w-x_0\|.
$$

If $w=x_0$, this is trivial; otherwise one divides by $\|w-x_0\|$ and obtains

$$
\|w-x_0\|\le \|q-x_0\|.
$$

Since $q$ is the metric projection of $x_0$ onto $Z$ and $w\in Z$, the reverse inequality $\|q-x_0\|\le \|w-x_0\|$ holds by definition of the projection. Therefore the two distances are equal. The lemma `projectionPoint_isBestApproximation` says that $q$ is a best approximation to $x_0$ in $Z$. Since $w\in Z$ and has the same minimal distance, $w$ is also a best approximation. The lemma `eq_projectionPoint_of_isBestApproximation` then gives $w=q$. Hence all weak sequential cluster points are equal to $q$.

Tenth, the proof upgrades this to weak convergence of the entire sequence. The theorem `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` says that a sequence in a Hilbert space has a weak limit if and only if its range is bounded and it has at most one weak sequential cluster point. The range of $x_n$ was already shown bounded, and the preceding paragraph shows uniqueness of weak cluster points. Therefore a weak limit exists. Any weak limit is itself a weak sequential cluster point by taking the identity subsequence, so the weak limit must be $q$. Thus

$$
x_n\rightharpoonup q.
$$

Finally, the proof upgrades weak convergence to strong convergence. From $x_n\rightharpoonup q$ and the inner-product characterization of weak convergence,

$$
\langle x_n-x_0,q-x_0\rangle\to \|q-x_0\|^2.
$$

Also $d_n=\|x_n-x_0\|\to \sup_n d_n$, so

$$
d_n\|q-x_0\|\to \left(\sup_n d_n\right)\|q-x_0\|.
$$

For each $n$, Cauchy-Schwarz gives

$$
\langle x_n-x_0,q-x_0\rangle\le d_n\|q-x_0\|.
$$

Passing to the limit yields

$$
\|q-x_0\|^2\le \left(\sup_n d_n\right)\|q-x_0\|.
$$

Combined with the earlier bound $\sup_n d_n\le \|q-x_0\|$, this forces

$$
\sup_n d_n=\|q-x_0\|.
$$

Hence

$$
\|x_n-x_0\|\to \|q-x_0\|.
$$

The proof also shows that $x_n-x_0$ converges weakly to $q-x_0$, by subtracting the constant inner product $\langle x_0,u\rangle$ from the weak convergence of $x_n$ to $q$. The theorem `tendsto_iff_tendsto_weakly_and_tendsto_norm` states that strong convergence in a Hilbert space is equivalent to weak convergence together with convergence of norms. Applying it to the sequence $x_n-x_0$ and the limit $q-x_0$ gives

$$
x_n-x_0\to q-x_0
$$

strongly. Adding the constant $x_0$ yields

$$
x_n\to q.
$$

Thus the inertial forward-backward algorithm converges strongly to the metric projection of the initial point onto the zero set $Z=\mathrm{operatorSumZeroSet} A B$.

