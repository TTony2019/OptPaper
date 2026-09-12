## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/cor_1.lean`

## Lean statement
```lean
theorem inertial_proximal_point_strong_convergence (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (hZeros : B.zeros.Nonempty)
    (alg : InertialForwardBackward (fun _ : H ↦ 0) B)
    (hInertiaBounded : Bornology.IsBounded (Set.range alg.inertia))
    (hLowerStepBound : 0 < liminf alg.stepSize atTop)
    (hZerosChebyshev : IsChebyshev B.zeros)
    (hInitialZerosQ : B.zeros ⊆ inertialForwardBackwardQ alg.x alg.x0 1) :
    Tendsto alg.x atTop (nhds (projectionPoint B.zeros hZerosChebyshev alg.x0))
```

## Statement explanation
The declaration is a strong-convergence theorem for an inertial proximal-point/forward-backward method in a real Hilbert space $H$. The operator $B:H\rightrightarrows H$ is set-valued and is assumed to be maximal monotone. Its zero set

```math
B^{-1}(0)=\{x\in H:0\in Bx\}
```

is assumed nonempty. The object `alg` is an inertial forward-backward algorithm for the decomposition $A+B$, where the single-valued part is the zero map $A(x)=0$. In the proof the algorithm is used through its sequences $x_n=\text{alg.x n}$, $y_n=\text{alg.y n}$, $z_n=\text{alg.z n}$, initial point $x_0=\text{alg.x0}$, step sizes $s_n=\text{alg.stepSize n}$, and inertia parameters $\theta_n=\text{alg.inertia n}$. The algorithm supplies, for $n\ge1$,

$$
y_n=x_n+\theta_n(x_n-x_{n-1}),
$$

$$
z_n\in J_{s_nB}(y_n),
$$

where $J_{rB}=(I+rB)^{-1}$ is the resolvent of $rB$, and

$$
x_{n+1}\in \mathrm{Proj}_{C_n\cap Q_n}(x_0),
$$

where

```math
C_n=\Bigl\{u:\|z_n-u\|^2\le \|x_n-u\|^2
-2\theta_n\langle x_n-u,x_{n-1}-x_n\rangle
+\theta_n^2\|x_{n-1}-x_n\|^2\Bigr\}
```

and

```math
Q_n=\{u:\langle u-x_n,x_0-x_n\rangle\le0\}.
```

Thus $C_n\cap Q_n$ is the feasible set at stage $n$, and the algorithm projects the initial point onto it.

The additional hypotheses are as follows. `hInertiaBounded` says that the range of the inertia sequence is bounded, so there is some $M\ge0$ with $|\theta_n|\le M$ for all $n$. `hLowerStepBound` says

$$
0<\liminf_{n\to\infty}s_n,
$$

so eventually the step sizes stay above a positive threshold. `hZerosChebyshev` says that the zero set $B^{-1}(0)$ is Chebyshev, i.e. every point has a unique nearest point in it. `hInitialZerosQ` says that

$$
B^{-1}(0)\subseteq Q_1,
$$

so the zero set is initially feasible for the half-space constraint $Q_1$.

The conclusion is

$$
x_n\longrightarrow p
$$

strongly in norm, where

$$
p=\mathrm{proj}_{B^{-1}(0)}(x_0)
$$

is the projection of the initial point $x_0$ onto the zero set $B^{-1}(0)$. In other words, under bounded inertia, a positive lower liminf for the step sizes, a nonempty Chebyshev zero set, and initial feasibility, the inertial proximal-point method converges strongly, not merely weakly, to the metric projection of the initial point onto the zero set.

## Lean proof
```lean
by
  classical
  have hbase : B.zeros ⊆ inertialForwardBackwardC alg.x alg.z alg.inertia 1 ∩
      inertialForwardBackwardQ alg.x alg.x0 1 := by
    intro u hu
    exact ⟨zeros_subset_inertialForwardBackwardC_proximal B hB alg 1 (by omega) hu,
      hInitialZerosQ hu⟩
  have hCQ_closed_convex : ∀ n : ℕ,
      IsClosed (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n) ∧
      Convex ℝ (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n) := by
    intro n
    rcases inertialForwardBackwardC_isClosed_convex_proximal B alg n with ⟨hCclosed, hCconvex⟩
    rcases inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n with ⟨hQclosed, hQconvex⟩
    exact ⟨hCclosed.inter hQclosed, hCconvex.inter hQconvex⟩
  have hfeasible : ∀ n : ℕ, 1 ≤ n → B.zeros ⊆
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
      have hvariational :=
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex hne
          (hCQ_closed_convex n).1 (hCQ_closed_convex n).2).mp
          (eq_projectionPoint_of_isBestApproximation _
            (isChebyshev_of_nonempty_isClosed_convex hne (hCQ_closed_convex n).1
              (hCQ_closed_convex n).2)
            ((mem_setValuedProjector_iff).mp (alg.projection_step n hn)))
      refine ⟨zeros_subset_inertialForwardBackwardC_proximal B hB alg (n + 1) (by omega) hu, ?_⟩
      simpa [inertialForwardBackwardQ] using hvariational.2 u huCQ
  have hx_next_mem_CQ : ∀ n : ℕ, 1 ≤ n → alg.x (n + 1) ∈
      inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n hn
    obtain ⟨u, hu⟩ := hZeros
    have hne : (inertialForwardBackwardC alg.x alg.z alg.inertia n ∩
        inertialForwardBackwardQ alg.x alg.x0 n).Nonempty := ⟨u, hfeasible n hn hu⟩
    exact (mem_setValuedProjector_iff.mp (alg.projection_step n hn)).1
  have hx_mem_Q : ∀ n : ℕ, alg.x n ∈ inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n
    simp [inertialForwardBackwardQ]
  have hx_is_projection_Q : ∀ n : ℕ, alg.x n =
      projectionPoint (inertialForwardBackwardQ alg.x alg.x0 n)
        (isChebyshev_of_nonempty_isClosed_convex ⟨alg.x n, hx_mem_Q n⟩
          (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
          (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2) alg.x0 := by
    intro n
    apply (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2).mpr
    constructor
    · exact hx_mem_Q n
    · intro v hv
      simpa [inertialForwardBackwardQ] using hv
  let p : H := projectionPoint B.zeros hZerosChebyshev alg.x0
  let d : ℕ → ℝ := fun n => ‖alg.x n - alg.x0‖
  have hpZeros : p ∈ B.zeros := projectionPoint_mem _ hZerosChebyshev _
  have hpQ : ∀ n : ℕ, p ∈ inertialForwardBackwardQ alg.x alg.x0 n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [inertialForwardBackwardQ, alg.initial_zero]
    · exact (hfeasible n (Nat.one_le_iff_ne_zero.mpr hn) hpZeros).2
  have hdist_le : ∀ n : ℕ, d n ≤ ‖p - alg.x0‖ := by
    intro n
    have hpyth := metric_projection_pythagorean
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2
      alg.x0 p (hpQ n)
    rw [← hx_is_projection_Q n, norm_sub_rev alg.x0 (alg.x n)] at hpyth
    rw [norm_sub_rev alg.x0 p] at hpyth
    dsimp [d]
    nlinarith [sq_nonneg ‖p - alg.x n‖, norm_nonneg (alg.x n - alg.x0),
      norm_nonneg (p - alg.x0)]
  have hstep_sq : ∀ n : ℕ, 1 ≤ n →
      ‖alg.x (n + 1) - alg.x n‖ ^ 2 + d n ^ 2 ≤ d (n + 1) ^ 2 := by
    intro n hn
    have hpyth := metric_projection_pythagorean
      ⟨alg.x n, hx_mem_Q n⟩
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).1
      (inertialForwardBackwardQ_isClosed_convex_proximal alg.x alg.x0 n).2
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
    refine ⟨‖p - alg.x0‖, ?_⟩
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
      rw [alg.inertial_step n hn]
      have hvec : (alg.x n + alg.inertia n • (alg.x n - alg.x (n - 1))) - alg.x n =
          alg.inertia n • (alg.x n - alg.x (n - 1)) := by abel
      rw [hvec, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mem_range_self _)) (norm_nonneg _)
    · simpa using hinc_prev_zero.const_mul M
  have hinc_rev_zero : Tendsto (fun n => ‖alg.x n - alg.x (n + 1)‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using hinc_zero
  have hzxnext_sq_zero : Tendsto (fun n => ‖alg.z n - alg.x (n + 1)‖ ^ 2)
      atTop (nhds 0) := by
    have hzxnext_sq_le : ∀ n : ℕ, 1 ≤ n →
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
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.x (n + 1)‖ ^ 2)
      (g := fun n => ‖alg.x n - alg.x (n + 1)‖ ^ 2 +
        2 * M * ‖alg.x n - alg.x (n + 1)‖ * ‖alg.x (n - 1) - alg.x n‖ +
          M ^ 2 * ‖alg.x (n - 1) - alg.x n‖ ^ 2) ?_ ?_ hrhs_zero
    · filter_upwards with n
      exact sq_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact hzxnext_sq_le n hn
  have hzxnext_zero : Tendsto (fun n => ‖alg.z n - alg.x (n + 1)‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hzxnext_sq_zero
    convert hsqrt using 1
    · ext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  have hzy_zero : Tendsto (fun n => ‖alg.z n - alg.y n‖) atTop (nhds 0) := by
    refine squeeze_zero' (f := fun n => ‖alg.z n - alg.y n‖)
      (g := fun n => ‖alg.z n - alg.x (n + 1)‖ +
        ‖alg.x (n + 1) - alg.x n‖ + ‖alg.x n - alg.y n‖) ?_ ?_ ?_
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards with n
      calc
        ‖alg.z n - alg.y n‖ ≤ ‖alg.z n - alg.x (n + 1)‖ +
            ‖alg.x (n + 1) - alg.y n‖ := by
              simpa [norm_sub_rev] using
                (norm_sub_le (alg.z n - alg.x (n + 1)) (alg.y n - alg.x (n + 1)))
        _ ≤ ‖alg.z n - alg.x (n + 1)‖ +
            (‖alg.x (n + 1) - alg.x n‖ + ‖alg.x n - alg.y n‖) := by
              gcongr
              simpa [norm_sub_rev] using
                (norm_sub_le (alg.x (n + 1) - alg.x n) (alg.y n - alg.x n))
        _ = _ := by ring
    · simpa [norm_sub_rev] using ((hzxnext_zero.add hinc_zero).add hyx_zero)
  let eps : ℝ := (liminf alg.stepSize atTop) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    linarith [hLowerStepBound]
  have hEventually : ∀ᶠ n in atTop, eps ≤ alg.stepSize n := by
    filter_upwards [Filter.eventually_lt_of_lt_liminf (u := alg.stepSize) (b := eps) (by
      change (liminf alg.stepSize atTop) / 2 < liminf alg.stepSize atTop
      linarith [hLowerStepBound])
      (isBoundedUnder_of_eventually_ge (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact (alg.stepSize_pos n hn).le))] with n hn
    exact hn.le
  let T : H → H := fun x => Classical.choose (positive_resolvent_nonempty B hB heps x)
  have hT : ∀ x, T x ∈ ((eps : ℝ) • B).resolvent x := by
    intro x
    exact Classical.choose_spec (positive_resolvent_nonempty B hB heps x)
  let R : ℕ → H → H := fun n x => if hn : 1 ≤ n then
    if x = alg.y n then alg.z n else Classical.choose
      (positive_resolvent_nonempty B hB (alg.stepSize_pos n hn) x)
    else T x
  have hR : ∀ n, 1 ≤ n → ∀ x, R n x ∈ ((alg.stepSize n : ℝ) • B).resolvent x := by
    intro n hn x
    by_cases hx : x = alg.y n
    · subst x
      simpa [R, hn] using alg.resolvent_step n hn
    · simpa [R, hn, hx] using Classical.choose_spec
        (positive_resolvent_nonempty B hB (alg.stepSize_pos n hn) x)
  have hT_y_zero : Tendsto (fun n => ‖alg.y n - T (alg.y n)‖) atTop (nhds 0) := by
    have hupper_zero : Tendsto (fun n => 2 * ‖alg.y n - alg.z n‖) atTop (nhds 0) := by
      simpa [norm_sub_rev] using hzy_zero.const_mul 2
    refine squeeze_zero' (f := fun n => ‖alg.y n - T (alg.y n)‖)
      (g := fun n => 2 * ‖alg.y n - alg.z n‖) ?_ ?_ hupper_zero
    · filter_upwards with n
      exact norm_nonneg _
    · filter_upwards [hEventually, eventually_ge_atTop 1] with n hstep hn
      have hbound := forward_backward_fixedPoints_and_residual_bound
        (fun _ : H => 0) B hB eps (zero_cocoerciveOn eps heps)
        (alg.stepSize n) eps heps hstep (R n) T
        (by intro x; simpa [R, hn] using hR n hn x) (by intro x; simpa using hT x)
      simpa [R, hn, norm_sub_rev] using hbound.2 (alg.y n)
  have hT_nonexp : LipschitzWith 1 T :=
    (forward_backward_nonexpansive_and_fixedPoints (fun _ : H => 0) B hB
      (eps / 2) eps (by linarith [heps]) (by linarith) (zero_cocoerciveOn (eps / 2) (by linarith [heps]))
      T (by intro x; simpa using hT x)).1
  have hT_fix : Function.fixedPoints T = B.zeros := by
    have hraw := (forward_backward_nonexpansive_and_fixedPoints (fun _ : H => 0) B hB
        (eps / 2) eps (by linarith [heps]) (by linarith)
        (zero_cocoerciveOn (eps / 2) (by linarith [heps])) T
        (by intro x; simpa using hT x)).2
    have hzero : operatorSumZeroSet (fun _ : H => 0) B = B.zeros := by
      ext x
      simp [operatorSumZeroSet, operatorSum]
    exact hraw.trans hzero
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
  have hclusterZeros : ∀ w : H,
      IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H w) →
        w ∈ B.zeros := by
    intro w hw
    rcases hw with ⟨phi, hphi, hweak⟩
    have hresidual_phi : Tendsto (fun k => alg.x (phi k) - T (alg.x (phi k))) atTop (nhds 0) :=
      hresidual.comp hphi.tendsto_atTop
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
      IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H w) → w = p := by
    intro w hw
    rcases hw with ⟨phi, hphi, hweak_phi⟩
    have hwZeros : w ∈ B.zeros := hclusterZeros w ⟨phi, hphi, hweak_phi⟩
    have hinner_raw :=
      (weakConvergence_iff_forall_tendsto_inner_right (fun k => alg.x (phi k)) w).1
        hweak_phi (w - alg.x0)
    have hinner : Tendsto (fun k => inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0))
        atTop (nhds (‖w - alg.x0‖ ^ 2)) := by
      have hsub := hinner_raw.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 (w - alg.x0)) atTop
          (nhds (inner ℝ alg.x0 (w - alg.x0))))
      convert hsub using 1
      · ext k
        rw [inner_sub_left]
      · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have hbound : ∀ k, inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0) ≤
        ‖p - alg.x0‖ * ‖w - alg.x0‖ := by
      intro k
      calc
        inner ℝ (alg.x (phi k) - alg.x0) (w - alg.x0) ≤
            ‖alg.x (phi k) - alg.x0‖ * ‖w - alg.x0‖ := real_inner_le_norm _ _
        _ ≤ ‖p - alg.x0‖ * ‖w - alg.x0‖ :=
          mul_le_mul_of_nonneg_right (hdist_le (phi k)) (norm_nonneg _)
    have hsq_le : ‖w - alg.x0‖ ^ 2 ≤ ‖p - alg.x0‖ * ‖w - alg.x0‖ :=
      le_of_tendsto hinner (Filter.Eventually.of_forall hbound)
    have hw_le : ‖w - alg.x0‖ ≤ ‖p - alg.x0‖ := by
      by_cases hwzero : ‖w - alg.x0‖ = 0
      · rw [hwzero]
        exact norm_nonneg _
      · have hwpos : 0 < ‖w - alg.x0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hwzero)
        nlinarith
    have hpbest := projectionPoint_isBestApproximation B.zeros hZerosChebyshev alg.x0
    have hp_le : ‖p - alg.x0‖ ≤ ‖w - alg.x0‖ := by
      have hinf := Metric.infDist_le_dist_of_mem (x := alg.x0) hwZeros
      have hpinf : dist alg.x0 p = Metric.infDist alg.x0 B.zeros := hpbest.2
      simpa [dist_eq_norm, norm_sub_rev] using hpinf.trans_le hinf
    have hdist_eq : ‖w - alg.x0‖ = ‖p - alg.x0‖ := le_antisymm hw_le hp_le
    apply eq_projectionPoint_of_isBestApproximation B.zeros hZerosChebyshev
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
    refine ⟨hwZeros, ?_⟩
    calc
      dist alg.x0 w = ‖w - alg.x0‖ := by rw [dist_eq_norm, norm_sub_rev]
      _ = ‖p - alg.x0‖ := hdist_eq
      _ = dist alg.x0 p := by rw [dist_eq_norm, norm_sub_rev]
      _ = Metric.infDist alg.x0 B.zeros := hpbest.2
  have hweak : Tendsto (fun n => toWeakSpace ℝ H (alg.x n)) atTop
      (nhds (toWeakSpace ℝ H p)) := by
    have huniq : ∀ y z : H,
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n)) (toWeakSpace ℝ H z) → y = z := by
      intro y z hy hz
      calc
        y = p := hclusterEq y hy
        _ = z := (hclusterEq z hz).symm
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint alg.x).2
        ⟨hx_bounded, huniq⟩ with ⟨w, hw⟩
    have hwcluster : IsSequentialClusterPt (fun n => toWeakSpace ℝ H (alg.x n))
        (toWeakSpace ℝ H w) := ⟨id, strictMono_id, by simpa using hw⟩
    have hwp : w = p := hclusterEq w hwcluster
    simpa [hwp] using hw
  have hL_le : (⨆ n, d n) ≤ ‖p - alg.x0‖ :=
    le_of_tendsto hd (Filter.Eventually.of_forall hdist_le)
  have hinner_raw :=
    (weakConvergence_iff_forall_tendsto_inner_right alg.x p).1 hweak (p - alg.x0)
  have hinner : Tendsto (fun n => inner ℝ (alg.x n - alg.x0) (p - alg.x0)) atTop
      (nhds (‖p - alg.x0‖ ^ 2)) := by
    have hsub := hinner_raw.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 (p - alg.x0)) atTop
        (nhds (inner ℝ alg.x0 (p - alg.x0))))
    convert hsub using 1
    · ext n
      rw [inner_sub_left]
    · rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hupper : Tendsto (fun n => d n * ‖p - alg.x0‖) atTop
      (nhds ((⨆ n, d n) * ‖p - alg.x0‖)) := hd.mul tendsto_const_nhds
  have hsq_le : ‖p - alg.x0‖ ^ 2 ≤ (⨆ n, d n) * ‖p - alg.x0‖ := by
    apply le_of_tendsto_of_tendsto hinner hupper
    filter_upwards with n
    calc
      inner ℝ (alg.x n - alg.x0) (p - alg.x0) ≤
          ‖alg.x n - alg.x0‖ * ‖p - alg.x0‖ := real_inner_le_norm _ _
      _ = d n * ‖p - alg.x0‖ := rfl
  have hp_le_L : ‖p - alg.x0‖ ≤ (⨆ n, d n) := by
    by_cases hpzero : ‖p - alg.x0‖ = 0
    · rw [hpzero]
      calc 0 = d 0 := by simp [d, alg.initial_zero]
           _ ≤ ⨆ n, d n := le_ciSup hdbdd 0
    · have hppos : 0 < ‖p - alg.x0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpzero)
      nlinarith
  have hL : (⨆ n, d n) = ‖p - alg.x0‖ := le_antisymm hL_le hp_le_L
  have hnorm : Tendsto (fun n => ‖alg.x n - alg.x0‖) atTop (nhds ‖p - alg.x0‖) := by
    simpa [d, hL] using hd
  have hweak_sub : Tendsto (fun n => toWeakSpace ℝ H (alg.x n - alg.x0)) atTop
      (nhds (toWeakSpace ℝ H (p - alg.x0))) := by
    apply (weakConvergence_iff_forall_tendsto_inner_right
      (fun n => alg.x n - alg.x0) (p - alg.x0)).2
    intro u
    have hraw := (weakConvergence_iff_forall_tendsto_inner_right alg.x p).1 hweak u
    have hsub := hraw.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ alg.x0 u) atTop (nhds (inner ℝ alg.x0 u)))
    simpa [inner_sub_left] using hsub
  have hstrong_sub : Tendsto (fun n => alg.x n - alg.x0) atTop (nhds (p - alg.x0)) :=
    (tendsto_iff_tendsto_weakly_and_tendsto_norm (fun n => alg.x n - alg.x0)
      (p - alg.x0)).2 ⟨hweak_sub, hnorm⟩
  simpa only [sub_add_cancel] using hstrong_sub.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => alg.x0) atTop (nhds alg.x0))
```

## Proof explanation
The proof is organized around showing that the iterates become asymptotically feasible in the half-spaces $Q_n$, that the iterates are weakly compact, that every weak sequential cluster point must equal the projection $p$, and then upgrading weak convergence to strong convergence.

First, the proof establishes the initial inclusion

$$
B^{-1}(0)\subseteq C_1\cap Q_1.
$$

For $u\in B^{-1}(0)$, the result `zeros_subset_inertialForwardBackwardC_proximal` gives $u\in C_1$. This lemma says that for a maximal monotone operator $B$, the inertial forward-backward algorithm for $0+B$, and every $n\ge1$, the zero set $B^{-1}(0)$ is contained in the proximal half-space $C_n$. The hypothesis `hInitialZerosQ` gives $u\in Q_1$ directly. The tactic `intro u hu` introduces an arbitrary element $u$ of the zero set and its membership proof, and the pair of conclusions is assembled with `exact`.

Next, the proof shows that for every $n$, the set $C_n\cap Q_n$ is closed and convex. The lemma `inertialForwardBackwardC_isClosed_convex_proximal` states that each $C_n$ is closed and convex. Concretely, $C_n$ is defined by an inequality involving squared norms and an inner product, so it is a closed convex set. The lemma `inertialForwardBackwardQ_isClosed_convex_proximal` states that each $Q_n$ is closed and convex; indeed $Q_n$ is a closed half-space. The intersection is then closed and convex by `IsClosed.inter` and `Convex.inter`. The proof uses `rcases` to destruct the conjunctions returned by these lemmas and then `exact` to give the pair for the intersection.

The main feasibility fact is then proved by induction:

$$
\forall n\ge1,\qquad B^{-1}(0)\subseteq C_n\cap Q_n.
$$

The base case is the initial inclusion above. For the induction step, suppose $B^{-1}(0)\subseteq C_n\cap Q_n$, and let $u\in B^{-1}(0)$. By the induction hypothesis, $u\in C_n\cap Q_n$. The algorithm's projection step says that $x_{n+1}$ is the projection of $x_0$ onto $C_n\cap Q_n$. The proof converts this into the variational inequality for metric projection using `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex`. That lemma says that for a nonempty closed convex set $C$, a point $p$ is the projection of $x$ onto $C$ if and only if

$$
p\in C
\quad\text{and}\quad
\forall y\in C,\quad \langle y-p,x-p\rangle\le0.
$$

Here $C=C_n\cap Q_n$, $p=x_{n+1}$, and $x=x_0$. Applying it to $y=u$ gives

$$
\langle u-x_{n+1},x_0-x_{n+1}\rangle\le0,
$$

which is exactly the defining inequality for $u\in Q_{n+1}$. Also $u\in C_{n+1}$ by `zeros_subset_inertialForwardBackwardC_proximal` applied at $n+1$. This proves the induction step. In Lean this is the `Nat.le_induction` block; the `simpa [inertialForwardBackwardQ]` step unfolds the definition of $Q_{n+1}$ to match the inequality just obtained.

The proof also records that for $n\ge1$,

$$
x_{n+1}\in C_n\cap Q_n,
$$

because $x_{n+1}$ is the projection onto $C_n\cap Q_n$, hence belongs to that set. The nonemptiness needed for the projection lemma comes from choosing an element of $B^{-1}(0)$, whose nonemptiness is `hZeros`, and using the feasibility inclusion just proved. The conversion from membership in the set-valued projector to membership in the set uses `mem_setValuedProjector_iff`.

Next, the proof shows that for every $n$,

$$
x_n\in Q_n
$$

and in fact

$$
x_n=\mathrm{proj}_{Q_n}(x_0).
$$

The first fact is immediate from the definition of $Q_n$, since

$$
\langle x_n-x_n,x_0-x_n\rangle=0\le0.
$$

The second follows from the projection characterization again: $x_n\in Q_n$, and for every $v\in Q_n$, the defining inequality of $Q_n$ is precisely

$$
\langle v-x_n,x_0-x_n\rangle\le0.
$$

Since $Q_n$ is nonempty closed convex, the projection characterization of `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` gives the equality. The proof uses `simp [inertialForwardBackwardQ]` to unfold the half-space condition.

Let

$$
p=\mathrm{proj}_{B^{-1}(0)}(x_0)
$$

and

```math
d_n=\|x_n-x_0\|.
```

The chosen projection point satisfies $p\in B^{-1}(0)$. Also $p\in Q_n$ for every $n$: for $n=0$, this is trivial because $Q_0$ uses the vector $x_0-x_0=0$; for $n\ge1$, it follows from the feasibility inclusion $B^{-1}(0)\subseteq C_n\cap Q_n$.

The proof then establishes the distance bound

```math
d_n\le \|p-x_0\|.
```

This uses `metric_projection_pythagorean`, which says that if $C$ is nonempty closed convex, $x$ is projected to $q$, and $y\in C$, then

```math
\|y-q\|^2+\|x-q\|^2\le\|x-y\|^2.
```

Taking $C=Q_n$, $q=x_n$, $x=x_0$, and $y=p$, and using $p\in Q_n$, gives

```math
\|p-x_n\|^2+\|x_0-x_n\|^2\le\|x_0-p\|^2.
```

Since the first term is nonnegative, $`d_n\le\|p-x_0\|`$. The `nlinarith` call uses nonnegativity of squares and norms to extract this inequality.

The proof then derives the step inequality

```math
\|x_{n+1}-x_n\|^2+d_n^2\le d_{n+1}^2
\qquad(n\ge1).
```

Again this is the Pythagorean inequality for the projection $x_n$ of $x_0$ onto $Q_n$, now applied to the point $x_{n+1}\in Q_n$, which was shown above. Therefore $d_{n+1}^2-d_n^2\ge0$, and with nonnegativity of distances, $d_n\le d_{n+1}$. Thus $d$ is monotone. The proof uses `monotone_nat_of_le_succ` and `nlinarith` to convert the squared inequality into monotonicity.

Since $d$ is monotone and bounded above by $`\|p-x_0\|`$, it has a finite supremum$L=\sup_n d_n$, and

$$
d_n\to L.
$$

This is the content of `tendsto_atTop_ciSup`. The boundedness of the distance sequence also implies, by `bounded_range_of_convergent_distance_to_point`, that the range of the sequence $x_n$ is bounded. This lemma says that if the distances $`\|x_n-z\|`$converge for some fixed$z$, then the sequence$x_n$is bounded; here$z=x_0$and the distances are$d_n$.

The proof then shows that the increments vanish. Since $d_{n+1}$ and $d_n$ both tend to $L$, their squares have the same limit, so

$$
d_{n+1}^2-d_n^2\to0.
$$

The step inequality gives

```math
0\le\|x_{n+1}-x_n\|^2\le d_{n+1}^2-d_n^2,
```

so by the squeeze theorem (`squeeze_zero'`),

```math
\|x_{n+1}-x_n\|^2\to0.
```

Using continuity of the square root, the proof concludes

```math
\|x_{n+1}-x_n\|\to0.
```

Similarly,

```math
\|x_n-x_{n-1}\|\to0.
```

The boundedness of the inertia sequence gives some $M\ge0$ with $|\theta_n|\le M$. From the inertial step

$$
y_n=x_n+\theta_n(x_n-x_{n-1}),
$$

the proof obtains

```math
\|y_n-x_n\|
=\|\theta_n(x_n-x_{n-1})\|
=|\theta_n|\,\|x_n-x_{n-1}\|
\le M\|x_n-x_{n-1}\|\to0.
```

Thus $y_n-x_n\to0$.

To control $z_n$, the proof uses the fact that $x_{n+1}\in C_n$, which gives

```math
\|z_n-x_{n+1}\|^2
\le \|x_n-x_{n+1}\|^2
-2\theta_n\langle x_n-x_{n+1},x_{n-1}-x_n\rangle
+\theta_n^2\|x_{n-1}-x_n\|^2.
```

The lemma `inertial_residual_sq_le_of_abs_inertia` states that if $|\theta|\le M$ and

```math
\|r\|^2\le \|v\|^2-2\theta\langle v,w\rangle+\theta^2\|w\|^2,
```

then

```math
\|r\|^2\le \|v\|^2+2M\|v\|\|w\|+M^2\|w\|^2.
```

Applying this with $r=z_n-x_{n+1}$, $v=x_n-x_{n+1}$, $w=x_{n-1}-x_n$, and $\theta=\theta_n$, the right-hand side tends to $0$ because both $`\|x_n-x_{n+1}\|`$and$`\|x_{n-1}-x_n\|`$tend to$0$. Hence

```math
\|z_n-x_{n+1}\|^2\to0,
```

and therefore

```math
\|z_n-x_{n+1}\|\to0.
```

Combining this with the vanishing of $`\|x_{n+1}-x_n\|`$and$`\|x_n-y_n\|`$, the proof concludes

```math
\|z_n-y_n\|\to0.
```

Now the proof constructs auxiliary mappings. Let

$$
\varepsilon=\frac{\liminf_{n\to\infty}s_n}{2}>0.
$$

Since $0\lt \liminf s_n$, the proof has $\varepsilon\gt 0$, and eventually

$$
\varepsilon\le s_n.
$$

The lemma `positive_resolvent_nonempty` says that if $B$ is maximal monotone and $r\gt 0$, then for every $y$ there exists $z\in J_{rB}(y)$. Using this, the proof defines a map $T$ by choosing, for each $x$, an element

$$
T(x)\in J_{\varepsilon B}(x).
$$

It also defines maps $R_n$ for $n\ge1$ by choosing an element of $J_{s_nB}(x)$, with the special case $R_n(y_n)=z_n$; this special case is valid because the algorithm itself gives $z_n\in J_{s_nB}(y_n)$.

The theorem `forward_backward_fixedPoints_and_residual_bound` is then applied with $A=0$, the maximal monotone operator $B$, cocoercivity parameter $\varepsilon$, and

$$
s=\varepsilon,\qquad r=s_n,\qquad T_s=T,\qquad T_r=R_n.
$$

The hypothesis $s\le r$, i.e. $\varepsilon\le s_n$, holds eventually. The cocoercivity hypothesis for $A=0$ is supplied by `zero_cocoerciveOn`, which says that the zero map is cocoercive with any positive constant on all of $H$. The conclusion of the cited theorem is that the fixed points of $R_n$ equal the zero set of $A+B=0+B=B$, and that for every $x$,

```math
\|x-T(x)\|\le 2\|x-R_n(x)\|.
```

Applying this at $x=y_n$, and using $R_n(y_n)=z_n$, gives

```math
\|y_n-T(y_n)\|\le 2\|y_n-z_n\|\to0.
```

Thus

$$
y_n-T(y_n)\to0.
$$

The theorem `forward_backward_nonexpansive_and_fixedPoints` is applied with $A=0$, the same $B$, $\alpha=\varepsilon/2$, and $\varepsilon$ as the step parameter. The hypotheses are $\varepsilon\gt 0$ and $\varepsilon\le 2(\varepsilon/2)$, which are immediate, and $T(x)\in J_{\varepsilon B}(x)$. The theorem concludes that $T$ is $1$-Lipschitz and that its fixed point set is the zero set of $0+B=B$. Since the zero set of the sum is $B^{-1}(0)$, the proof obtains

$$
\mathrm{Fix}(T)=B^{-1}(0).
$$

The translation from the operator-sum zero set to $B^{-1}(0)$ is done by unfolding `operatorSumZeroSet` and `operatorSum`.

Using the nonexpansiveness of $T$, the proof estimates

```math
\|x_n-T(x_n)\|
\le \|x_n-y_n\|+\|y_n-T(y_n)\|+\|T(y_n)-T(x_n)\|
\le 2\|x_n-y_n\|+\|y_n-T(y_n)\|.
```

Both terms on the right tend to $0$, so

```math
\|x_n-T(x_n)\|\to0,
```

and hence

$$
x_n-T(x_n)\to0
$$

strongly.

Next the proof identifies all weak sequential cluster points of $x_n$. Suppose $x_{\phi(k)}$ converges weakly to $w$. Along this subsequence, the residual $x_{\phi(k)}-T(x_{\phi(k)})$ still tends strongly to $0$. The map $T$ is globally $1$-Lipschitz, hence Lipschitz on all of $H$. The weak image of $H$ is sequentially closed: this follows from `isClosed_iff_weak_image_isClosed_of_convex` applied to the closed convex set $H$. The Browder demiclosedness principle `browder_demiclosedness_principle` then applies with $D=H$, $T$, the sequence $x_{\phi(k)}$, weak limit $w$, and strong residual limit $0$. It gives

$$
w-T(w)=0.
$$

Thus $w$ is a fixed point of $T$. Since $\mathrm{Fix}(T)=B^{-1}(0)$, every weak sequential cluster point $w$ of $x_n$ belongs to $B^{-1}(0)$. The proof also uses `mem_of_tendsto_weakly_of_isClosed_convex` to record that $w$ lies in the closed convex set $H$, and `mem_fixedPointSetOn_iff` to translate between fixed points on $H$ and fixed points of $T$.

The proof then shows that every such weak cluster point must equal $p$. Let $x_{\phi(k)}\rightharpoonup w$. Since $w\in B^{-1}(0)$, the weak convergence and the characterization `weakConvergence_iff_forall_tendsto_inner_right` give

```math
\langle x_{\phi(k)}-x_0,w-x_0\rangle
\longrightarrow \langle w-x_0,w-x_0\rangle
=\|w-x_0\|^2.
```

On the other hand, by Cauchy-Schwarz and the earlier distance bound $`d_n\le\|p-x_0\|`$,

```math
\langle x_{\phi(k)}-x_0,w-x_0\rangle
\le \|x_{\phi(k)}-x_0\|\,\|w-x_0\|
\le \|p-x_0\|\,\|w-x_0\|.
```

Taking limits gives

```math
\|w-x_0\|^2\le \|p-x_0\|\,\|w-x_0\|.
```

If $`\|w-x_0\|=0`$, then the desired inequality$`\|w-x_0\|\le\|p-x_0\|`$is immediate. Otherwise, dividing by$`\|w-x_0\|>0`$ gives

```math
\|w-x_0\|\le\|p-x_0\|.
```

Conversely, since $p$ is a best approximation to $x_0$ in $B^{-1}(0)$ and $w\in B^{-1}(0)$, the distance from $x_0$ to $B^{-1}(0)$ is at most $`\|w-x_0\|`$, while$p$ attains that distance. The proof uses `projectionPoint_isBestApproximation` and `Metric.infDist_le_dist_of_mem` to conclude

```math
\|p-x_0\|\le\|w-x_0\|.
```

Hence

```math
\|w-x_0\|=\|p-x_0\|.
```

Thus $w$ is also a best approximation of $x_0$ in $B^{-1}(0)$. Since the zero set is Chebyshev, the best approximation is unique, so `eq_projectionPoint_of_isBestApproximation` gives $w=p$. The proof rewrites the best-approximation condition using `isBestApproximation_iff_mem_and_dist_eq_infDist`.

The sequence $x_n$ is bounded, and the previous paragraph shows that it has at most one weak sequential cluster point, namely $p$. The theorem `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` states that a sequence in a Hilbert space has a weak limit if and only if it is bounded and has at most one weak sequential cluster point. Applying it yields a weak limit $w$, and since the limit itself is a weak sequential cluster point, the uniqueness result forces $w=p$. Therefore

$$
x_n\rightharpoonup p
$$

weakly.

It remains to upgrade weak convergence to strong convergence. The proof already has

$$
d_n\to L=\sup_n d_n
$$

and $`L\le\|p-x_0\|`$. To get the reverse inequality, it uses the weak convergence$x_n\rightharpoonup p$. By `weakConvergence_iff_forall_tendsto_inner_right`,

```math
\langle x_n-x_0,p-x_0\rangle
\longrightarrow \|p-x_0\|^2.
```

Cauchy-Schwarz gives

```math
\langle x_n-x_0,p-x_0\rangle
\le \|x_n-x_0\|\,\|p-x_0\|
=d_n\|p-x_0\|.
```

Since $`d_n\|p-x_0\|\to L\|p-x_0\|`$, passing to the limit gives

```math
\|p-x_0\|^2\le L\|p-x_0\|.
```

If $`\|p-x_0\|=0`$, then$`L\ge0=\|p-x_0\|`$. Otherwise, dividing by$`\|p-x_0\|>0`$gives$`\|p-x_0\|\le L`$. Thus$`L=\|p-x_0\|`$, and therefore

```math
\|x_n-x_0\|=d_n\to\|p-x_0\|.
```

Finally, the proof combines weak convergence and norm convergence. The weak convergence $x_n\rightharpoonup p$ implies, again by the inner-product characterization, that

$$
x_n-x_0\rightharpoonup p-x_0
$$

weakly, because inner products with any $u$ converge after subtracting the constant $\langle x_0,u\rangle$. The norm convergence just proved is

```math
\|x_n-x_0\|\to\|p-x_0\|.
```

The theorem `tendsto_iff_tendsto_weakly_and_tendsto_norm` states that strong convergence is equivalent to weak convergence together with convergence of norms. Applying it to the sequence $x_n-x_0$ gives

$$
x_n-x_0\longrightarrow p-x_0
$$

strongly. Adding the constant $x_0$ gives

$$
x_n\longrightarrow p
$$

strongly, which is the desired conclusion.

Throughout the proof, `intro` introduces arbitrary elements or hypotheses; `rw` rewrites by definitions and previously proved equalities; `simp` and `simpa` unfold definitions such as `inertialForwardBackwardQ` and simplify trivial inequalities; `exact` closes goals with a provided proof or term; `refine` constructs structured proofs; `rcases` destructs conjunctions and existential hypotheses; `nlinarith` and `linarith` solve arithmetic and order inequalities, often using nonnegativity of squares and norms; `filter_upwards` proves eventually statements; `squeeze_zero'` applies the squeeze theorem to nonnegative sequences; `gcongr` uses monotonicity of addition and norms in inequalities; and `convert` changes a goal to an equivalent form.

