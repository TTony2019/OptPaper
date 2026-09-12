## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/thm_1.lean`

## Lean statement
```lean
theorem IPAHDD_finiteLength_and_critical {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (f phi : H → ℝ) (h gamma beta L r : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDD f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta)
    (hf : ContDiff ℝ 1 f) (hL : HasLipschitzGradient (gradient f) L)
    (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta)) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 + f (alg.x 1) - sInf (Set.range f)
    ∧ HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (nhds xInf) ∧
      IsDryFrictionCritical phi f xInf ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦
        ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
        2 * h ^ 2 * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2)
```

## Statement explanation
The theorem is stated in a real Hilbert space $H$. The data are two functions $f,\phi:H\to\mathbb R$, real parameters $h,\gamma,\beta,L,r$, a dry-friction hypothesis `hdf : DF_r phi r`, and an algorithm trajectory `alg : IPAHDD ...`. The hypothesis `DF_r phi r` supplies exactly the facts used later: $\phi$ extended to extended-real values lies in $\Gamma_0(H)$, meaning it is convex and lower semicontinuous; $\phi(0)=0$; $r>0$; the open ball $B(0,r)$ is contained in the subdifferential $\partial\phi(0)$; and $\phi$ is continuous. The theorem also assumes that $f$ is $C^1$, that its gradient is $L$-Lipschitz, that $L\ge0$, that $f$ is bounded below, that $h>0$, $\gamma>0$, $\beta>0$, and that the damping inequality

$$
\gamma \ge L\left(\frac h2+\beta\right)
$$

holds. The algorithm `alg` is an IPAHDD trajectory for $f$ and $\phi$; the proof below uses only the shifted recurrence supplied by `IPAHDD_shifted_recurrence`.

The conclusion asserts the existence of a limit point $x_\infty$ and of a number $E_1$ such that

$$
E_1=\frac12\left\|\frac1h(x_1-x_0)\right\|^2+f(x_1)-\mathrm{sInf}(\mathrm{range}f).
$$

Here $x_k$ denotes the trajectory `alg.x k`, and $\mathrm{sInf}(\mathrm{range}f)$ is the infimum of $f$ over $H$. The theorem then states:

- the trajectory has finite length, i.e.

$$
\sum_{k=0}^{\infty}\|x_{k+1}-x_k\|<\infty;
$$

- $x_k\to x_\infty$;
- $x_\infty$ is dry-friction critical, meaning

$$
-\nabla f(x_\infty)\in\partial\phi(0);
$$

- the total variation after index $1$ is bounded by

$$
\sum_{k=1}^{\infty}\|x_{k+1}-x_k\|
\le \frac1r\left(E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2\right);
$$

- the total squared second difference is bounded by

$$
\sum_{k=1}^{\infty}\|x_{k+1}-2x_k+x_{k-1}\|^2
\le 2h^2\left(E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2\right).
$$

Thus the statement says that an IPAHDD trajectory with dry friction and Hessian-driven damping has finite length, converges, has a critical limit, and satisfies explicit quantitative bounds on its total variation and total squared acceleration.

## Lean proof
```lean
by
  let d : ℕ → H := fun k ↦ alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k ↦ (1 / h) • d k
  rcases hpositive with ⟨hh, hg, hb⟩
  have hgrad : ∀ z, HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    fun z => hasFDerivAt_gradient f hf z
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hden : 0 < 1 + h * gamma := by
    nlinarith [mul_pos hh hg]
  have hden0 : 1 + h * gamma ≠ 0 := ne_of_gt hden
  have hlam : 0 < h / (1 + h * gamma) := div_pos hh hden
  have hc : 0 ≤ beta * L / (2 * h) := by
    exact div_nonneg (mul_nonneg hb.le hL_nonneg) (by positivity)
  have hdry : ∀ u : H, r * ‖u‖ ≤ phi u :=
    subgradient_ball_exact_linear_lower_bound phi hdf.value_at_zero hdf.radius_pos hdf.ball_subset
  have hshift (k : ℕ) :
      ∃ q, q ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + gamma • d (k + 1) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0) := by
    simpa [v, d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      IPAHDD_shifted_recurrence f phi hdf.toEReal_mem_gammaZero h gamma beta alg hh hg k
  have hdescent (x y : H) :
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 :=
    smooth_descent_of_fderiv_lipschitz f L hf hL x y
  have hdv (k : ℕ) : d k = h • v k := by
    dsimp [d, v]
    rw [smul_smul]
    field_simp [hh.ne']
    simp
  have hraw (k : ℕ) :
      (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
        (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
        gamma * h * ‖v (k + 1)‖ ^ 2 + h * phi (v (k + 1)) +
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) ≤ 0 := by
    obtain ⟨q, hq, hrec⟩ := hshift k
    have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
    have hinert : inner ℝ (v (k + 1) - v k) (v (k + 1)) =
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 :=
      inner_sub_self_energy_identity _ _
    have hdamp : inner ℝ (gamma • d (k + 1)) (v (k + 1)) =
        gamma * h * ‖v (k + 1)‖ ^ 2 := by
      rw [hdv (k + 1), inner_smul_left, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have hqterm : inner ℝ (h • q) (v (k + 1)) = h * inner ℝ q (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hbetaterm :
        inner ℝ (beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) (v (k + 1)) =
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      rw [inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
    have hgradterm : inner ℝ (h • gradient f (alg.x (k + 1))) (v (k + 1)) =
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
      dsimp [v]
      rw [inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hh.ne']
    have hscalar :
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          gamma * h * ‖v (k + 1)‖ ^ 2 + h * inner ℝ q (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) = 0 := by
      simpa only [inner_add_left, inner_sub_left, inner_zero_left, add_zero,
        hinert, hdamp, hqterm, hbetaterm, hgradterm] using hinner
    have hphi : phi (v (k + 1)) ≤ inner ℝ q (v (k + 1)) := by
      have hq0 := hq 0
      change (⟪0 - v (k + 1), q⟫_ℝ : EReal) + (phi (v (k + 1)) : EReal) ≤
        (phi 0 : EReal) at hq0
      norm_cast at hq0
      simp only [zero_sub, inner_neg_left, hdf.value_at_zero,
        neg_add_le_iff_le_add, add_zero, real_inner_comm] at hq0
      linarith
    have hhphi : h * phi (v (k + 1)) ≤ h * inner ℝ q (v (k + 1)) :=
      mul_le_mul_of_nonneg_left hphi hh.le
    linarith
  have hfric (k : ℕ) : r * ‖d (k + 1)‖ ≤ h * phi (v (k + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left (hdry (v (k + 1))) hh.le
    have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm]
    nlinarith
  have hcross (k : ℕ) :
      beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
        beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2) := by
    have hnormv : ‖v (k + 1)‖ = ‖d (k + 1)‖ / h := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / h)]
      ring
    have hinner :
        inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
          L * ‖d k‖ * (‖d (k + 1)‖ / h) := by
      calc
        inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) ≤
            ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖ :=
          real_inner_le_norm _ _
        _ ≤ (L * ‖alg.x (k + 1) - alg.x k‖) * ‖v (k + 1)‖ := by
          exact mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
        _ = L * ‖d k‖ * (‖d (k + 1)‖ / h) := by simp [d, hnormv]
    have hmul := mul_le_mul_of_nonneg_left hinner hb.le
    have hyoung : 2 * (‖d k‖ * ‖d (k + 1)‖) ≤
        ‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖d k‖ - ‖d (k + 1)‖)]
    have hcoef : 0 ≤ beta * L / h := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    field_simp [hh.ne'] at hmul hyoung' ⊢
    nlinarith
  have hcross_lower (k : ℕ) :
      -(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2)) ≤
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
    have hnormv : ‖v (k + 1)‖ = ‖d (k + 1)‖ / h := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / h)]
      ring
    have hnormgrad :
        ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
      simpa [d] using hL (alg.x (k + 1)) (alg.x k)
    have hprod :
        ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖ ≤
          (L * ‖d k‖) * ‖v (k + 1)‖ :=
      mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg _)
    have hinter :
        -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) ≤
          inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      calc
        -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) =
            -((L * ‖d k‖) * ‖v (k + 1)‖) := by rw [hnormv]
        _ ≤ -(‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖) :=
            neg_le_neg hprod
        _ ≤ inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) :=
            neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hmul := mul_le_mul_of_nonneg_left hinter hb.le
    have hyoung : 2 * (‖d k‖ * ‖d (k + 1)‖) ≤
        ‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖d k‖ - ‖d (k + 1)‖)]
    have hcoef : 0 ≤ beta * L / h := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    field_simp [hh.ne'] at hmul hyoung' ⊢
    nlinarith
  let c : ℝ := beta * L / (2 * h)
  let E : ℕ → ℝ := fun k =>
    (1 / 2 : ℝ) * ‖v k‖ ^ 2 + f (alg.x (k + 1)) - sInf (Set.range f)
  let M : ℕ → ℝ := fun k => E k + c * ‖d k‖ ^ 2
  have hc' : 0 ≤ c := by simpa [c] using hc
  obtain ⟨a, ha⟩ := hbelow
  have hbounded : BddBelow (Set.range f) := ⟨a, by
    rintro y ⟨z, rfl⟩
    exact ha z⟩
  have hE_nonneg (k : ℕ) : 0 ≤ E k := by
    have hinf : sInf (Set.range f) ≤ f (alg.x (k + 1)) :=
      csInf_le hbounded ⟨alg.x (k + 1), rfl⟩
    dsimp [E]
    have hkin : 0 ≤ (1 / 2 : ℝ) * ‖v k‖ ^ 2 := by positivity
    linarith
  have hM_nonneg (k : ℕ) : 0 ≤ M k := by
    dsimp [M]
    exact add_nonneg (hE_nonneg k) (mul_nonneg hc' (sq_nonneg _))
  have hcoef : c ≤ gamma / h - L / 2 - beta * L / (2 * h) := by
    dsimp [c]
    field_simp [hh.ne']
    nlinarith [hgamma]
  have hacc_vec (k : ℕ) :
      d (k + 1) - d k = alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k := by
    dsimp [d]
    abel
  have hacc_id (k : ℕ) :
      (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 =
        (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
    have hv : v (k + 1) - v k = (1 / h) • (d (k + 1) - d k) := by
      dsimp [v, d]
      simp only [smul_sub]
    rw [hv, hacc_vec, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / h)]
    field_simp [hh.ne']
  have hstep (k : ℕ) :
      M (k + 1) - M k +
          (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
          r * ‖d (k + 1)‖ ≤ 0 := by
    have hdesc := hdescent (alg.x (k + 1)) (alg.x (k + 2))
    have hdesc' :
        f (alg.x (k + 2)) - f (alg.x (k + 1)) -
            (L / 2) * ‖d (k + 1)‖ ^ 2 ≤
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
      dsimp [d]
      norm_num [Nat.add_assoc] at hdesc ⊢
      linarith
    have hdamp : gamma * h * ‖v (k + 1)‖ ^ 2 =
        (gamma / h) * ‖d (k + 1)‖ ^ 2 := by
      have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
        rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      rw [hnorm]
      field_simp [hh.ne']
    have hmain :
        E (k + 1) - E k + (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          (gamma / h - L / 2 - c) * ‖d (k + 1)‖ ^ 2 + r * ‖d (k + 1)‖ ≤
          c * ‖d k‖ ^ 2 := by
      have hraw' := hraw k
      rw [hdamp] at hraw'
      dsimp [E, c]
      linarith [hraw', hfric k, hcross_lower k, hdesc']
    have hcoeftimes : c * ‖d (k + 1)‖ ^ 2 ≤
        (gamma / h - L / 2 - c) * ‖d (k + 1)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · linarith [hcoef]
      · exact sq_nonneg _
    calc
      M (k + 1) - M k +
          (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
          r * ‖d (k + 1)‖ =
          E (k + 1) - E k + (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
            c * ‖d (k + 1)‖ ^ 2 - c * ‖d k‖ ^ 2 + r * ‖d (k + 1)‖ := by
              rw [hacc_id k]
              dsimp [M]
              ring
      _ ≤ 0 := by linarith
  have htel (N : ℕ) :
      M N + ∑ k ∈ Finset.range N,
          ((1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
            r * ‖d (k + 1)‖) ≤ M 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep N]
  have hsum_d (N : ℕ) : ∑ k ∈ Finset.range N, ‖d (k + 1)‖ ≤ M 0 / r := by
    have hacc_nonneg : 0 ≤ ∑ k ∈ Finset.range N,
        (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro k hk
      positivity
    have hlen_nonneg : 0 ≤ ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg hdf.radius_pos.le (norm_nonneg _)
    have hle := htel N
    rw [Finset.sum_add_distrib] at hle
    have hlen_factor :
        (∑ k ∈ Finset.range N, r * ‖d (k + 1)‖) =
          r * (∑ k ∈ Finset.range N, ‖d (k + 1)‖) := by
      rw [Finset.mul_sum]
    rw [hlen_factor] at hle
    have hright : r * (∑ k ∈ Finset.range N, ‖d (k + 1)‖) ≤ M 0 := by
      linarith [hM_nonneg N]
    have hright' : (∑ k ∈ Finset.range N, ‖d (k + 1)‖) * r ≤ M 0 := by
      simpa [mul_comm] using hright
    exact (le_div_iff₀ hdf.radius_pos).mpr hright'
  have hsum_acc (N : ℕ) : ∑ k ∈ Finset.range N,
      ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 ≤ 2 * h ^ 2 * M 0 := by
    have hacc_nonneg : 0 ≤ ∑ k ∈ Finset.range N,
        (1 / (2 * h ^ 2)) * ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro k hk
      positivity
    have hlen_nonneg : 0 ≤ ∑ k ∈ Finset.range N, r * ‖d (k + 1)‖ := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg hdf.radius_pos.le (norm_nonneg _)
    have hle := htel N
    rw [Finset.sum_add_distrib] at hle
    have hscaled : (1 / (2 * h ^ 2)) *
        (∑ k ∈ Finset.range N,
          ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2) ≤ M 0 := by
      rw [Finset.mul_sum]
      linarith [hM_nonneg N]
    have hpos : 0 < 2 * h ^ 2 := by positivity
    have hmult := mul_le_mul_of_nonneg_left hscaled hpos.le
    have hcancel : (2 * h ^ 2) * ((1 / (2 * h ^ 2)) *
        (∑ k ∈ Finset.range N,
          ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2)) =
        ∑ k ∈ Finset.range N,
          ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      field_simp [hh.ne']
    rw [hcancel] at hmult
    simpa [mul_assoc] using hmult
  have hs_d : Summable (fun k => ‖d (k + 1)‖) :=
    summable_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hs_acc : Summable (fun k =>
      ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hsum_acc
  have hs : Summable (fun k : ℕ => ‖d k‖) :=
    summable_real_of_summable_real_succ (fun k : ℕ => ‖d k‖) hs_d
  have hfinite : HasFiniteLength alg.x := by
    unfold HasFiniteLength
    simpa [d] using hs
  obtain ⟨xInf, hxInf⟩ := finite_length_tendsto alg.x hfinite
  let E1 : ℝ := (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
    f (alg.x 1) - sInf (Set.range f)
  have hE1 : E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
      f (alg.x 1) - sInf (Set.range f) := rfl
  have hM0 : M 0 = E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2 := by
    dsimp [M, E, c, v, d, E1]
  have hlength0 : tsum (fun k => ‖d (k + 1)‖) ≤ M 0 / r :=
    Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) hsum_d
  have hlength : tsum (fun k : {k : ℕ // 1 ≤ k} =>
      ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
      (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
    change tsum (fun k : {k : ℕ // 1 ≤ k} =>
      (fun n : ℕ => ‖d n‖) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n : ℕ => ‖d n‖) k.1) =
          tsum (fun n : ℕ => ‖d (n + 1)‖) :=
        tsum_subtype_succ_reindex (fun n : ℕ => ‖d n‖)
      _ ≤ M 0 / r := hlength0
      _ = (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
        rw [hM0]
        field_simp [hdf.radius_pos.ne']
  have hacc0 : tsum (fun k =>
      ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2) ≤ 2 * h ^ 2 * M 0 :=
    Real.tsum_le_of_sum_range_le (fun k => sq_nonneg _) hsum_acc
  have hacc : tsum (fun k : {k : ℕ // 1 ≤ k} =>
      ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
      2 * h ^ 2 * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
    change tsum (fun k : {k : ℕ // 1 ≤ k} =>
      (fun n : ℕ => ‖alg.x (n + 1) - 2 • alg.x n + alg.x (n - 1)‖ ^ 2) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} =>
          (fun n : ℕ => ‖alg.x (n + 1) - 2 • alg.x n + alg.x (n - 1)‖ ^ 2) k.1) =
          tsum (fun n : ℕ =>
            ‖alg.x ((n + 1) + 1) - 2 • alg.x (n + 1) + alg.x ((n + 1) - 1)‖ ^ 2) :=
        tsum_subtype_succ_reindex
          (fun n : ℕ => ‖alg.x (n + 1) - 2 • alg.x n + alg.x (n - 1)‖ ^ 2)
      _ ≤ 2 * h ^ 2 * M 0 := by simpa [Nat.add_assoc, Nat.add_sub_cancel] using hacc0
      _ = 2 * h ^ 2 * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by rw [hM0]
  have hd_norm : Filter.Tendsto (fun k => ‖d k‖) Filter.atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hd : Filter.Tendsto d Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hd_norm
  have hd_succ : Filter.Tendsto (fun k => d (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hd.comp (Filter.tendsto_add_atTop_nat 1)
  have hv : Filter.Tendsto v Filter.atTop (nhds 0) := by
    simpa [v] using hd.const_smul (1 / h)
  have hv_succ : Filter.Tendsto (fun k => v (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hv.comp (Filter.tendsto_add_atTop_nat 1)
  have hv_diff : Filter.Tendsto (fun k => v (k + 1) - v k) Filter.atTop (nhds 0) :=
    by simpa using hv_succ.sub hv
  have hxInf_succ : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
    simpa using hxInf.comp (Filter.tendsto_add_atTop_nat 1)
  have hgrad : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop (nhds (gradient f xInf))
    := (hC1.tendsto xInf).comp hxInf
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hxInf_succ
  have hgrad_diff : Filter.Tendsto
      (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) :=
    by simpa using hgrad_succ.sub hgrad
  let q : ℕ → H := fun k => Classical.choose (hshift k)
  have hqmem (k : ℕ) : q k ∈ subdifferential phi (v (k + 1)) :=
    (Classical.choose_spec (hshift k)).1
  have hqrec (k : ℕ) :
      v (k + 1) - v k + gamma • d (k + 1) + h • q k +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0 :=
    (Classical.choose_spec (hshift k)).2
  have hqsolve (k : ℕ) :
      h • q k = -(v (k + 1) - v k + gamma • d (k + 1) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1))) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      h • q k + (v (k + 1) - v k + gamma • d (k + 1) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1))) =
          v (k + 1) - v k + gamma • d (k + 1) + h • q k +
            beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
            h • gradient f (alg.x (k + 1)) := by ac_rfl
      _ = 0 := hqrec k
  have hdamp : Filter.Tendsto (fun k => gamma • d (k + 1)) Filter.atTop (nhds 0) :=
    by simpa using hd_succ.const_smul gamma
  have hbeta : Filter.Tendsto
      (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)))
      Filter.atTop (nhds 0) := by simpa using hgrad_diff.const_smul beta
  have hgrad_term : Filter.Tendsto (fun k => h • gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (h • gradient f xInf)) := hgrad_succ.const_smul h
  have hright : Filter.Tendsto (fun k =>
      -(v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)))) Filter.atTop (nhds (-(h • gradient f xInf))) := by
    simpa using (((hv_diff.add hdamp).add hbeta).add hgrad_term).neg
  have hq_scaled : Filter.Tendsto (fun k => h • q k) Filter.atTop
      (nhds (h • (-gradient f xInf))) := by
    convert hright using 1
    · ext k
      rw [hqsolve]
    · simp
  have hscalar : (1 / h : ℝ) * h = 1 := by field_simp [hh.ne']
  have hq : Filter.Tendsto q Filter.atTop (nhds (-gradient f xInf)) := by
    have hq' := hq_scaled.const_smul (1 / h)
    have hqfun : (fun k => (1 / h) • (h • q k)) = q := by
      funext k
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    have hqlim : (1 / h) • (h • (-gradient f xInf)) = -gradient f xInf := by
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    rw [hqfun, hqlim] at hq'
    exact hq'
  have hcritical : IsDryFrictionCritical phi f xInf := by
    unfold IsDryFrictionCritical
    exact convex_subgradient_limit_at_zero phi (fun k => v (k + 1)) q
      (-gradient f xInf) hdf.continuous hv_succ hq hqmem
  exact ⟨xInf, E1, hE1, hfinite, hxInf, hcritical, hlength, hacc⟩
```

## Proof explanation
The proof has no `intro` step, because all variables and hypotheses are already explicit in the theorem statement. It begins by defining the discrete velocity and difference sequences

$$
d_k=x_{k+1}-x_k,\qquad v_k=\frac1h d_k.
$$

The tactic `let` introduces these abbreviations. The hypothesis `hpositive` is split by `rcases` into $h>0$, $\gamma>0$, and $\beta>0$. Several elementary positivity facts are recorded: $1+h\gamma>0$, $h/(1+h\gamma)>0$, and

$$
c:=\frac{\beta L}{2h}\ge0.
$$

The latter follows from $\beta>0$, $L\ge0$, and $h>0$. The proof also records two gradient facts. The theorem `hasFDerivAt_gradient` says that if $f$ is $C^1$, then at every $z$ the Fréchet derivative of $f$ at $z$ is the continuous linear functional $w\mapsto\langle\nabla f(z),w\rangle$. The theorem `continuous_gradient_of_contDiff` says that if $f$ is $C^1$, then $\nabla f$ is continuous; this continuity is used later to pass gradient limits through the convergence of $x_k$.

The dry-friction hypothesis is converted into a global linear lower bound. The theorem `subgradient_ball_exact_linear_lower_bound` states that if $\phi(0)=0$, $r>0$, and $B(0,r)\subseteq\partial\phi(0)$, then

$$
r\|u\|\le \phi(u)\qquad\text{for all }u\in H.
$$

The proof applies this using the fields `hdf.value_at_zero`, `hdf.radius_pos`, and `hdf.ball_subset`, obtaining

$$
\forall u,\qquad r\|u\|\le\phi(u).
$$

Mathematically, the reason is that $s\in\partial\phi(0)$ means $\phi(u)\ge\phi(0)+\langle u,s\rangle=\langle u,s\rangle$ for all $u$; taking the supremum over all $s\in B(0,r)$ gives the lower bound $r\|u\|\le\phi(u)$.

Next the proof invokes the shifted recurrence. The theorem `IPAHDD_shifted_recurrence` gives, for each $k$, the existence of a vector $q$ such that

$$
q\in\partial\phi\!\left(v_{k+1}\right)
$$

and

$$
v_{k+1}-v_k+\gamma d_{k+1}+h q
+\beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
+h\nabla f(x_{k+1})=0.
$$

This is exactly the algorithmic recurrence expressed in the variables $d_k$ and $v_k$. The tactic `simpa` rewrites the statement from the library lemma into these local abbreviations.

The descent inequality comes from `smooth_descent_of_fderiv_lipschitz`. It states that if $f$ is $C^1$ and $\nabla f$ is $L$-Lipschitz, then

$$
f(y)\le f(x)+\langle\nabla f(x),y-x\rangle+\frac L2\|y-x\|^2.
$$

The proof records this for arbitrary $x,y$, and later specializes it to $x=x_{k+1}$, $y=x_{k+2}$. In that specialization it becomes

$$
f(x_{k+2})-f(x_{k+1})-\frac L2\|d_{k+1}\|^2
\le \langle\nabla f(x_{k+1}),d_{k+1}\rangle.
$$

The first major energy estimate is called `hraw`. Starting from the recurrence, the proof takes the inner product of both sides with $v_{k+1}$. The identity `inner_sub_self_energy_identity` gives

$$
\langle v_{k+1}-v_k,v_{k+1}\rangle
=\frac12\|v_{k+1}\|^2-\frac12\|v_k\|^2+\frac12\|v_{k+1}-v_k\|^2.
$$

Since $d_k=h v_k$, the damping term becomes

$$
\langle \gamma d_{k+1},v_{k+1}\rangle
=\gamma h\|v_{k+1}\|^2.
$$

Also $d_{k+1}=h v_{k+1}$, so

$$
\langle h\nabla f(x_{k+1}),v_{k+1}\rangle
=\langle\nabla f(x_{k+1}),d_{k+1}\rangle.
$$

The subgradient membership $q\in\partial\phi(v_{k+1})$ is used at the point $0$:

$$
\langle 0-v_{k+1},q\rangle+\phi(v_{k+1})\le\phi(0)=0,
$$

so

$$
\phi(v_{k+1})\le\langle q,v_{k+1}\rangle.
$$

Multiplying by $h>0$ gives $h\phi(v_{k+1})\le h\langle q,v_{k+1}\rangle$. Therefore, replacing the $h\langle q,v_{k+1}\rangle$ term in the scalar equality by the smaller term $h\phi(v_{k+1})$, the proof obtains

$$
\frac12\|v_{k+1}\|^2-\frac12\|v_k\|^2
+\frac12\|v_{k+1}-v_k\|^2
+\gamma h\|v_{k+1}\|^2
+h\phi(v_{k+1})
$$

$$
+\beta\langle\nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle
+\langle\nabla f(x_{k+1}),d_{k+1}\rangle\le0.
$$

This is the estimate `hraw`.

From the dry-friction bound one gets a friction estimate for the difference sequence:

$$
r\|d_{k+1}\|\le h\phi(v_{k+1}).
$$

Indeed $r\|v_{k+1}\|\le\phi(v_{k+1})$, and $d_{k+1}=h v_{k+1}$, so

$$
r\|d_{k+1}\|=r h\|v_{k+1}\|\le h\phi(v_{k+1}).
$$

This is `hfric`.

The cross term involving $\nabla f(x_{k+1})-\nabla f(x_k)$ is bounded above and below. The upper bound `hcross` uses Cauchy–Schwarz,

$$
\langle\nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle
\le \|\nabla f(x_{k+1})-\nabla f(x_k)\|\|v_{k+1}\|,
$$

and the Lipschitz hypothesis, which gives

$$
\|\nabla f(x_{k+1})-\nabla f(x_k)\|
\le L\|x_{k+1}-x_k\|=L\|d_k\|.
$$

Since $\|v_{k+1}\|=\|d_{k+1}\|/h$, this yields a bound by

$$
\frac{\beta L}{h}\|d_k\|\|d_{k+1}\|.
$$

Young’s inequality $2ab\le a^2+b^2$ then gives

$$
\beta\langle\nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle
\le c(\|d_k\|^2+\|d_{k+1}\|^2),
\qquad c=\frac{\beta L}{2h}.
$$

The lower bound `hcross_lower` is proved similarly, using

$$
|\langle u,w\rangle|\le\|u\|\|w\|
$$

to get

$$
-c(\|d_k\|^2+\|d_{k+1}\|^2)
\le
\beta\langle\nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle.
$$

This lower bound is the one used in the Lyapunov inequality.

The proof then defines

$$
E_k=\frac12\|v_k\|^2+f(x_{k+1})-\mathrm{sInf}(\mathrm{range}f),
\qquad
M_k=E_k+c\|d_k\|^2.
$$

The bounded-below hypothesis on $f$ makes $\mathrm{range}f$ bounded below, so $\mathrm{sInf}(\mathrm{range}f)\le f(x_{k+1})$. Hence $E_k\ge0$, and since $c\ge0$, also $M_k\ge0$. The damping condition $\gamma\ge L(h/2+\beta)$ is rewritten as

$$
c\le \frac{\gamma}{h}-\frac L2-c.
$$

Indeed, multiplying by $h>0$, this is equivalent to

$$
\gamma\ge L\left(\frac h2+\beta\right).
$$

The proof also expresses the second difference of the trajectory:

$$
d_{k+1}-d_k=x_{k+2}-2x_{k+1}+x_k.
$$

Since $v_{k+1}-v_k=(1/h)(d_{k+1}-d_k)$,

$$
\frac12\|v_{k+1}-v_k\|^2
=\frac{1}{2h^2}\|x_{k+2}-2x_{k+1}+x_k\|^2.
$$

Combining `hraw`, `hfric`, `hcross_lower`, and the descent inequality gives the intermediate inequality

$$
E_{k+1}-E_k+\frac12\|v_{k+1}-v_k\|^2
+\left(\frac{\gamma}{h}-\frac L2-c\right)\|d_{k+1}\|^2
+r\|d_{k+1}\|
\le c\|d_k\|^2.
$$

Using $c\le \gamma/h-L/2-c$, one replaces $c\|d_{k+1}\|^2$ by the larger coefficient term. The resulting Lyapunov inequality is

$$
M_{k+1}-M_k
+\frac{1}{2h^2}\|x_{k+2}-2x_{k+1}+x_k\|^2
+r\|d_{k+1}\|\le0.
$$

This is `hstep`.

Summing `hstep` from $k=0$ to $N-1$ gives the telescoping estimate

$$
M_N+\sum_{k=0}^{N-1}
\left(
\frac{1}{2h^2}\|x_{k+2}-2x_{k+1}+x_k\|^2
+r\|d_{k+1}\|
\right)\le M_0.
$$

The proof proves this by induction on $N$, using `Finset.sum_range_succ` and `linarith` to handle the algebraic telescoping. Because both summands are nonnegative, this yields two partial-sum bounds:

$$
\sum_{k=0}^{N-1}\|d_{k+1}\|\le \frac{M_0}{r},
\qquad
\sum_{k=0}^{N-1}
\|x_{k+2}-2x_{k+1}+x_k\|^2
\le 2h^2 M_0.
$$

The division by $r$ is legitimate because $r>0$. The theorem `summable_of_sum_range_le` then gives summability of the nonnegative sequences

$$
k\mapsto\|d_{k+1}\|,
\qquad
k\mapsto\|x_{k+2}-2x_{k+1}+x_k\|^2.
$$

The theorem `summable_real_of_summable_real_succ` upgrades the first summability to

$$
\sum_{k=0}^{\infty}\|d_k\|<\infty.
$$

Since $d_k=x_{k+1}-x_k$, this is exactly `HasFiniteLength alg.x`. The theorem `finite_length_tendsto` then applies: in a complete normed space, a sequence whose successive differences are absolutely summable converges. Hence there exists $x_\infty$ with $x_k\to x_\infty$.

The proof defines

$$
E_1=\frac12\left\|\frac1h(x_1-x_0)\right\|^2
+f(x_1)-\mathrm{sInf}(\mathrm{range}f).
$$

This is the same as $E_0$ in the Lyapunov notation, because $v_0=(1/h)(x_1-x_0)$. It also observes that

$$
M_0=E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2.
$$

Using `Real.tsum_le_of_sum_range_le`, the partial-sum bound for $\|d_{k+1}\|$ becomes an infinite-sum bound:

$$
\sum_{k=0}^{\infty}\|d_{k+1}\|\le \frac{M_0}{r}.
$$

The theorem `tsum_subtype_succ_reindex` reindexes sums over the subtype $\{k:\mathbb N\mid 1\le k\}$:

$$
\sum_{k=1}^{\infty}a_k=\sum_{n=0}^{\infty}a_{n+1}.
$$

Applying this with $a_k=\|d_k\|$ gives

$$
\sum_{k=1}^{\infty}\|x_{k+1}-x_k\|
\le \frac{M_0}{r}
=\frac1r\left(E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2\right).
$$

Similarly, the partial-sum bound for the second difference becomes

$$
\sum_{k=1}^{\infty}\|x_{k+1}-2x_k+x_{k-1}\|^2
\le 2h^2 M_0
=2h^2\left(E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2\right),
$$

using the same reindexing theorem and the identity $k=n+1$.

Finally the proof establishes criticality of the limit. Since $\sum\|d_k\|<\infty$, the terms satisfy $\|d_k\|\to0$, hence $d_k\to0$. The theorem `tendsto_zero_iff_norm_tendsto_zero` converts the norm convergence to convergence of $d_k$ to $0$. Therefore $v_k=(1/h)d_k\to0$, and also $v_{k+1}\to0$ and $v_{k+1}-v_k\to0$. Since $x_k\to x_\infty$ and $\nabla f$ is continuous, the gradients satisfy

$$
\nabla f(x_k)\to\nabla f(x_\infty),
\qquad
\nabla f(x_{k+1})\to\nabla f(x_\infty),
$$

so their difference tends to $0$.

For each $k$, the recurrence provides a subgradient $q_k\in\partial\phi(v_{k+1})$. The recurrence can be solved for $h q_k$:

$$
h q_k
=-\left(
v_{k+1}-v_k+\gamma d_{k+1}
+\beta(\nabla f(x_{k+1})-\nabla f(x_k))
+h\nabla f(x_{k+1})
\right).
$$

Every term on the right tends to the corresponding limit, so the right-hand side tends to

$$
-h\nabla f(x_\infty).
$$

Dividing by $h\neq0$ gives

$$
q_k\to -\nabla f(x_\infty).
$$

The theorem `convex_subgradient_limit_at_zero` states that if $\phi$ is continuous, $u_n\to0$, $q_n\to q_0$, and $q_n\in\partial\phi(u_n)$ for every $n$, then $q_0\in\partial\phi(0)$. The proof applies this with $u_k=v_{k+1}$, $q_k=q_k$, and $q_0=-\nabla f(x_\infty)$. Since $\phi$ is continuous by `hdf.continuous`, and $v_{k+1}\to0$, it concludes

$$
-\nabla f(x_\infty)\in\partial\phi(0),
$$

which is exactly `IsDryFrictionCritical phi f xInf`.

The final `exact` assembles the limit point $x_\infty$, the number $E_1$, the defining equality for $E_1$, finite length, convergence, dry-friction criticality, and the two quantitative series bounds.

