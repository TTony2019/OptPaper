## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/thm_4.lean`

## Lean statement
```lean
theorem IPAHDDPert_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f phi : H → ℝ)
    (e : ℕ → H) (h gamma beta L r : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDPert f phi.toEReal hdf.toEReal_mem_gammaZero e h gamma beta)
    (hf : ContDiff ℝ 1 f)
    (hL : HasLipschitzGradient (gradient f) L) (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta)) (he : Filter.Tendsto e Filter.atTop (nhds 0)) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        f (alg.x 1) - sInf (Set.range f) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (nhds xInf) ∧
      ((∀ k, ‖e k‖ ≤ r / 2) →
        tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
          (2 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2)) ∧
      IsDryFrictionCritical phi f xInf ∧
      (-gradient f xInf ∈ interior (subdifferential phi 0) →
        let q := 1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))
        0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
          ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
          ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
      (‖gradient f xInf‖ < r → IsFinitelyConvergent alg.x)
```

## Statement explanation
Let $H$ be a complete real inner product space. The theorem `IPAHDDPert_finiteLength` is a convergence theorem for a perturbed inertial proximal algorithm with Hessian-driven damping and dry friction. Its data are real-valued functions $f,\phi:H\to\mathbb R$, a perturbation sequence $e:\mathbb N\to H$, positive step parameters $h,\gamma,\beta$, a Lipschitz constant $L$, and a dry-friction radius $r$. The hypothesis $hdf:DF_r\,\phi\,r$ is a dry-friction condition on $\phi$. In the proof it is used through the following visible consequences: $\phi(0)=0$, $r>0$, the open ball $B(0,r)$ is contained in the subdifferential $\partial\phi(0)$, $\phi$ is continuous, and $\phi$ viewed as an extended-real function belongs to the convex lower-semicontinuous class needed by the proximal operator. The object $alg$ is an instance of the perturbed IPAHDD algorithm; its iterates are written $x_k=alg.x\,k$. The further assumptions are that $f$ is $C^1$, that $\nabla f$ is $L$-Lipschitz, that $L\ge0$, that $f$ is bounded below, that $h>0$, $\gamma>0$, $\beta>0$, that

$$
\gamma\ge L\left(\frac h2+\beta\right),
$$

and that $e_k\to0$ in $H$.

The conclusion asserts the existence of a limit point $x_\infty$ and an initial energy $E_1$ such that

$$
E_1=\frac12\left\|\frac1h(x_1-x_0)\right\|^2+f(x_1)-\inf(\mathrm{range}f),
$$

and then several facts. First, the iterates have finite length,

$$
\sum_{k=0}^\infty \|x_{k+1}-x_k\|<\infty,
$$

and consequently $x_k\to x_\infty$. Second, if the perturbation satisfies $\|e_k\|\le r/2$ for every $k$, then the tail total variation obeys the explicit bound

$$
\sum_{k\ge1}\|x_{k+1}-x_k\|\le \frac2r\left(E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2\right).
$$

Third, the limit is dry-friction critical:

$$
-\nabla f(x_\infty)\in\partial\phi(0).
$$

Fourth, if the stronger interior condition

$$
-\nabla f(x_\infty)\in\mathrm{int}\partial\phi(0)
$$

holds, then with

$$
q=\frac1{\sqrt{1+2h(\gamma-\beta L)/(1+\beta hL)}}
$$

one has $0<q<1$, and there is $k_0$ such that for all $k\ge k_0$,

$$
\|x_{k+1}-x_k\|\le q^{k-k_0}\|x_{k_0+1}-x_{k_0}\|,
$$

and

$$
\|x_k-x_\infty\|\le \frac{q^{k-k_0}}{1-q}\|x_{k_0+1}-x_{k_0}\|.
$$

Finally, if $\|\nabla f(x_\infty)\|<r$, then the sequence is finitely convergent, meaning that it is eventually constant.

In ordinary language, the theorem says that the perturbed inertial proximal-gradient scheme with Hessian damping and a dry-friction term always has finite length and converges; the limit satisfies the natural stationary inclusion. If the dry-friction condition is strong enough around the limit subgradient, the convergence is actually linear with an explicit ratio. If the gradient at the limit lies strictly inside the dry-friction ball, then the algorithm stops after finitely many steps.

## Lean proof
```lean
by
  rcases hpositive with ⟨hh, hg, hb⟩
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hgrad : ∀ z, HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    fun z => hasFDerivAt_gradient f hf z
  let d : ℕ → H := fun k => alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k => (1 / h) • d k
  have hdv (k : ℕ) : d k = h • v k := by
    dsimp [d, v]
    rw [smul_smul]
    field_simp [hh.ne']
    simp
  have hshift (k : ℕ) :
      ∃ s, s ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + gamma • d (k + 1) + h • s +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = h • e k) := by
    simpa [d, v, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ipahddPert_shifted_recurrence_local f phi hdf.toEReal_mem_gammaZero e h gamma beta alg hh hg k
  have hraw (k : ℕ) :
      (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
        (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
        gamma * h * ‖v (k + 1)‖ ^ 2 + h * phi (v (k + 1)) +
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) ≤
          ‖e k‖ * ‖d (k + 1)‖ := by
    obtain ⟨s, hs, hrec⟩ := hshift k
    have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
    have hinert := inner_sub_self_energy_identity_pert_local (v (k + 1)) (v k)
    have hdamp : inner ℝ (gamma • d (k + 1)) (v (k + 1)) =
        gamma * h * ‖v (k + 1)‖ ^ 2 := by
      rw [hdv (k + 1), inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have hsterm : inner ℝ (h • s) (v (k + 1)) = h * inner ℝ s (v (k + 1)) := by
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
          gamma * h * ‖v (k + 1)‖ ^ 2 + h * inner ℝ s (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) =
            inner ℝ (h • e k) (v (k + 1)) := by
      simpa only [inner_add_left, inner_sub_left, inner_zero_left, add_zero,
        hinert, hdamp, hsterm, hbetaterm, hgradterm] using hinner
    have hphi : phi (v (k + 1)) ≤ inner ℝ s (v (k + 1)) := by
      have hs0 := hs 0
      change (⟪0 - v (k + 1), s⟫_ℝ : EReal) + (phi (v (k + 1)) : EReal) ≤
        (phi 0 : EReal) at hs0
      norm_cast at hs0
      simp [hdf.value_at_zero, inner_neg_left] at hs0
      rw [real_inner_comm] at hs0
      linarith
    have hhphi := mul_le_mul_of_nonneg_left hphi hh.le
    have herr : inner ℝ (h • e k) (v (k + 1)) ≤ ‖e k‖ * ‖d (k + 1)‖ := by
      rw [hdv (k + 1), inner_smul_left, inner_smul_right]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hh.ne']
      simpa [hdv] using real_inner_le_norm (e k) (d (k + 1))
    linarith
  have hdry : ∀ u : H, r * ‖u‖ ≤ phi u :=
    subgradient_ball_exact_linear_lower_bound phi hdf.value_at_zero hdf.radius_pos hdf.ball_subset
  have hfric (k : ℕ) : r * ‖d (k + 1)‖ ≤ h * phi (v (k + 1)) := by
    have hmul := mul_le_mul_of_nonneg_left (hdry (v (k + 1))) hh.le
    have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    rw [hnorm]
    nlinarith
  have hcross_lower (k : ℕ) :
      -(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2)) ≤
        beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
    have hnormv : ‖v (k + 1)‖ = ‖d (k + 1)‖ / h := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / h)]
      ring
    have hnormgrad : ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
      simpa [d] using hL (alg.x (k + 1)) (alg.x k)
    have hprod := mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg (v (k + 1)))
    have hinter : -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) ≤
        inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      calc
        -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) =
            -((L * ‖d k‖) * ‖v (k + 1)‖) := by rw [hnormv]
        _ ≤ -(‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖) :=
          neg_le_neg hprod
        _ ≤ inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) :=
          neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hmul := mul_le_mul_of_nonneg_left hinter hb.le
    have hyoung : 2 * (‖d k‖ * ‖d (k + 1)‖) ≤ ‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖d k‖ - ‖d (k + 1)‖)]
    have hcoef : 0 ≤ beta * L / h := by positivity
    have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
    field_simp [hh.ne'] at hmul hyoung' ⊢
    nlinarith
  let c : ℝ := beta * L / (2 * h)
  let E : ℕ → ℝ := fun k =>
    (1 / 2 : ℝ) * ‖v k‖ ^ 2 + f (alg.x (k + 1)) - sInf (Set.range f)
  let M : ℕ → ℝ := fun k => E k + c * ‖d k‖ ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hbounded : BddBelow (Set.range f) := by
    obtain ⟨a, ha⟩ := hbelow
    exact ⟨a, fun y hy => by rcases hy with ⟨x, rfl⟩; exact ha x⟩
  have hM_nonneg (k : ℕ) : 0 ≤ M k := by
    have hinf : sInf (Set.range f) ≤ f (alg.x (k + 1)) :=
      csInf_le hbounded ⟨alg.x (k + 1), rfl⟩
    dsimp [M, E]
    have hkin : 0 ≤ f (alg.x (k + 1)) - sInf (Set.range f) := sub_nonneg.mpr hinf
    have hvel : 0 ≤ (1 / 2 : ℝ) * ‖v k‖ ^ 2 := by positivity
    have hcorr : 0 ≤ c * ‖d k‖ ^ 2 := mul_nonneg hc (sq_nonneg _)
    linarith
  have hstep (k : ℕ) :
      M (k + 1) - M k +
          (1 / (2 * h ^ 2) : ℝ) *
            ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
          (r - ‖e k‖) * ‖d (k + 1)‖ ≤ 0 := by
    have hsmooth := smooth_descent_of_fderiv_lipschitz_pert_local f L hf hL
      (alg.x (k + 1)) (alg.x (k + 2))
    have hsmooth' :
        f (alg.x (k + 2)) - f (alg.x (k + 1)) -
            (L / 2) * ‖d (k + 1)‖ ^ 2 ≤
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
      simpa [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsmooth
    have hcoef : c ≤ gamma / h - L / 2 - c := by
      dsimp [c]
      field_simp [hh.ne']
      nlinarith [hgamma]
    have hacc : d (k + 1) - d k =
        alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k := by
      dsimp [d]
      abel
    have haccnorm :
        (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 =
          (1 / (2 * h ^ 2) : ℝ) *
            ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 := by
      rw [← hacc]
      have hdsub : d (k + 1) - d k = h • (v (k + 1) - v k) := by
        rw [hdv (k + 1), hdv k, smul_sub]
      rw [hdsub, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      field_simp [hh.ne']
    have hnorm : ‖d (k + 1)‖ = h * ‖v (k + 1)‖ := by
      rw [hdv (k + 1), norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hdamp : gamma * h * ‖v (k + 1)‖ ^ 2 =
        (gamma / h) * ‖d (k + 1)‖ ^ 2 := by
      rw [hnorm]
      field_simp [hh.ne']
    have hraw' := hraw k
    have hfric' := hfric k
    have hcross' := hcross_lower k
    rw [haccnorm, hdamp] at hraw'
    dsimp [M, E, c]
    nlinarith
  have he_norm : Filter.Tendsto (fun k => ‖e k‖) Filter.atTop (nhds 0) := by
    simpa using he.norm
  have he_tail : ∀ᶠ k : ℕ in Filter.atTop, ‖e k‖ < r / 2 := by
    exact he_norm.eventually (eventually_lt_nhds (by simpa using (half_pos hdf.radius_pos)))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 he_tail
  have htailstep (k : ℕ) (hk : K ≤ k) :
      M (k + 1) - M k +
          (1 / (2 * h ^ 2) : ℝ) *
            ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
          (r / 2) * ‖d (k + 1)‖ ≤ 0 := by
    have hkerr : ‖e k‖ ≤ r / 2 := (hK k hk).le
    have hcoeff : r / 2 ≤ r - ‖e k‖ := by linarith
    have hlin := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (d (k + 1)))
    linarith [hstep k]
  have htailtel (N : ℕ) :
      M (K + N) + ∑ i ∈ Finset.range N,
        ((1 / (2 * h ^ 2) : ℝ) *
          ‖alg.x (K + i + 2) - 2 • alg.x (K + i + 1) + alg.x (K + i)‖ ^ 2 +
          (r / 2) * ‖d (K + i + 1)‖) ≤ M K := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        have hs : M (K + N + 1) - M (K + N) +
            (1 / (2 * h ^ 2) : ℝ) *
              ‖alg.x (K + N + 2) - 2 • alg.x (K + N + 1) + alg.x (K + N)‖ ^ 2 +
            (r / 2) * ‖d (K + N + 1)‖ ≤ 0 := by
          convert htailstep (K + N) (by omega) using 1 <;> ring
        simp only [← Nat.add_assoc]
        linarith
  have htailsum (N : ℕ) :
      ∑ i ∈ Finset.range N, ‖d (K + i + 1)‖ ≤ M K / (r / 2) := by
    have hacc_nonneg : 0 ≤ ∑ i ∈ Finset.range N,
        (1 / (2 * h ^ 2) : ℝ) *
          ‖alg.x (K + i + 2) - 2 • alg.x (K + i + 1) + alg.x (K + i)‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro i hi
      positivity
    have hlen_nonneg : 0 ≤ ∑ i ∈ Finset.range N, (r / 2) * ‖d (K + i + 1)‖ := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (half_pos hdf.radius_pos).le (norm_nonneg _)
    have hle := htailtel N
    rw [Finset.sum_add_distrib] at hle
    have hfactor : (∑ i ∈ Finset.range N, (r / 2) * ‖d (K + i + 1)‖) =
        (r / 2) * ∑ i ∈ Finset.range N, ‖d (K + i + 1)‖ := by
      rw [Finset.mul_sum]
    rw [hfactor] at hle
    apply (le_div_iff₀ (half_pos hdf.radius_pos)).mpr
    linarith [hM_nonneg (K + N)]
  have hsTail : Summable (fun n => ‖d (K + n + 1)‖) :=
    summable_of_sum_range_le (fun n => norm_nonneg _) htailsum
  have hs : Summable (fun n => ‖d n‖) := by
    apply (summable_nat_add_iff (f := fun n => ‖d n‖) (K + 1)).mp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsTail
  have hfinite : HasFiniteLength alg.x := by
    unfold HasFiniteLength
    simpa [d] using hs
  obtain ⟨xInf, hxInf⟩ := finite_length_tendsto_pert_local alg.x hfinite
  let E1 : ℝ := (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
    f (alg.x 1) - sInf (Set.range f)
  have hE1 : E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
      f (alg.x 1) - sInf (Set.range f) := rfl
  have hM0 : M 0 = E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2 := by
    dsimp [M, E, c, v, d, E1]
  have hlength : (∀ k, ‖e k‖ ≤ r / 2) →
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (2 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
    intro hehalf
    have hzero_step (k : ℕ) :
        M (k + 1) - M k +
            (1 / (2 * h ^ 2) : ℝ) *
              ‖alg.x (k + 2) - 2 • alg.x (k + 1) + alg.x k‖ ^ 2 +
            (r / 2) * ‖d (k + 1)‖ ≤ 0 := by
      have hcoeff : r / 2 ≤ r - ‖e k‖ := by linarith [hehalf k]
      have hmul := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (d (k + 1)))
      linarith [hstep k]
    have htel (N : ℕ) : M N + ∑ i ∈ Finset.range N,
        ((1 / (2 * h ^ 2) : ℝ) *
          ‖alg.x (i + 2) - 2 • alg.x (i + 1) + alg.x i‖ ^ 2 +
          (r / 2) * ‖d (i + 1)‖) ≤ M 0 := by
      induction N with
      | zero => simp
      | succ N ih =>
          rw [Finset.sum_range_succ]
          have hs : M (N + 1) - M N +
              (1 / (2 * h ^ 2) : ℝ) *
                ‖alg.x (N + 2) - 2 • alg.x (N + 1) + alg.x N‖ ^ 2 +
              (r / 2) * ‖d (N + 1)‖ ≤ 0 := hzero_step N
          linarith
    have hsum (N : ℕ) : ∑ i ∈ Finset.range N, ‖d (i + 1)‖ ≤ M 0 / (r / 2) := by
      have hacc_nonneg : 0 ≤ ∑ i ∈ Finset.range N,
          (1 / (2 * h ^ 2) : ℝ) *
            ‖alg.x (i + 2) - 2 • alg.x (i + 1) + alg.x i‖ ^ 2 := by
        apply Finset.sum_nonneg
        intro i hi
        positivity
      have hle := htel N
      rw [Finset.sum_add_distrib] at hle
      have hfactor : (∑ i ∈ Finset.range N, (r / 2) * ‖d (i + 1)‖) =
          (r / 2) * ∑ i ∈ Finset.range N, ‖d (i + 1)‖ := by
        rw [Finset.mul_sum]
      rw [hfactor] at hle
      apply (le_div_iff₀ (half_pos hdf.radius_pos)).mpr
      linarith [hM_nonneg N]
    have htsum : tsum (fun i => ‖d (i + 1)‖) ≤ M 0 / (r / 2) :=
      Real.tsum_le_of_sum_range_le (fun i => norm_nonneg _) hsum
    change tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n => ‖d n‖) k.1) ≤ _
    calc
      tsum (fun k : {k : ℕ // 1 ≤ k} => (fun n => ‖d n‖) k.1) =
          tsum (fun n => ‖d (n + 1)‖) :=
            tsum_subtype_succ_reindex (fun n : ℕ => ‖d n‖)
      _ ≤ M 0 / (r / 2) := htsum
      _ = (2 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) := by
          rw [hM0]
          field_simp [hdf.radius_pos.ne'] <;> ring
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
  have hgradlim : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop
      (nhds (gradient f xInf)) := (hC1.tendsto xInf).comp hxInf
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1))) Filter.atTop
      (nhds (gradient f xInf)) := (hC1.tendsto xInf).comp hxInf_succ
  have hgrad_diff : Filter.Tendsto
      (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) :=
    by simpa using hgrad_succ.sub hgradlim
  let s : ℕ → H := fun k => Classical.choose (hshift k)
  have hsmem (k : ℕ) : s k ∈ subdifferential phi (v (k + 1)) :=
    (Classical.choose_spec (hshift k)).1
  have hsrec (k : ℕ) :
      v (k + 1) - v k + gamma • d (k + 1) + h • s k +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
        h • gradient f (alg.x (k + 1)) = h • e k :=
    (Classical.choose_spec (hshift k)).2
  have hssolve (k : ℕ) : h • s k = h • e k -
      (v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
        h • gradient f (alg.x (k + 1))) := by
    rw [← hsrec k]
    abel
  have hdamp : Filter.Tendsto (fun k => gamma • d (k + 1)) Filter.atTop (nhds 0) :=
    by simpa using hd_succ.const_smul gamma
  have hbeta : Filter.Tendsto
      (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) Filter.atTop (nhds 0) :=
    by simpa using hgrad_diff.const_smul beta
  have herr : Filter.Tendsto (fun k => h • e k) Filter.atTop (nhds 0) :=
    by simpa using he.const_smul h
  have hgrad_term : Filter.Tendsto (fun k => h • gradient f (alg.x (k + 1))) Filter.atTop
      (nhds (h • gradient f xInf)) := hgrad_succ.const_smul h
  have hright : Filter.Tendsto (fun k => h • e k -
      (v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
        h • gradient f (alg.x (k + 1)))) Filter.atTop (nhds (-(h • gradient f xInf))) := by
    simpa using herr.sub (((hv_diff.add hdamp).add hbeta).add hgrad_term)
  have hs_scaled : Filter.Tendsto (fun k => h • s k) Filter.atTop
      (nhds (h • (-gradient f xInf))) := by
    convert hright using 1
    · ext k
      rw [hssolve]
    · simp
  have hsLim : Filter.Tendsto s Filter.atTop (nhds (-gradient f xInf)) := by
    have hs' := hs_scaled.const_smul (1 / h)
    have hsfun : (fun k => (1 / h) • (h • s k)) = s := by
      funext k
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    have hslim : (1 / h) • (h • (-gradient f xInf)) = -gradient f xInf := by
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    rw [hsfun, hslim] at hs'
    exact hs'
  have hcritical : IsDryFrictionCritical phi f xInf := by
    unfold IsDryFrictionCritical
    exact convex_subgradient_limit_at_zero phi (fun k => v (k + 1)) s
      (-gradient f xInf) hdf.continuous hv_succ hsLim hsmem
  have hstop : ‖gradient f xInf‖ < r → IsFinitelyConvergent alg.x := by
    intro hmargin
    let D : ℝ := 1 + h * gamma
    let lam : ℝ := h / D
    let z : ℕ → H := fun k =>
      (1 / (h * D)) • d k -
        (beta / D) • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) -
        lam • gradient f (alg.x (k + 1)) + lam • e k
    have hD : 0 < D := by
      dsimp [D]
      nlinarith [mul_pos hh hg]
    have hlam : 0 < lam := by
      dsimp [lam]
      exact div_pos hh hD
    have hzlim : Filter.Tendsto z Filter.atTop (nhds (lam • (-gradient f xInf))) := by
      dsimp [z]
      simpa using (((hd.const_smul (1 / (h * D))).sub
        (hgrad_diff.const_smul (beta / D))).sub (hgrad_succ.const_smul lam)).add
          (he.const_smul lam)
    have hscaled : Filter.Tendsto (fun k => lam⁻¹ • z k) Filter.atTop
        (nhds (-gradient f xInf)) := by
      have hz := hzlim.const_smul lam⁻¹
      simpa only [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul] using hz
    have hsmall : ∀ᶠ k : ℕ in Filter.atTop, ‖lam⁻¹ • z k‖ < r := by
      exact hscaled.norm.eventually (eventually_lt_nhds (by simpa using hmargin))
    obtain ⟨kStop, hkStop⟩ := Filter.eventually_atTop.1 hsmall
    have hnext : ∀ j ≥ kStop, alg.x (j + 2) = alg.x (j + 1) := by
      intro j hj
      have hmem : lam⁻¹ • z j ∈ subdifferential phi 0 := hdf.ball_subset (by
        simpa [Metric.mem_ball, dist_eq_norm] using hkStop j hj)
      have hzero : IsProximalPoint phi lam (z j) 0 := by
        refine ⟨hlam, ?_⟩
        simpa [sub_zero] using hmem
      have hp : IsProximalPoint phi lam (z j)
          (ERealFunction.scaledProximityOperator phi.toEReal hdf.toEReal_mem_gammaZero
            ⟨lam, hlam⟩ (z j)) :=
        ⟨hlam, ERealFunction.scaledProximityOperator_residual_mem
          hdf.toEReal_mem_gammaZero ⟨lam, hlam⟩ (z j)⟩
      have hpzero :
          ERealFunction.scaledProximityOperator phi.toEReal hdf.toEReal_mem_gammaZero
            ⟨lam, hlam⟩ (z j) = 0 :=
        proximal_point_eq_zero_pert_local phi lam hlam (z j) _ hp hzero
      have hupdate := alg.update j
      rw [alg.aux] at hupdate
      have hz : (1 / (h * (1 + h * gamma))) • d j -
          (beta / (1 + h * gamma)) • (gradient f (alg.x (j + 1)) - gradient f (alg.x j)) -
          (h / (1 + h * gamma)) • gradient f (alg.x (j + 1)) +
          (h / (1 + h * gamma)) • e j = z j := rfl
      rw [hz, hpzero] at hupdate
      simpa using hupdate
    apply eventually_constant_of_eventual_successor_eq alg.x (kStop + 1)
    intro k hk
    have hsucc := hnext (k - 1) (by omega)
    have hindex : k - 1 + 2 = k + 1 := by omega
    have hindex' : k - 1 + 1 = k := by omega
    rw [hindex, hindex'] at hsucc
    exact hsucc
  refine ⟨xInf, E1, hE1, hfinite, hxInf, hlength, hcritical, ?_, hstop⟩
  intro hinterior
  dsimp
  have hq := ipahdd_rate_mem_Ioo h gamma beta L hh hg hb hL_nonneg hgamma
  refine ⟨hq.1, hq.2, ?_⟩
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hinterior)
  let eps : ℝ := rho / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hgradtail : ∀ᶠ k : ℕ in Filter.atTop,
      ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ < eps := by
    have hzero : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)) - gradient f xInf)
        Filter.atTop (nhds 0) := by
      simpa using hgrad_succ.sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => gradient f xInf) Filter.atTop (nhds (gradient f xInf)))
    simpa using hzero.norm.eventually
      (eventually_lt_nhds (show ‖(0 : H)‖ < eps by simpa using heps))
  have herrtail : ∀ᶠ k : ℕ in Filter.atTop, ‖e k‖ ≤ eps / 2 := by
    have hstrict : ∀ᶠ k : ℕ in Filter.atTop, ‖e k‖ < eps / 2 :=
      he_norm.eventually (eventually_lt_nhds (by simpa using half_pos heps))
    filter_upwards [hstrict] with k hk
    exact hk.le
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 (hgradtail.and herrtail)
  have htranslated (k : ℕ) (hk : k0 ≤ k) (u : H) (hu : ‖u‖ ≤ 1) :
      -gradient f (alg.x (k + 1)) + eps • u ∈ subdifferential phi 0 := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hrewrite :
        (-gradient f (alg.x (k + 1)) + eps • u) - -gradient f xInf =
          -(gradient f (alg.x (k + 1)) - gradient f xInf) + eps • u := by
      abel
    rw [hrewrite]
    calc
      ‖-(gradient f (alg.x (k + 1)) - gradient f xInf) + eps • u‖ ≤
          ‖-(gradient f (alg.x (k + 1)) - gradient f xInf)‖ + ‖eps • u‖ := norm_add_le _ _
      _ = ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ + ‖eps • u‖ := by rw [norm_neg]
      _ = ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ + eps * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos heps]
      _ < eps + eps * ‖u‖ := by gcongr; exact (hk0 k hk).1
      _ ≤ eps + eps := by
        have hmul : eps * ‖u‖ ≤ eps := by
          simpa using (mul_le_mul_of_nonneg_left hu heps.le)
        linarith
      _ = rho := by dsimp [eps]; ring
  have hfricInterior (k : ℕ) (hk : k0 ≤ k) :
      eps * ‖v (k + 1)‖ ≤
        phi (v (k + 1)) + inner ℝ (gradient f (alg.x (k + 1))) (v (k + 1)) := by
    by_cases hv0 : v (k + 1) = 0
    · simp [hv0, hdf.value_at_zero]
    · let u : H := (‖v (k + 1)‖)⁻¹ • v (k + 1)
      have hvpos : 0 < ‖v (k + 1)‖ := norm_pos_iff.mpr hv0
      have hu : ‖u‖ ≤ 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
        field_simp [hvpos.ne']
        norm_num
      have hmem := htranslated k hk u hu
      have hsub := hmem (v (k + 1))
      have hinner : inner ℝ u (v (k + 1)) = ‖v (k + 1)‖ := by
        dsimp [u]
        rw [inner_smul_left, real_inner_self_eq_norm_sq]
        simp only [map_inv₀, starRingEnd_apply, star_trivial]
        field_simp [hvpos.ne']
      change (⟪v (k + 1) - 0, -gradient f (alg.x (k + 1)) + eps • u⟫_ℝ : EReal) +
          (phi 0 : EReal) ≤ (phi (v (k + 1)) : EReal) at hsub
      norm_cast at hsub
      simp only [sub_zero] at hsub
      rw [hdf.value_at_zero, inner_add_right, inner_neg_right, inner_smul_right] at hsub
      rw [real_inner_comm (gradient f (alg.x (k + 1))) (v (k + 1)),
        real_inner_comm u (v (k + 1)), hinner] at hsub
      linarith
  have hsq_contract (k : ℕ) (hk : k0 ≤ k) :
      (1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖d (k + 1)‖ ^ 2 ≤
        (1 + beta * h * L) * ‖d k‖ ^ 2 := by
    have hnorm (j : ℕ) : ‖d j‖ = h * ‖v j‖ := by
      rw [hdv j, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    have hrawtwo := mul_le_mul_of_nonneg_left (hraw k) (show (0 : ℝ) ≤ 2 by norm_num)
    have hfric := mul_le_mul_of_nonneg_left (hfricInterior k hk) hh.le
    have hcross := hcross_lower k
    have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 := by positivity
    have hgradscale :
        inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) =
          h * inner ℝ (gradient f (alg.x (k + 1))) (v (k + 1)) := by
      rw [hdv (k + 1), inner_smul_right]
    have hfricscale : h * eps * ‖v (k + 1)‖ ≤
        h * phi (v (k + 1)) + inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
      rw [hgradscale]
      nlinarith [hfric]
    have hcrossv :
        -(beta * L * h * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2)) ≤
          2 * beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      calc
        -(beta * L * h * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2)) =
            2 * (-(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2))) := by
              rw [hnorm k, hnorm (k + 1)]
              field_simp [hh.ne']
        _ ≤ 2 * (beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k))
            (v (k + 1))) := mul_le_mul_of_nonneg_left hcross (by norm_num)
        _ = _ := by ring
    have herrscaled : 2 * ‖e k‖ * ‖d (k + 1)‖ ≤ h * eps * ‖v (k + 1)‖ := by
      have hm := mul_le_mul_of_nonneg_right (hk0 k hk).2
        (show 0 ≤ 2 * ‖d (k + 1)‖ by positivity)
      calc
        2 * ‖e k‖ * ‖d (k + 1)‖ =
            ‖e k‖ * (2 * (h * ‖v (k + 1)‖)) := by
              rw [hnorm (k + 1)]
              ring
        _ ≤ (eps / 2) * (2 * (h * ‖v (k + 1)‖)) := by
              simpa [hnorm (k + 1)] using hm
        _ = h * eps * ‖v (k + 1)‖ := by ring
    have hvcontract :
        (1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖v (k + 1)‖ ^ 2 ≤
          (1 + beta * h * L) * ‖v k‖ ^ 2 := by
      have hepsnorm : 0 ≤ h * eps * ‖v (k + 1)‖ := by positivity
      nlinarith [hrawtwo, hcrossv, hfricscale, herrscaled]
    rw [hnorm k, hnorm (k + 1)]
    calc
      (1 + beta * h * L + 2 * h * (gamma - beta * L)) * (h * ‖v (k + 1)‖) ^ 2 =
          h ^ 2 * ((1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖v (k + 1)‖ ^ 2) := by ring
      _ ≤ h ^ 2 * ((1 + beta * h * L) * ‖v k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hvcontract (sq_nonneg h)
      _ = (1 + beta * h * L) * (h * ‖v k‖) ^ 2 := by ring
  have hgap : 0 < gamma - beta * L := by
    rcases hL_nonneg.eq_or_lt with rfl | hLpos
    · simpa using hg
    · have hstrict : beta * L < L * (h / 2 + beta) := by
        nlinarith [mul_pos hLpos hh]
      nlinarith [hgamma, hstrict]
  have hB : 0 < 1 + beta * h * L := by positivity
  have hA : 0 < 1 + beta * h * L + 2 * h * (gamma - beta * L) := by
    nlinarith [mul_pos hh hgap]
  have hq_sq :
      (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ 2 *
          (1 + beta * h * L + 2 * h * (gamma - beta * L)) = 1 + beta * h * L := by
    have hratio : (1 + beta * h * L + 2 * h * (gamma - beta * L)) /
        (1 + beta * h * L) = 1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L) := by
      field_simp [hB.ne']
    have hhelper := ipahddPert_q_sq_mul_A_eq_B_local h gamma beta L hh hB hgap
    dsimp only at hhelper
    rw [hratio] at hhelper
    exact hhelper
  have hcontract (k : ℕ) (hk : k0 ≤ k) : ‖d (k + 1)‖ ≤
      (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) * ‖d k‖ := by
    have hsquare : ‖d (k + 1)‖ ^ 2 ≤
        ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
          (1 + beta * h * L))) * ‖d k‖) ^ 2 := by
      have hmain := hsq_contract k hk
      have hrewrite : 1 + beta * h * L =
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ 2 *
            (1 + beta * h * L + 2 * h * (gamma - beta * L)) := hq_sq.symm
      rw [hrewrite] at hmain
      have hmul := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hA.le)
      field_simp [hA.ne'] at hmul
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq.1.le (norm_nonneg _))).mp hsquare
  have hgeom (n : ℕ) : ‖d (k0 + n)‖ ≤
      (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n * ‖d k0‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        ‖d (k0 + (n + 1))‖ = ‖d ((k0 + n) + 1)‖ := by congr 2
        _ ≤ (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) * ‖d (k0 + n)‖ := hcontract _ (Nat.le_add_right k0 n)
        _ ≤ (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) * ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ n * ‖d k0‖) := mul_le_mul_of_nonneg_left ih hq.1.le
        _ = (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ (n + 1) * ‖d k0‖ := by rw [pow_succ]; ring
  have hsum (n p : ℕ) :
      (∑ i ∈ Finset.range p, (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
        (1 + beta * h * L))) ^ (n + i)) ≤
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
          (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)))) :=
    geometric_range_sum_le_pert_local _ hq.1.le hq.2 n p
  have htel (n p : ℕ) : alg.x (k0 + n + p) - alg.x (k0 + n) =
      ∑ i ∈ Finset.range p, d (k0 + n + i) := by
    induction p with
    | zero => simp
    | succ p ih =>
      rw [Finset.sum_range_succ, ← ih]
      dsimp [d]
      convert (show alg.x (k0 + n + p + 1) - alg.x (k0 + n) =
        (alg.x (k0 + n + p) - alg.x (k0 + n)) +
          (alg.x (k0 + n + p + 1) - alg.x (k0 + n + p)) by abel) using 1
  have htail (n p : ℕ) : ‖alg.x (k0 + n) - alg.x (k0 + n + p)‖ ≤
      (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
        (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)))) * ‖d k0‖ := by
    calc
      ‖alg.x (k0 + n) - alg.x (k0 + n + p)‖ = ‖alg.x (k0 + n + p) - alg.x (k0 + n)‖ := by
        rw [← norm_neg (alg.x (k0 + n) - alg.x (k0 + n + p))]; congr 1 <;> abel
      _ = ‖∑ i ∈ Finset.range p, d (k0 + n + i)‖ := by rw [htel]
      _ ≤ ∑ i ∈ Finset.range p, ‖d (k0 + n + i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range p, (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
          (1 + beta * h * L))) ^ (n + i) * ‖d k0‖ := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hgeom (n + i)
      _ = (∑ i ∈ Finset.range p, (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
          (1 + beta * h * L))) ^ (n + i)) * ‖d k0‖ := by rw [Finset.sum_mul]
      _ ≤ ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
          (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))))) * ‖d k0‖ :=
        mul_le_mul_of_nonneg_right (hsum n p) (norm_nonneg _)
  refine ⟨k0, ?_⟩
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hdist : ‖alg.x (k0 + n) - xInf‖ ≤
      (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
        (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L)))) * ‖d k0‖ := by
    apply le_of_tendsto ((tendsto_const_nhds.sub
      (hxInf.comp (Filter.tendsto_add_atTop_nat (k0 + n)))).norm)
    filter_upwards with p
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail n p
  constructor
  · simpa [d] using hgeom n
  · simpa [d] using hdist
```

## Proof explanation
The proof begins by unpacking $h>0$, $\gamma>0$, and $\beta>0$ from `hpositive` using `rcases`. It records two calculus facts: $\nabla f$ is continuous by `continuous_gradient_of_contDiff`, and at every point $z$,

$$
f\text{ has Fr\'echet derivative }y\mapsto\langle \nabla f(z),y\rangle
$$

by `hasFDerivAt_gradient`. These facts are used later to pass gradients through limits.

Next the proof introduces the discrete velocity and increment notation

$$
d_k=x_{k+1}-x_k,\qquad v_k=\frac1h d_k.
$$

The identity $d_k=h v_k$ is proved by rewriting with `smul_smul`, clearing the denominator $h\ne0$ using `field_simp`, and simplifying. The lemma `ipahddPert_shifted_recurrence_local` is then applied. It supplies, for each $k$, an element $s_k\in\partial\phi(v_{k+1})$ such that

$$
v_{k+1}-v_k+\gamma d_{k+1}+h s_k
+\beta(\nabla f(x_{k+1})-\nabla f(x_k))
+h\nabla f(x_{k+1})
=h e_k.
$$

This is the shifted recurrence for the perturbed IPAHDD algorithm, expressed in the variables $d_k$ and $v_k$. The tactic `simpa` rewrites the indices into the local notation.

From this recurrence the proof derives a basic energy inequality. Taking the inner product with $v_{k+1}$, it uses the identity

$$
\langle v_{k+1}-v_k,v_{k+1}\rangle
=\frac12\|v_{k+1}\|^2-\frac12\|v_k\|^2+\frac12\|v_{k+1}-v_k\|^2
$$

from `inner_sub_self_energy_identity_pert_local`. The damping term becomes

$$
\langle \gamma d_{k+1},v_{k+1}\rangle
=\gamma h\|v_{k+1}\|^2,
$$

because $d_{k+1}=h v_{k+1}$. The subgradient term $\langle h s_k,v_{k+1}\rangle$ is handled by the subgradient inequality for $s_k\in\partial\phi(v_{k+1})$ evaluated at $0$, using $\phi(0)=0$, which gives

$$
\phi(v_{k+1})\le \langle s_k,v_{k+1}\rangle.
$$

Finally the right-hand side is bounded by Cauchy–Schwarz:

$$
\langle h e_k,v_{k+1}\rangle\le \|e_k\|\,\|d_{k+1}\|.
$$

The result is the inequality

$$
\frac12\|v_{k+1}\|^2-\frac12\|v_k\|^2
+\frac12\|v_{k+1}-v_k\|^2
+\gamma h\|v_{k+1}\|^2+h\phi(v_{k+1})
+\beta\langle \nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle
+\langle \nabla f(x_{k+1}),d_{k+1}\rangle
\le \|e_k\|\,\|d_{k+1}\|.
$$

The dry-friction hypothesis is then used through `subgradient_ball_exact_linear_lower_bound`: since $\phi(0)=0$, $r>0$, and $B(0,r)\subseteq\partial\phi(0)$, one has

$$
r\|u\|\le \phi(u)
$$

for every $u\in H$. Applying this to $u=v_{k+1}$ and multiplying by $h>0$ gives

$$
r\|d_{k+1}\|\le h\phi(v_{k+1}),
$$

because $\|d_{k+1}\|=h\|v_{k+1}\|$.

The next estimate controls the Hessian-driving term from below. Since $\nabla f$ is $L$-Lipschitz,

$$
\|\nabla f(x_{k+1})-\nabla f(x_k)\|\le L\|d_k\|.
$$

Cauchy–Schwarz and the identity $\|v_{k+1}\|=\|d_{k+1}\|/h$ give

$$
-\frac{\beta L}{2h}\bigl(\|d_k\|^2+\|d_{k+1}\|^2\bigr)
\le
\beta\langle \nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle.
$$

The proof uses the elementary Young inequality

$$
2\|d_k\|\,\|d_{k+1}\|
\le \|d_k\|^2+\|d_{k+1}\|^2.
$$

Then the proof defines

$$
c=\frac{\beta L}{2h},\qquad
E_k=\frac12\|v_k\|^2+f(x_{k+1})-\inf(\mathrm{range}f),\qquad
M_k=E_k+c\|d_k\|^2.
$$

The bounded-below hypothesis on $f$ gives `BddBelow (Set.range f)`, hence $\inf(\mathrm{range}f)\le f(x_{k+1})$, so every $M_k\ge0$. The core descent inequality is

$$
M_{k+1}-M_k
+\frac1{2h^2}\|x_{k+2}-2x_{k+1}+x_k\|^2
+(r-\|e_k\|)\|d_{k+1}\|\le0.
$$

To obtain it, the proof uses `smooth_descent_of_fderiv_lipschitz_pert_local`, which says that for a $C^1$ function with $L$-Lipschitz gradient,

$$
f(y)\le f(x)+\langle \nabla f(x),y-x\rangle+\frac L2\|y-x\|^2.
$$

Applied to $x=x_{k+1}$ and $y=x_{k+2}$, this controls the change $f(x_{k+2})-f(x_{k+1})$. The acceleration identity

$$
d_{k+1}-d_k=x_{k+2}-2x_{k+1}+x_k
$$

and the identity

$$
\frac12\|v_{k+1}-v_k\|^2
=\frac1{2h^2}\|x_{k+2}-2x_{k+1}+x_k\|^2
$$

convert the previous energy inequality into the form above. The inequality

$$
c\le \frac{\gamma}{h}-\frac L2-c
$$

is derived from

$$
\gamma\ge L\left(\frac h2+\beta\right)
$$

by elementary algebra, and `nlinarith` combines the scalar inequalities.

Since $e_k\to0$, eventually $\|e_k\|<r/2$. Choosing $K$ beyond that threshold, the proof obtains for $k\ge K$

$$
M_{k+1}-M_k
+\frac1{2h^2}\|x_{k+2}-2x_{k+1}+x_k\|^2
+\frac r2\|d_{k+1}\|\le0.
$$

Telescoping this inequality from $K$ to $K+N$ gives

$$
M_{K+N}
+\sum_{i=0}^{N-1}\left(
\frac1{2h^2}\|x_{K+i+2}-2x_{K+i+1}+x_{K+i}\|^2
+\frac r2\|d_{K+i+1}\|\right)
\le M_K.
$$

Because all $M_k\ge0$, the partial sums of $\|d_{K+i+1}\|$ are bounded by $M_K/(r/2)$. Hence the tail of $\|d_k\|$ is summable, and therefore the whole sequence $\|d_k\|$ is summable. This proves `HasFiniteLength alg.x`. Then `finite_length_tendsto_pert_local` applies: a sequence whose successive increments have summable norms converges in the complete space $H$. Thus there is $x_\infty$ with $x_k\to x_\infty$.

The same telescoping argument, now started at $0$ and assuming $\|e_k\|\le r/2$ for all $k$, gives the explicit finite-length bound. The proof defines

$$
E_1=\frac12\left\|\frac1h(x_1-x_0)\right\|^2+f(x_1)-\inf(\mathrm{range}f).
$$

It shows $M_0=E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2$. Then for every $N$,

$$
\sum_{i=0}^{N-1}\|d_{i+1}\|\le \frac{M_0}{r/2}.
$$

Passing to the infinite sum uses `Real.tsum_le_of_sum_range_le`. The reindexing

$$
\sum_{k\ge1} a_k=\sum_{n\ge0}a_{n+1}
$$

is exactly `tsum_subtype_succ_reindex`, which converts the subtype sum over $k\ge1$ into the ordinary tail sum. Simplifying $M_0/(r/2)$ with `field_simp` and `ring` gives the stated bound.

At this point the proof knows $\|d_k\|\to0$, hence $d_k\to0$. Therefore $v_k\to0$, $v_{k+1}\to0$, $v_{k+1}-v_k\to0$, and $x_{k+1}\to x_\infty$. Continuity of $\nabla f$ gives

$$
\nabla f(x_k)\to\nabla f(x_\infty),\qquad
\nabla f(x_{k+1})\to\nabla f(x_\infty),
$$

and hence the gradient difference tends to $0$.

The proof then chooses the subgradients $s_k$ supplied by the shifted recurrence. From the recurrence,

$$
h s_k
=
h e_k
-\left(v_{k+1}-v_k+\gamma d_{k+1}
+\beta(\nabla f(x_{k+1})-\nabla f(x_k))
+h\nabla f(x_{k+1})\right).
$$

All terms on the right except $h\nabla f(x_{k+1})$ tend to $0$, while $h\nabla f(x_{k+1})\to h\nabla f(x_\infty)$. Therefore

$$
h s_k\to -h\nabla f(x_\infty),
$$

and multiplying by $1/h$ gives

$$
s_k\to -\nabla f(x_\infty).
$$

Since $s_k\in\partial\phi(v_{k+1})$, $v_{k+1}\to0$, and $\phi$ is continuous, the theorem `convex_subgradient_limit_at_zero` applies. It states that if $u_n\to0$, $q_n\to q_0$, and $q_n\in\partial\phi(u_n)$, then $q_0\in\partial\phi(0)$. Here this yields

$$
-\nabla f(x_\infty)\in\partial\phi(0),
$$

which is precisely `IsDryFrictionCritical phi f xInf`.

The finite-convergence part is proved under the extra assumption $\|\nabla f(x_\infty)\|<r$. The proof defines

$$
D=1+h\gamma,\qquad \lambda=\frac hD,
$$

and

$$
z_k
=
\frac1{hD}d_k
-\frac{\beta}{D}(\nabla f(x_{k+1})-\nabla f(x_k))
-\lambda\nabla f(x_{k+1})
+\lambda e_k.
$$

Using the limits above, $z_k\to \lambda(-\nabla f(x_\infty))$, hence

$$
\lambda^{-1}z_k\to -\nabla f(x_\infty).
$$

Because $\|\nabla f(x_\infty)\|<r$, eventually $\|\lambda^{-1}z_k\|<r$. By the dry-friction ball inclusion, this means

$$
\lambda^{-1}z_k\in\partial\phi(0).
$$

Thus $0$ is a proximal point of $\phi$ at $z_k$ with parameter $\lambda$. On the other hand, the scaled proximal operator produces a proximal point with residual in the subdifferential, by `scaledProximityOperator_residual_mem`. The lemma `proximal_point_eq_zero_pert_local` says that if both $p$ and $0$ are proximal points of $\phi$ at the same point $z$ with the same positive parameter $\lambda$, then $p=0$. Therefore the proximal update at $z_k$ is zero for all large $k$. Substituting this into the algorithm update equation `alg.update` together with `alg.aux` gives

$$
x_{k+2}=x_{k+1}
$$

for all sufficiently large $k$. Then `eventually_constant_of_eventual_successor_eq` converts eventual equality of successive terms into `IsFinitelyConvergent alg.x`.

The final part assumes

$$
-\nabla f(x_\infty)\in\mathrm{int}\partial\phi(0).
$$

Then there is $\rho>0$ such that the ball of radius $\rho$ around $-\nabla f(x_\infty)$ is contained in $\partial\phi(0)$. The proof sets $\varepsilon=\rho/2$. Since $\nabla f(x_{k+1})\to\nabla f(x_\infty)$ and $e_k\to0$, eventually

$$
\|\nabla f(x_{k+1})-\nabla f(x_\infty)\|<\varepsilon,
\qquad
\|e_k\|\le \frac{\varepsilon}{2}.
$$

For such $k$ and any $u$ with $\|u\|\le1$, the triangle inequality gives

$$
-\nabla f(x_{k+1})+\varepsilon u\in\partial\phi(0).
$$

This is the translated subgradient ball estimate. It is used to prove the strengthened dry-friction inequality

$$
\varepsilon\|v_{k+1}\|
\le
\phi(v_{k+1})+\langle \nabla f(x_{k+1}),v_{k+1}\rangle.
$$

If $v_{k+1}=0$, this is trivial; otherwise one takes $u=v_{k+1}/\|v_{k+1}\|$ and applies the subgradient inequality at $v_{k+1}$.

Combining this stronger inequality with the earlier energy inequality, the lower bound on the Hessian term, and the smallness of $e_k$, the proof obtains the contraction

$$
\bigl(1+\beta hL+2h(\gamma-\beta L)\bigr)\|d_{k+1}\|^2
\le
(1+\beta hL)\|d_k\|^2.
$$

The rate lemma `ipahdd_rate_mem_Ioo` gives, under the hypotheses $h>0$, $\gamma>0$, $\beta>0$, $L\ge0$, and $\gamma\ge L(h/2+\beta)$, that

$$
q=\frac1{\sqrt{1+2h(\gamma-\beta L)/(1+\beta hL)}}
$$

satisfies $0<q<1$. The square identity

$$
q^2\bigl(1+\beta hL+2h(\gamma-\beta L)\bigr)=1+\beta hL
$$

follows from `ipahddPert_q_sq_mul_A_eq_B_local`. Dividing the contraction by the positive coefficient and taking square roots gives

$$
\|d_{k+1}\|\le q\|d_k\|
$$

for all large $k$. By induction,

$$
\|d_{k_0+n}\|\le q^n\|d_{k_0}\|.
$$

Then writing $x_{k_0+n+p}-x_{k_0+n}$ as a sum of increments and using the triangle inequality,

$$
\|x_{k_0+n}-x_{k_0+n+p}\|
\le
\sum_{i=0}^{p-1}\|d_{k_0+n+i}\|
\le
\frac{q^n}{1-q}\|d_{k_0}\|.
$$

The geometric sum estimate is exactly `geometric_range_sum_le_pert_local`. Letting $p\to\infty$ and using $x_{k_0+n+p}\to x_\infty$ gives

$$
\|x_{k_0+n}-x_\infty\|
\le
\frac{q^n}{1-q}\|d_{k_0}\|.
$$

This produces the two stated eventual bounds, completing the interior case.

Throughout, the Lean tactics have the following mathematical roles: `intro` introduces a hypothesis or a variable into the goal; `rcases` splits conjunctions and existential hypotheses; `rw` rewrites with an equality; `simp` and `simpa` reduce definitions and normalize expressions; `field_simp` clears nonzero denominators; `ring` proves algebraic identities; `positivity` proves nonnegativity of norms and squares; `linarith` and `nlinarith` combine linear and nonlinear arithmetic inequalities; `convert` changes a goal into an equivalent formulation; `refine` builds the final existential-and-conjunction statement; `exact` closes goals by applying the appropriate previously established lemma.

