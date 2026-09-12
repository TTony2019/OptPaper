## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_2.lean`

## Lean statement
```lean
theorem theorem_3_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (z : ℝ → H)
    (hf : ContDiff ℝ 2 f)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hsol : IsDrygradTrajectory r f z t₀)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hz_contdiff : ContDiff ℝ 2 z)
    (hinitial : r < ‖gradient f (z t₀)‖) :
    AntitoneOn (fun t => ‖deriv z t‖) (Set.Ici t₀) ∧
      Filter.Tendsto (fun t : ℝ => t * ‖deriv z t‖) Filter.atTop (nhds 0)
```

## Statement explanation
The declaration `theorem_3_1` states the following. Let $H$ be a complete real inner product space. Let $t_0,r\in\mathbb R$ with $r>0$. Let $f:H\to\mathbb R$ be a function that is $C^2$, convex on all of $H$, bounded below, and whose gradient $\nabla f$ is locally Lipschitz. Let $z:\mathbb R\to H$ be a $C^2$ curve which is a dry-gradient trajectory with friction coefficient $r$ starting at time $t_0$. Assume the initial condition $r<\|\nabla f(z(t_0))\|$. The conclusion is two-fold: the speed function

$$
t\mapsto \|z'(t)\|
$$

is nonincreasing on $[t_0,\infty)$, and the product $t\|z'(t)\|$ tends to $0$ as $t\to+\infty$. Here $\nabla f$ is the Riesz gradient of $f$, $z'(t)$ is the derivative of $z$ at $t$, and the dry-gradient trajectory hypothesis is used in the proof in the following form: for every $t\ge t_0$, there exists a vector $u$ in the subdifferential of the dry friction potential $x\mapsto r\|x\|$ at $z'(t)$ such that the balance equation $z'(t)+u+\nabla f(z(t))=0$ holds.

## Lean proof
```lean
by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfderiv_contdiff : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f by simpa using hf)).2.2
  have hgradient_contdiff : ContDiff ℝ 1 (gradient f) := by
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfderiv_contdiff
  have hgradient_diff : Differentiable ℝ (gradient f) :=
    hgradient_contdiff.differentiable (by norm_num)
  have hz_diff : Differentiable ℝ z := hz_contdiff.differentiable (by norm_num)
  have hz_second_deriv : ∀ t : ℝ,
      HasDerivAt (deriv z) (deriv (deriv z) t) t := by
    intro t
    exact (hz_contdiff.differentiable_deriv_two t).hasDerivAt
  have hgrad_deriv : ∀ t : ℝ, HasDerivAt (fun s => gradient f (z s))
      (fderiv ℝ (gradient f) (z t) (deriv z t)) t := by
    intro t
    simpa [Function.comp_def] using
      (hgradient_diff (z t)).hasFDerivAt.comp_hasDerivAt t (hz_diff t).hasDerivAt
  have hHessian_nonneg : ∀ t : ℝ,
      0 ≤ inner ℝ (fderiv ℝ (gradient f) (z t) (deriv z t)) (deriv z t) := by
    intro t
    have hmono := gradient_derivative_inner_nonnegative f hconvex hf_diff z
      (hz_diff t).hasDerivAt (hgrad_deriv t)
    simpa [real_inner_comm] using hmono
  have hL1 : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ici t₀) := by
    rcases theorem_2_1 hr f z (hf.of_le (by norm_num)) hf_lower hgradient_lip hz_diff hinitial
      hsol with
      ⟨_, _, hL1, _⟩
    exact hL1
  have hradial : ∀ t ∈ Set.Ici t₀, deriv z t ≠ 0 →
      deriv z t + (r / ‖deriv z t‖) • deriv z t + gradient f (z t) = 0 := by
    intro t ht hv
    rcases hsol t ht with ⟨u, hu, hsum⟩
    have hu' : ∀ y : H,
        (dryFrictionPotential (H := H) r (deriv z t) : EReal) +
            (inner ℝ u (y - deriv z t) : EReal) ≤
          (dryFrictionPotential (H := H) r y : EReal) := by
      intro y
      have hy := (ERealFunction.mem_subdifferential_iff
        (dryFrictionPotential (H := H) r) (deriv z t) u).mp hu y
      simpa [real_inner_comm, add_comm] using hy
    rw [drygrad_subgradient_eq_radial hr hv hu'] at hsum
    exact hsum
  have hacc : ∀ t ∈ interior (Set.Ici t₀),
      inner ℝ (deriv (deriv z) t) (deriv z t) ≤ 0 := by
    intro t ht
    have ht₀ : t ∈ Set.Ici t₀ := interior_subset ht
    by_cases hv : deriv z t = 0
    · simp [hv]
    · have hvnorm : ‖deriv z t‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hn : HasDerivAt (fun s => ‖deriv z s‖)
          (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖) t := by
        have hs := (hz_second_deriv t).norm_sq.sqrt (pow_ne_zero 2 hvnorm)
        convert hs using 1
        all_goals simp [real_inner_comm, norm_nonneg]
        all_goals field_simp
      have hc : HasDerivAt (fun s : ℝ => r / ‖deriv z s‖)
          (-(r * (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖)) /
            ‖deriv z t‖ ^ 2) t := by
        convert (hasDerivAt_const t r).div hn hvnorm using 1
        all_goals ring
      have hd : HasDerivAt (fun s =>
          deriv z s + (r / ‖deriv z s‖) • deriv z s + gradient f (z s))
          (deriv (deriv z) t + ((r / ‖deriv z t‖) • deriv (deriv z) t +
            (-(r * (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖)) /
              ‖deriv z t‖ ^ 2) • deriv z t) +
            fderiv ℝ (gradient f) (z t) (deriv z t)) t :=
        ((hz_second_deriv t).add (hc.smul (hz_second_deriv t))).add (hgrad_deriv t)
      have hneigh : ∀ᶠ s in nhds t, deriv z s ≠ 0 :=
        (hz_second_deriv t).continuousAt.eventually_ne hv
      have hEq : (fun _ : ℝ => (0 : H)) =ᶠ[nhds t]
          fun s => deriv z s + (r / ‖deriv z s‖) • deriv z s + gradient f (z s) := by
        filter_upwards [mem_interior_iff_mem_nhds.mp ht, hneigh] with s hs hsnz
        exact (hradial s hs hsnz).symm
      have hDzero : deriv (deriv z) t + ((r / ‖deriv z t‖) • deriv (deriv z) t +
          (-(r * (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖)) /
            ‖deriv z t‖ ^ 2) • deriv z t) +
          fderiv ℝ (gradient f) (z t) (deriv z t) = 0 := by
        exact (hd.congr_of_eventuallyEq hEq).unique (hasDerivAt_const t 0)
      have hinner := congrArg (fun w => inner ℝ w (deriv z t)) hDzero
      simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        inner_zero_left] at hinner
      simp at hinner
      field_simp [hvnorm] at hinner
      nlinarith [hHessian_nonneg t, norm_pos_iff.mpr hv]
  have hsq_anti : AntitoneOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
      (fun t _ => ((hz_second_deriv t).continuousAt.norm).continuousWithinAt.pow 2)
    · intro t ht
      exact (hz_second_deriv t).norm_sq.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hz_second_deriv t).norm_sq.deriv]
      rw [real_inner_comm]
      nlinarith [hacc t ht]
  have hspeed : AntitoneOn (fun t => ‖deriv z t‖) (Set.Ici t₀) := by
    intro s hs t ht hst
    nlinarith [hsq_anti hs ht hst, norm_nonneg (deriv z s), norm_nonneg (deriv z t)]
  exact ⟨hspeed, lemma_3_1 (fun t => ‖deriv z t‖) (fun _ _ => norm_nonneg _) hspeed hL1⟩
```

## Proof explanation
The proof first records several smoothness consequences of the hypotheses. From $f$ being $C^2$, the command `hf.differentiable` gives that $f$ is differentiable. The characterization `contDiff_succ_iff_fderiv` applied to $2=1+1$ gives that the Fréchet derivative $Df$ is $C^1$. Since the gradient $\nabla f$ is obtained from $Df$ by the Riesz representation map, which is a continuous linear equivalence, `hgradient_contdiff` shows that $\nabla f$ is $C^1$; hence `hgradient_diff` gives that $\nabla f$ is differentiable. Similarly, from $z$ being $C^2$, `hz_diff` gives that $z$ is differentiable. The lemma `differentiable_deriv_two` gives `hz_second_deriv`: for every $t$, the derivative curve $z'$ has derivative $z''(t)$ at $t$. The chain rule `comp_hasDerivAt` then gives `hgrad_deriv`: the curve $s\mapsto \nabla f(z(s))$ has derivative

$$
D\nabla f(z(t))\bigl(z'(t)\bigr)
$$

at $t$. Applying `gradient_derivative_inner_nonnegative` to the convex differentiable function $f$ and the curve $z$ yields

$$
0\le \bigl\langle z'(t),D\nabla f(z(t))\bigl(z'(t)\bigr)\bigr\rangle .
$$

Using symmetry of the real inner product, this becomes `hHessian_nonneg`:

$$
0\le \bigl\langle D\nabla f(z(t))\bigl(z'(t)\bigr),z'(t)\bigr\rangle .
$$

This is the monotonicity of the gradient of a convex function, expressed as the nonnegativity of the Hessian quadratic form along the velocity.

Next the proof invokes `theorem_2_1`. Its statement gives, among other conclusions, that under the hypotheses $r>0$, $f$ is $C^1$, lower bounded, with locally Lipschitz gradient, and $z$ is a differentiable dry-gradient trajectory starting at $t_0$ with $r<\|\nabla f(z(t_0))\|$, the functions

$$
t\mapsto \|z'(t)\|^2
\qquad\text{and}\qquad
t\mapsto \|z'(t)\|
$$

are integrable on $[t_0,\infty)$. The proof only needs the third conclusion, extracted by `rcases` as `hL1`:

$$
\int_{t_0}^{\infty}\|z'(t)\|\,dt<\infty.
$$

The command `hf.of_le` lowers the $C^2$ assumption on $f$ to the $C^1$ assumption required by `theorem_2_1`.

The key structural property of the dry-gradient trajectory is then extracted in `hradial`. For $t\ge t_0$, the hypothesis `hsol t ht` supplies a vector $u$ and an equality expressing the dry-gradient balance. The membership $u\in\partial(r\|\cdot\|)(z'(t))$ is converted, using `ERealFunction.mem_subdifferential_iff`, into the subgradient inequality

$$
r\|z'(t)\|+\langle u,y-z'(t)\rangle\le r\|y\|
$$

for every $y\in H$. The lemma `drygrad_subgradient_eq_radial`, applied with $r>0$, $v=z'(t)\neq0$, and this inequality, gives

$$
u=\frac{r}{\|z'(t)\|}\,z'(t).
$$

Substituting this into the balance equation yields `hradial`:

$$
z'(t)+\frac{r}{\|z'(t)\|}\,z'(t)+\nabla f(z(t))=0
$$

for every $t\ge t_0$ with $z'(t)\neq0$.

The proof then establishes the acceleration inequality `hacc`: for every $t>t_0$,

$$
\langle z''(t),z'(t)\rangle\le0.
$$

If $z'(t)=0$, this is immediate because the second factor is zero. Otherwise write $v=z'(t)$, $a=z''(t)$, $c=\|v\|$, and $q=\langle a,v\rangle$. The proof differentiates the radial equation on a neighborhood of $t$ where the speed is nonzero. The lemma `HasDerivAt.norm_sq.sqrt` gives that $s\mapsto\|z'(s)\|$ has derivative $q/c$ at $t$, because the derivative of $\|z'(s)\|^2$ is $2\langle z'(s),z''(s)\rangle$ and the chain rule for the square root contributes $1/(2\|z'(t)\|)$. The quotient rule then gives the derivative of $s\mapsto r/\|z'(s)\|$ as

$$
-\frac{r(q/c)}{c^2}.
$$

Using `hz_second_deriv` for the derivative of $z'$, the scalar multiplication rule, and `hgrad_deriv` for the derivative of $\nabla f(z(s))$, the proof obtains the derivative of the whole left-hand side

$$
E(s)=z'(s)+\frac{r}{\|z'(s)\|}\,z'(s)+\nabla f(z(s))
$$

at $t$. Because $t$ is in the interior of $[t_0,\infty)$, points near $t$ still lie in $[t_0,\infty)$; by continuity and the assumption $z'(t)\neq0$, they also satisfy $z'(s)\neq0$ near $t$. Hence `hradial` says $E(s)=0$ eventually near $t$. The tactic `filter_upwards` combines the eventual conditions, and `congr_of_eventuallyEq` transfers the derivative computation to the zero function. Uniqueness of the derivative then gives $E'(t)=0$.

Taking the inner product of the equation $E'(t)=0$ with $v=z'(t)$ and simplifying inner products, the terms involving $r$ cancel because $\langle v,v\rangle=\|v\|^2=c^2$. The result is

$$
q+\langle D\nabla f(z(t))(v),v\rangle=0.
$$

By `hHessian_nonneg`, the second term is nonnegative. Therefore $q\le0$, which is exactly $\langle z''(t),z'(t)\rangle\le0$. This is the mathematical content of `hacc`: along the trajectory, the acceleration has nonpositive inner product with the velocity, so the speed cannot increase.

From this acceleration inequality, the proof shows that the squared speed is antitone. The function $s\mapsto\|z'(s)\|^2$ is continuous on $[t_0,\infty)$ and differentiable on its interior, with derivative

$$
2\langle z'(t),z''(t)\rangle.
$$

Using symmetry of the inner product and `hacc`, this derivative is $2\langle z''(t),z'(t)\rangle\le0$ on the interior. The theorem `antitoneOn_of_deriv_nonpos` then gives `hsq_anti`: the function $t\mapsto\|z'(t)\|^2$ is nonincreasing on $[t_0,\infty)$. Passing from squared speed to speed uses only nonnegativity: if $s\le t$, then $\|z'(s)\|^2\ge\|z'(t)\|^2$, and since both norms are nonnegative, $\|z'(s)\|\ge\|z'(t)\|$. The `nlinarith` tactic performs this nonlinear arithmetic, giving `hspeed`, the nonincreasing property of $t\mapsto\|z'(t)\|$.

Finally, the proof applies `lemma_3_1` to the function $h(t)=\|z'(t)\|$. The hypotheses of that lemma are: $h$ is nonnegative on $[t_0,\infty)$, which follows from `norm_nonneg`; $h$ is antitone on $[t_0,\infty)$, which is `hspeed`; and $h$ is integrable on $[t_0,\infty)$, which is `hL1`. The conclusion of `lemma_3_1` is

$$
t\,h(t)\to0
\qquad(t\to+\infty),
$$

so

$$
t\|z'(t)\|\to0
\qquad(t\to+\infty).
$$

The final `exact` packages `hspeed` and this limit into the required conjunction.

