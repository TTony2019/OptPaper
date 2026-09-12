## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_thm_1.lean`

## Lean statement
```lean
theorem descent_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) (h : IsC11 f L) (x y : E) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2
```

## Statement explanation
The declaration `descent_lemma` is a theorem about a complete real inner product space \(E\). The assumptions say that \(E\) is a normed additive commutative group, is an inner product space over \(\mathbb R\), and is complete; together these make \(E\) a real Hilbert space. The theorem takes a function \(f:E\to\mathbb R\), a real constant \(L\), a hypothesis \(h:\operatorname{IsC11} f L\), and two points \(x,y\in E\). In the proof, the hypothesis \(h\) is used through two concrete consequences: first, at each point \(u\), \(f\) has a gradient \(\nabla f(u)\), so that the gradient is available in a chain rule; second, for all points \(u,v\), the gradient is \(L\)-Lipschitz in the sense
\[
\|\nabla f(u)-\nabla f(v)\|\le L\|u-v\|.
\]
Thus `IsC11 f L` supplies the \(C^1\)-with-\(L\)-Lipschitz-gradient regularity needed for the descent lemma. The conclusion is the quadratic upper bound
\[
f(y)\le f(x)+\langle \nabla f(x),y-x\rangle+\frac L2\|y-x\|^2,
\]
where \(\langle\cdot,\cdot\rangle\) is the real inner product and \(\nabla f(x)\) is the gradient of \(f\) at \(x\). Mathematically, this says that if the gradient of \(f\) is \(L\)-Lipschitz, then \(f(y)\) is bounded above by its first-order Taylor approximation at \(x\) plus the quadratic term \(\frac L2\|y-x\|^2\). No sign condition on \(L\) is separately listed in the statement; the Lipschitz estimate used in the proof is exactly the one supplied by \(h\).

## Lean proof
```lean
by
  let φ : ℝ → E := fun t => AffineMap.lineMap x y t
  let r : ℝ → ℝ := fun t =>
    f (φ t) - f x - t * inner ℝ (gradient f x) (y - x) -
      (L / 2) * t ^ 2 * ‖y - x‖ ^ 2
  have hr0 : r 0 = 0 := by
    simp [r, φ]
  have hline_f (t₀ : ℝ) :
      HasDerivAt (fun t : ℝ => f (φ t))
        (inner ℝ (gradient f (φ t₀)) (y - x)) t₀ := by
    have hline : HasDerivAt φ (y - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t₀))
    have hcomp := (h.hasGradientAt (φ t₀)).hasFDerivAt.comp_hasDerivAt t₀ hline
    simpa using hcomp
  have hr_deriv (t : ℝ) :
      HasDerivAt r
        (inner ℝ (gradient f (φ t) - gradient f x) (y - x) - L * t * ‖y - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => f (φ s))
        (inner ℝ (gradient f (φ t)) (y - x)) t := hline_f t
    have h2 : HasDerivAt (fun _ : ℝ => f x) 0 t := hasDerivAt_const t (f x)
    have h3 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient f x) (y - x))
        (inner ℝ (gradient f x) (y - x)) t := by
      simpa using
        (hasDerivAt_id t |>.mul_const (inner ℝ (gradient f x) (y - x)))
    have h4 : HasDerivAt (fun s : ℝ => (L / 2) * s ^ 2 * ‖y - x‖ ^ 2)
        (L * t * ‖y - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖y - x‖ ^ 2) using 1
      ring
    have hderiv := ((h1.sub h2).sub h3).sub h4
    simpa [r, sub_sub, inner_sub_left] using hderiv
  have hr_diff (t : ℝ) : DifferentiableAt ℝ r t :=
    (hr_deriv t).differentiableAt
  have hr_cont : Continuous r :=
    continuous_iff_continuousAt.mpr fun t => (hr_diff t).continuousAt
  have hr_contOn : ContinuousOn r (Set.Icc (0 : ℝ) 1) := hr_cont.continuousOn
  have hr_diffOn : DifferentiableOn ℝ r (Set.Ioo (0 : ℝ) 1) :=
    fun t _ => (hr_diff t).differentiableWithinAt
  have hr_deriv_nonpos {t : ℝ} (ht : 0 < t) :
      inner ℝ (gradient f (φ t) - gradient f x) (y - x) - L * t * ‖y - x‖ ^ 2 ≤ 0 := by
    have h_cauchy :
        inner ℝ (gradient f (φ t) - gradient f x) (y - x) ≤
          ‖gradient f (φ t) - gradient f x‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient f (φ t) - gradient f x‖ ≤ L * ‖φ t - x‖ :=
      h.lipschitz (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖y - x‖ := by
      have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y :=
        dist_left_lineMap x y t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner ℝ (gradient f (φ t) - gradient f x) (y - x) ≤ L * t * ‖y - x‖ ^ 2 := by
      calc
        inner ℝ (gradient f (φ t) - gradient f x) (y - x)
            ≤ ‖gradient f (φ t) - gradient f x‖ * ‖y - x‖ := h_cauchy
        _ ≤ (L * ‖φ t - x‖) * ‖y - x‖ := by
          nlinarith [h_lip, norm_nonneg (y - x)]
        _ = L * t * ‖y - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      deriv r c = (r 1 - r 0) / (1 - 0) :=
    exists_deriv_eq_slope r (by norm_num : (0 : ℝ) < 1) hr_contOn hr_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c : deriv r c =
      inner ℝ (gradient f (φ c) - gradient f x) (y - x) - L * c * ‖y - x‖ ^ 2 :=
    (hr_deriv c).deriv
  have h_deriv_c_nonpos : deriv r c ≤ 0 := by
    rw [h_deriv_c]
    exact hr_deriv_nonpos hc.1
  rw [show (1 : ℝ) - 0 = 1 by norm_num, div_one, hr0, sub_zero] at hc_eq
  have hr1_nonpos : r 1 ≤ 0 := by linarith
  simp [r, φ] at hr1_nonpos
  linarith
```

## Proof explanation
The proof begins by defining the affine line segment
\[
\phi(t)=\operatorname{lineMap}(x,y,t),
\]
so that \(\phi(0)=x\), \(\phi(1)=y\), and \(\phi'(t)=y-x\). It then defines the auxiliary function
\[
r(t)=f(\phi(t))-f(x)-t\langle \nabla f(x),y-x\rangle-\frac L2 t^2\|y-x\|^2.
\]
This \(r\) measures the difference between \(f\) along the segment and its quadratic model based at \(x\). The first step `have hr0 : r 0 = 0` uses `simp` with the definitions of \(r\) and \(\phi\): at \(t=0\), \(\phi(0)=x\), and the terms involving \(t\) and \(t^2\) vanish.

Next, `hline_f` proves that for every \(t_0\in\mathbb R\),
\[
t\mapsto f(\phi(t))
\]
has derivative
\[
\langle \nabla f(\phi(t_0)),y-x\rangle
\]
at \(t_0\). The proof first uses `AffineMap.hasDerivAt_lineMap` to get \(\phi'(t_0)=y-x\). Then `h.hasGradientAt (φ t₀)` gives that \(f\) has gradient \(\nabla f(\phi(t_0))\) at \(\phi(t_0)\), hence a Fréchet derivative there. The chain rule `HasFDerivAt.comp_hasDerivAt` composes this Fréchet derivative with the derivative of the curve \(\phi\) at \(t_0\). Since the gradient represents the derivative as \(v\mapsto \langle \nabla f(\phi(t_0)),v\rangle\), the resulting scalar derivative is \(\langle \nabla f(\phi(t_0)),y-x\rangle\).

The step `hr_deriv` computes the derivative of \(r\). It combines four derivative facts. First, \(h_1\) is the just-proved derivative of \(f(\phi(t))\). Second, \(h_2\) says the constant \(f(x)\) has derivative \(0\). Third, \(h_3\) computes the derivative of
\[
t\mapsto t\langle \nabla f(x),y-x\rangle
\]
as \(\langle \nabla f(x),y-x\rangle\), using `hasDerivAt_id` and `mul_const`. Fourth, \(h_4\) computes the derivative of
\[
t\mapsto \frac L2 t^2\|y-x\|^2
\]
as \(Lt\|y-x\|^2\), using the derivative of \(t^2\), constant multiplication, and `ring` to simplify the coefficient. Subtracting these derivatives gives
\[
r'(t)=\langle \nabla f(\phi(t))-\nabla f(x),y-x\rangle-Lt\|y-x\|^2.
\]
The simplification uses `inner_sub_left`, the linearity of the inner product in its first argument, to combine
\[
\langle \nabla f(\phi(t)),y-x\rangle-\langle \nabla f(x),y-x\rangle
\]
into
\[
\langle \nabla f(\phi(t))-\nabla f(x),y-x\rangle.
\]

The derivative formula implies \(r\) is differentiable at every \(t\). The proof records this in `hr_diff`, then obtains continuity of \(r\) from differentiability in `hr_cont`, continuity on \([0,1]\) in `hr_contOn`, and differentiability on \((0,1)\) in `hr_diffOn`. These are exactly the regularity hypotheses needed for the mean value theorem on the interval \([0,1]\).

The key estimate is `hr_deriv_nonpos`. For \(t>0\), it proves
\[
\langle \nabla f(\phi(t))-\nabla f(x),y-x\rangle-Lt\|y-x\|^2\le 0.
\]
The proof uses Cauchy–Schwarz in the form `real_inner_le_norm`, giving
\[
\langle \nabla f(\phi(t))-\nabla f(x),y-x\rangle
\le
\|\nabla f(\phi(t))-\nabla f(x)\|\,\|y-x\|.
\]
It then uses the Lipschitz estimate `h.lipschitz (φ t) x`, which gives
\[
\|\nabla f(\phi(t))-\nabla f(x)\|\le L\|\phi(t)-x\|.
\]
Finally, because \(\phi(t)\) lies on the segment from \(x\) to \(y\), the distance from \(x\) to \(\phi(t)\) is \(t\|y-x\|\) when \(t>0\). This is obtained from `dist_left_lineMap`, the fact \(\|t\|=t\) for \(t>0\) via `abs_of_pos`, and norm-distance conversions. Combining these inequalities yields
\[
\langle \nabla f(\phi(t))-\nabla f(x),y-x\rangle
\le Lt\|y-x\|^2.
\]
Subtracting the same quantity \(Lt\|y-x\|^2\) from both sides gives the desired nonpositivity. The tactics `nlinarith`, `ring`, and `linarith` are used to multiply the Lipschitz estimate by the nonnegative factor \(\|y-x\|\), simplify algebraic identities, and finish the inequality.

Next, the proof applies the mean value theorem through `exists_deriv_eq_slope`. The hypotheses supplied are \(0<1\), continuity of \(r\) on \([0,1]\), and differentiability of \(r\) on \((0,1)\). The conclusion is that there exists \(c\in(0,1)\) such that
\[
r'(c)=\frac{r(1)-r(0)}{1-0}.
\]
The proof destructs this existence statement with `rcases`, obtaining \(c\), the membership \(c\in(0,1)\), and the equality above. Then `h_deriv_c` identifies \(r'(c)\) with the explicit derivative formula
\[
r'(c)=\langle \nabla f(\phi(c))-\nabla f(x),y-x\rangle-Lc\|y-x\|^2.
\]
Because \(c>0\), the earlier estimate `hr_deriv_nonpos` applies to \(c\), giving \(r'(c)\le 0\).

The proof rewrites the mean value theorem equality: \(1-0=1\), so dividing by \(1\) is harmless, and \(r(0)=0\), so the right-hand side becomes \(r(1)\). Hence \(r'(c)=r(1)\). Since \(r'(c)\le 0\), linear arithmetic gives \(r(1)\le 0\). Finally, `simp [r, φ] at hr1_nonpos` evaluates \(r(1)\) and \(\phi(1)=y\), producing
\[
f(y)-f(x)-\langle \nabla f(x),y-x\rangle-\frac L2\|y-x\|^2\le 0.
\]
The final `linarith` rearranges this inequality into
\[
f(y)\le f(x)+\langle \nabla f(x),y-x\rangle+\frac L2\|y-x\|^2,
\]
which is exactly the claimed descent lemma.

