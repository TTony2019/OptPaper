## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_thm_2.lean`

## Lean statement
```lean
theorem descent_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (psi : H → ℝ) (gradPsi : H → H) (L : ℝ) (hdiff : Differentiable ℝ psi)
    (hgrad : ∀ x h, fderiv ℝ psi x h = inner ℝ (gradPsi x) h)
    (hlip : ∀ x y, ‖gradPsi x - gradPsi y‖ ≤ L * ‖x - y‖) (x v : H) :
    psi v ≤ psi x + inner ℝ (gradPsi x) (v - x) + L / 2 * ‖v - x‖ ^ 2
```

## Statement explanation
The theorem `descent_lemma` is a real-inner-product-space form of the standard descent lemma for functions with Lipschitz gradient. Let $H$ be a real inner product space, and let $\psi:H\to\mathbb R$ be a real-valued function on $H$. Let $g:H\to H$ be the map denoted `gradPsi`. The hypotheses say:

- $\psi$ is differentiable over $\mathbb R$ at every point of $H$.
- For every $x\in H$ and every direction $h\in H$,

$$
D\psi(x)h=\langle g(x),h\rangle,
$$

  so $g(x)$ is the gradient vector representing the Fréchet derivative of $\psi$ at $x$.
- The gradient map $g$ is Lipschitz with constant $L$:

```math
\|g(x)-g(y)\|\le L\|x-y\|
```

  for all $x,y\in H$.
- $x$ and $v$ are arbitrary points of $H$.

The conclusion is the quadratic upper bound

```math
\psi(v)\le \psi(x)+\langle g(x),v-x\rangle+\frac{L}{2}\|v-x\|^2.
```

Thus the value at $v$ is bounded above by the first-order Taylor expansion of $\psi$ at $x$, plus the usual quadratic error term controlled by the Lipschitz constant of the gradient. No separate hypothesis $L\ge 0$ appears in the statement.

## Lean proof
```lean
by
  let φ : ℝ → H := fun t => AffineMap.lineMap x v t
  let r : ℝ → ℝ := fun t =>
    psi (φ t) - psi x - t * inner ℝ (gradPsi x) (v - x) -
      (L / 2) * t ^ 2 * ‖v - x‖ ^ 2
  have hr0 : r 0 = 0 := by
    simp [r, φ]
  have hline_psi (t₀ : ℝ) :
      HasDerivAt (fun t : ℝ => psi (φ t))
        (inner ℝ (gradPsi (φ t₀)) (v - x)) t₀ := by
    have hline : HasDerivAt φ (v - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := v) (x := t₀))
    have hcomp := (hdiff (φ t₀)).hasFDerivAt.comp_hasDerivAt t₀ hline
    rw [hgrad (φ t₀) (v - x)] at hcomp
    exact hcomp
  have hr_deriv (t : ℝ) :
      HasDerivAt r
        (inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) - L * t * ‖v - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => psi (φ s))
        (inner ℝ (gradPsi (φ t)) (v - x)) t := hline_psi t
    have h2 : HasDerivAt (fun _ : ℝ => psi x) 0 t := hasDerivAt_const t (psi x)
    have h3 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradPsi x) (v - x))
        (inner ℝ (gradPsi x) (v - x)) t := by
      simpa using
        (hasDerivAt_id t |>.mul_const (inner ℝ (gradPsi x) (v - x)))
    have h4 : HasDerivAt (fun s : ℝ => (L / 2) * s ^ 2 * ‖v - x‖ ^ 2)
        (L * t * ‖v - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖v - x‖ ^ 2) using 1
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
      inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) - L * t * ‖v - x‖ ^ 2 ≤ 0 := by
    have h_cauchy :
        inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) ≤
          ‖gradPsi (φ t) - gradPsi x‖ * ‖v - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradPsi (φ t) - gradPsi x‖ ≤ L * ‖φ t - x‖ :=
      hlip (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖v - x‖ := by
      have hdist : dist x (AffineMap.lineMap x v t) = ‖t‖ * dist x v :=
        dist_left_lineMap x v t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) ≤ L * t * ‖v - x‖ ^ 2 := by
      calc
        inner ℝ (gradPsi (φ t) - gradPsi x) (v - x)
            ≤ ‖gradPsi (φ t) - gradPsi x‖ * ‖v - x‖ := h_cauchy
        _ ≤ (L * ‖φ t - x‖) * ‖v - x‖ := by
          nlinarith [h_lip, norm_nonneg (v - x)]
        _ = L * t * ‖v - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      deriv r c = (r 1 - r 0) / (1 - 0) :=
    exists_deriv_eq_slope r (by norm_num : (0 : ℝ) < 1) hr_contOn hr_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c : deriv r c =
      inner ℝ (gradPsi (φ c) - gradPsi x) (v - x) - L * c * ‖v - x‖ ^ 2 :=
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
The proof reduces the problem to a one-dimensional estimate along the line segment from $x$ to $v$. It defines

$$
\phi(t)=\mathrm{lineMap}(x,v,t).
$$

In this vector-space setting, $\phi(t)$ is the affine interpolation between $x$ and $v$, namely $(1-t)x+tv$, equivalently $x+t(v-x)$. Hence $\phi(0)=x$, $\phi(1)=v$, and the derivative of $\phi$ is the constant vector $v-x$.

The proof then defines the remainder function

```math
r(t)=\psi(\phi(t))-\psi(x)-t\langle g(x),v-x\rangle-\frac{L}{2}t^2\|v-x\|^2.
```

This is the error between $\psi(\phi(t))$ and its first-order approximation at $t=0$, corrected by the quadratic term. At $t=0$, all terms except $\psi(x)-\psi(x)$ vanish, so `hr0` states

$$
r(0)=0.
$$

Next, the proof computes the derivative of $t\mapsto \psi(\phi(t))$. At a point $t_0$, the affine map $\phi$ has derivative $v-x$. This is the content of `AffineMap.hasDerivAt_lineMap`. Since $\psi$ is differentiable at $\phi(t_0)$, the chain rule `HasFDerivAt.comp_hasDerivAt` gives that the derivative of $\psi\circ\phi$ at $t_0$ is

$$
D\psi(\phi(t_0))(v-x).
$$

Using the hypothesis `hgrad`, this derivative equals

$$
\langle g(\phi(t_0)),v-x\rangle.
$$

This is the lemma `hline_psi`.

The proof then differentiates $r$. It differentiates each term separately:

- $t\mapsto \psi(\phi(t))$ has derivative $\langle g(\phi(t)),v-x\rangle$ by `hline_psi`.
- The constant term $\psi(x)$ has derivative $0$, using `hasDerivAt_const`.
- The term $t\mapsto t\langle g(x),v-x\rangle$ has derivative $\langle g(x),v-x\rangle$, using the fact that the identity function has derivative $1$ and multiplying by a constant multiplies the derivative by that constant.
- The term

```math
t\mapsto \frac{L}{2}t^2\|v-x\|^2
```

  has derivative

```math
L t\|v-x\|^2,
```

  using the derivative of $t^2$, namely $2t$, together with multiplication by the constants $\frac{L}{2}$ and $`\|v-x\|^2`$.

Subtracting these derivatives gives

```math
r'(t)
=\langle g(\phi(t))-g(x),v-x\rangle
-L t\|v-x\|^2.
```

The identity $\langle a-b,c\rangle=\langle a,c\rangle-\langle b,c\rangle$, invoked as `inner_sub_left`, is used to combine the two inner-product terms into this single inner product.

Since $r$ has a derivative at every $t$, `hr_diff` records that $r$ is differentiable at every point. Consequently `hr_cont` gives that $r$ is continuous. Restricting these facts to the interval $[0,1]$, the proof obtains continuity of $r$ on $[0,1]$ and differentiability of $r$ on $(0,1)$.

The key sign estimate is `hr_deriv_nonpos`. For $t\gt 0$, the proof shows

```math
\langle g(\phi(t))-g(x),v-x\rangle
-L t\|v-x\|^2\le 0.
```

Indeed, by Cauchy-Schwarz in the form `real_inner_le_norm`,

```math
\langle g(\phi(t))-g(x),v-x\rangle
\le
\|g(\phi(t))-g(x)\|\,\|v-x\|.
```

By the Lipschitz hypothesis,

```math
\|g(\phi(t))-g(x)\|\le L\|\phi(t)-x\|.
```

Since $\phi(t)=x+t(v-x)$, its distance from $x$ is

```math
\|\phi(t)-x\|=t\|v-x\|
```

for $t\gt 0$. This is obtained from `dist_left_lineMap`, which says that the distance from $x$ to the line-map point is $`\|t\|`$times the distance from$x$to$v$, together with$`\|t\|=t`$because$t>0$. Multiplying the Lipschitz inequality by the nonnegative factor$`\|v-x\|`$ and substituting the distance formula yields

```math
\langle g(\phi(t))-g(x),v-x\rangle
\le
L t\|v-x\|^2.
```

Therefore the derivative formula for $r'(t)$ is nonpositive whenever $t\gt 0$.

The proof now applies the mean value theorem via `exists_deriv_eq_slope`. Since $r$ is continuous on $[0,1]$ and differentiable on $(0,1)$, there exists $c\in(0,1)$ such that

$$
r'(c)=\frac{r(1)-r(0)}{1-0}.
$$

Using the formula already computed for $r'(c)$, and using $c\gt 0$, the proof obtains

$$
r'(c)\le 0.
$$

After simplifying the denominator and using $r(0)=0$, the mean value theorem equation becomes

$$
r(1)=r'(c).
$$

Hence

$$
r(1)\le 0.
$$

Finally, the proof expands $r(1)$. Since $\phi(1)=v$, the definition of $r$ gives

```math
r(1)
=\psi(v)-\psi(x)-\langle g(x),v-x\rangle-\frac{L}{2}\|v-x\|^2.
```

The inequality $r(1)\le 0$ therefore becomes

```math
\psi(v)-\psi(x)-\langle g(x),v-x\rangle-\frac{L}{2}\|v-x\|^2\le 0.
```

Rearranging this inequality, which is exactly what the final `linarith` step does, yields

```math
\psi(v)
\le
\psi(x)+\langle g(x),v-x\rangle+\frac{L}{2}\|v-x\|^2.
```

This is the desired descent lemma.

