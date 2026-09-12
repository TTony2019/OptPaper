## Source file
`Beck_Teboulle_FISTA_2009/items/lem_3.lean`

## Lean statement
```lean
theorem key_inequality' {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf L : ℝ}
    (hP : ProblemP f g Lf) (hLpos : 0 < L)
    (y x z : EuclideanSpace ℝ (Fin n))
    (hz : IsProxPoint f g L y z)
    (hcond : compositeObjective f g z ≤ quadraticApprox f g L z y) :
    compositeObjective f g x - compositeObjective f g z ≥
      (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫
```

## Statement explanation
The theorem `key_inequality'` is stated for a natural number $n$, two functions

$$
f,g:\mathbb R^n\to\mathbb R,
$$

where Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and for real parameters $L_f$ and $L$. The hypothesis `hP : ProblemP f g Lf` is a bundled problem assumption. Its full definition is not present in the supplied source, but the proof uses it to obtain: convexity of $g$ through `hP.convex_g`, convexity of $f$ through `hP.convex_f`, and smoothness of $f$ through `hP.smooth_f`. The parameter $L_f$ itself is not used in the displayed conclusion. The hypothesis `hLpos : 0 < L` says that the step parameter $L$ is positive. The points $y,x,z$ all lie in $\mathbb R^n$.

The predicate `hz : IsProxPoint f g L y z` says that $z$ is a proximal point for the composite objective at $y$ with parameter $L$. The proof uses the cited characterization `proxMap_optimality_condition`: when $L>0$ and $g$ is convex, $z$ is a proximal point if and only if there exists $\gamma\in\partial g(z)$ such that

$$
\nabla f(y)+L(z-y)+\gamma=0.
$$

Here $\partial g(z)$ is the subdifferential of $g$ at $z$, defined in the supplied source by

$$
\gamma\in\partial g(z)
\quad\Longleftrightarrow\quad
\forall v,\; g(z)+\langle \gamma,v-z\rangle\le g(v).
$$

The definitions used in the statement are

$$
F(x):=\mathrm{compositeObjective} f g x=f(x)+g(x)
$$

and

$$
Q_L(x,y):=\mathrm{quadraticApprox} f g L x y
=f(y)+\langle\nabla f(y),x-y\rangle+\frac L2\|x-y\|^2+g(x).
$$

The hypothesis

$$
\texttt{hcond}:\quad F(z)\le Q_L(z,y)
$$

therefore says explicitly

$$
f(z)+g(z)\le f(y)+\langle\nabla f(y),z-y\rangle+\frac L2\|z-y\|^2+g(z),
$$

or equivalently

$$
f(z)\le f(y)+\langle\nabla f(y),z-y\rangle+\frac L2\|z-y\|^2.
$$

This is a bound on $F(z)$ by the quadratic approximation at $z$.

The conclusion is

$$
F(x)-F(z)\ge \frac L2\|z-y\|^2+L\langle y-x,z-y\rangle,
$$

or equivalently

$$
F(x)\ge F(z)+\frac L2\|z-y\|^2+L\langle y-x,z-y\rangle.
$$

Thus the theorem gives a lower bound for the composite objective at an arbitrary point $x$, relative to its value at the proximal point $z$, with a quadratic term in $z-y$ and a linear correction involving $x,y,z$.

## Lean proof
```lean
by
  -- Lemma 2.2: optimality condition → existence of subgradient γ
  have h_gamma : ∃ (γ : EuclideanSpace ℝ (Fin n)), γ ∈ subdifferential g z ∧
      gradient f y + L • (z - y) + γ = 0 :=
    ((proxMap_optimality_condition (f := f) (g := g) hLpos hP.convex_g y z).mp hz)
  rcases h_gamma with ⟨γ, hγ_subdiff, hγ_eq⟩
  -- Gradient inequality for convex C^1 f: f a ≥ f b + ⟨∇f b, a-b⟩
  have h_convex_f (a b : EuclideanSpace ℝ (Fin n)) :
      f a ≥ f b + ⟪gradient f b, a - b⟫ := by
    let h_ab := fun (t : ℝ) => f (b + t • (a - b))
    have h_conv_ab : ConvexOn ℝ (Set.univ : Set ℝ) h_ab := by
      refine ⟨convex_univ, λ p hp q hq c d hc hd hcd => ?_⟩
      dsimp [h_ab]
      have hkey : b + ((c * p + d * q) • (a - b)) =
          c • (b + p • (a - b)) + d • (b + q • (a - b)) := by
        calc
          b + ((c * p + d * q) • (a - b))
              = (c + d) • b + ((c * p + d * q) • (a - b)) := by simp [hcd]
          _ = (c • b + d • b) + ((c * p) • (a - b) + (d * q) • (a - b)) := by simp [add_smul]
          _ = c • b + d • b + (c * p) • (a - b) + (d * q) • (a - b) := by abel
          _ = c • b + (c * p) • (a - b) + (d • b + (d * q) • (a - b)) := by abel
          _ = c • (b + p • (a - b)) + d • (b + q • (a - b)) := by simp [smul_add, mul_smul]
      rw [hkey]
      have hpu : (b + p • (a - b)) ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := Set.mem_univ _
      have hpv : (b + q • (a - b)) ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := Set.mem_univ _
      have hineq := hP.convex_f.2 hpu hpv hc hd hcd
      simpa [smul_eq_mul] using hineq
    have h_diff_ab : Differentiable ℝ f :=
      hP.smooth_f.contDiff.differentiable (by decide)
    have h_diffAt_b : DifferentiableAt ℝ f b := h_diff_ab.differentiableAt
    have h_line : HasLineDerivAt ℝ f (lineDeriv ℝ f b (a - b)) b (a - b) :=
      h_diffAt_b.lineDifferentiableAt.hasLineDerivAt
    have h_line_deriv : lineDeriv ℝ f b (a - b) = ⟪gradient f b, a - b⟫ := by
      rw [h_diffAt_b.lineDeriv_eq_fderiv, inner_gradient_left h_diffAt_b]
    have h_deriv : HasDerivAt h_ab (⟪gradient f b, a - b⟫) 0 := by
      have h_line' : HasLineDerivAt ℝ f (⟪gradient f b, a - b⟫) b (a - b) := by
        simpa [h_line_deriv] using h_line
      dsimp [HasLineDerivAt] at h_line' ⊢
      exact h_line'
    have h_slope : ⟪gradient f b, a - b⟫ ≤ h_ab 1 - h_ab 0 := by
      have := ConvexOn.le_slope_of_hasDerivAt h_conv_ab (Set.mem_univ 0) (Set.mem_univ 1)
        (by norm_num : (0 : ℝ) < 1) h_deriv
      simpa [slope, div_one] using this
    have h0 : h_ab 0 = f b := by simp [h_ab]
    have h1 : h_ab 1 = f a := by simp [h_ab]
    rw [h0, h1] at h_slope
    linarith
  -- Subgradient inequality for g
  have h_subgrad_g (a : EuclideanSpace ℝ (Fin n)) : g a ≥ g z + ⟪γ, a - z⟫ :=
    hγ_subdiff a
  -- Expand definitions
  dsimp [compositeObjective, quadraticApprox] at hcond ⊢
  -- Combine f and g lower bounds
  have h_lower (a : EuclideanSpace ℝ (Fin n)) :
      f a + g a ≥ f y + ⟪gradient f y, a - y⟫ + g z + ⟪γ, a - z⟫ := by
    have hf := h_convex_f a y
    have hg := h_subgrad_g a
    linarith
  have h_Fx_lower := h_lower x
  -- Express γ from the optimality condition
  have hγ_expr : γ = -gradient f y - L • (z - y) := by
    calc
      γ = -(gradient f y + L • (z - y)) :=
        eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hγ_eq)
      _ = -gradient f y - L • (z - y) := by abel
  rw [hγ_expr] at h_Fx_lower
  -- Key algebraic identity: set a := z-y, b := x-z.
  set a := z - y with ha
  set b := x - z with hb
  have hyx_eq : y - x = -a - b := by dsimp [a, b]; abel
  have hx_minus_y : x - y = a + b := by dsimp [a, b]; abel
  -- Compute the main algebraic expression
  have h_algebra : (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) -
      (f y + ⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) =
      (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by
    rw [hx_minus_y, ← ha, hyx_eq]
    simp [sub_eq_add_neg, inner_add_right, inner_add_left, inner_neg_left, inner_smul_left,
      real_inner_self_eq_norm_sq a, real_inner_comm b a]
    ring
  -- Assemble the final inequality
  have h_Fx_lower' : f x + g x ≥ f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫ := by
    simpa [ha, hb] using h_Fx_lower
  calc
    f x + g x - (f z + g z)
        ≥ (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) - (f z + g z) := by linarith
    _ ≥ (f y + ⟪gradient f y, x - y⟫ + g z + ⟪-gradient f y - L • a, b⟫) -
        (f y + ⟪gradient f y, z - y⟫ + (L / 2) * ‖z - y‖ ^ 2 + g z) := by linarith
    _ = (L / 2) * ‖z - y‖ ^ 2 + L * ⟪y - x, z - y⟫ := by rw [h_algebra]
```

## Proof explanation
The proof begins by extracting the subgradient information from the proximal-point assumption. The theorem `proxMap_optimality_condition` is applied with $L>0$, with the convexity of $g$ supplied by `hP.convex_g`, and with the points $y,z$. Since `hz` is exactly the statement that $z$ is a proximal point, the forward direction `.mp` gives the existence of some vector $\gamma$ such that

$$
\gamma\in\partial g(z)
$$

and

$$
\nabla f(y)+L(z-y)+\gamma=0.
$$

The tactic `rcases` destructs this existential statement and names the witnesses `γ`, `hγ_subdiff`, and `hγ_eq`.

Next, the proof establishes the standard gradient inequality for the convex smooth function $f$: for every $a,b$,

$$
f(a)\ge f(b)+\langle\nabla f(b),a-b\rangle.
$$

For fixed $a,b$, it introduces the one-dimensional function

$$
h_{ab}(t)=f(b+t(a-b)).
$$

The first task is to show that $h_{ab}$ is convex on $\mathbb R$. For $p,q\in\mathbb R$ and $c,d\ge 0$ with $c+d=1$, the proof checks the convex-combination identity

$$
b+((cp+dq)(a-b))
=c\bigl(b+p(a-b)\bigr)+d\bigl(b+q(a-b)\bigr).
$$

This uses $c+d=1$ and the algebraic normalization tactics `simp`, `add_smul`, `abel`, and `mul_smul`. Then it applies the convexity inequality of $f$ from `hP.convex_f.2` to the two points $b+p(a-b)$ and $b+q(a-b)$. Since both lie in the whole space, this yields

$$
h_{ab}(cp+dq)\le c h_{ab}(p)+d h_{ab}(q).
$$

Hence $h_{ab}$ is convex.

The proof then identifies the derivative of $h_{ab}$ at $0$. From the smoothness field `hP.smooth_f.contDiff.differentiable`, the function $f$ is differentiable, hence differentiable at $b$. The line derivative of $f$ at $b$ in direction $a-b$ is therefore defined, and the lemmas `lineDeriv_eq_fderiv` and `inner_gradient_left` identify it as

$$
\mathrm{lineDeriv}_{\mathbb R} f(b;a-b)=\langle\nabla f(b),a-b\rangle.
$$

Consequently,

$$
h_{ab}'(0)=\langle\nabla f(b),a-b\rangle.
$$

The proof records this as `HasDerivAt h_ab (⟪gradient f b, a - b⟫) 0`.

Now the convexity of $h_{ab}$ and the derivative at $0$ are fed into `ConvexOn.le_slope_of_hasDerivAt`, applied to the points $0$ and $1$ with $0<1$. In this proof, that theorem is used only to provide the slope inequality

$$
h_{ab}'(0)\le h_{ab}(1)-h_{ab}(0).
$$

Substituting the derivative and the endpoint values

$$
h_{ab}(0)=f(b),\qquad h_{ab}(1)=f(a),
$$

gives

$$
\langle\nabla f(b),a-b\rangle\le f(a)-f(b),
$$

which is equivalent to

$$
f(a)\ge f(b)+\langle\nabla f(b),a-b\rangle.
$$

The tactic `linarith` finishes this scalar linear rearrangement.

The proof then uses the subgradient inequality for $g$. Since $\gamma\in\partial g(z)$, the definition of the subdifferential says that for every $v$,

$$
g(z)+\langle\gamma,v-z\rangle\le g(v).
$$

Applying this with $v=a$ gives

$$
g(a)\ge g(z)+\langle\gamma,a-z\rangle.
$$

Combining this with the gradient inequality for $f$, applied with $b=y$, gives for every $a$,

$$
f(a)+g(a)\ge f(y)+\langle\nabla f(y),a-y\rangle+g(z)+\langle\gamma,a-z\rangle.
$$

The proof records this general lower bound as `h_lower`, using `linarith` to add the two inequalities.

Specializing $a=x$ yields

$$
f(x)+g(x)\ge f(y)+\langle\nabla f(y),x-y\rangle+g(z)+\langle\gamma,x-z\rangle.
$$

The proof next solves for $\gamma$. From

$$
\nabla f(y)+L(z-y)+\gamma=0,
$$

it obtains

$$
\gamma=-\bigl(\nabla f(y)+L(z-y)\bigr)
=-\nabla f(y)-L(z-y).
$$

The step uses `eq_neg_of_add_eq_zero_left` to solve the additive equation and `abel` to push the negative sign through the sum. Substituting this expression for $\gamma$ into the lower bound for $x$ gives

$$
f(x)+g(x)\ge f(y)+\langle\nabla f(y),x-y\rangle+g(z)
+\langle-\nabla f(y)-L(z-y),x-z\rangle.
$$

At this point the proof introduces the abbreviations

$$
a=z-y,\qquad b=x-z.
$$

Then

$$
x-y=a+b,\qquad y-x=-a-b.
$$

The key algebraic identity `h_algebra` states that

$$
\begin{aligned}
&\Bigl(f(y)+\langle\nabla f(y),x-y\rangle+g(z)+\langle-\nabla f(y)-La,b\rangle\Bigr)\\
&\qquad
-\Bigl(f(y)+\langle\nabla f(y),z-y\rangle+\frac L2\|z-y\|^2+g(z)\Bigr)\\
&=
\frac L2\|z-y\|^2+L\langle y-x,z-y\rangle.
\end{aligned}
$$

The proof verifies this by rewriting $x-y=a+b$, $z-y=a$, and $y-x=-a-b$, then expanding the inner products using additivity, homogeneity, and symmetry of the real inner product. In particular, it uses

$$
\langle a,a\rangle=\|a\|^2
$$

and

$$
\langle b,a\rangle=\langle a,b\rangle.
$$

After cancellation and rearrangement, the scalar identity is closed by `ring`.

Finally, the proof assembles the desired inequality using a `calc` block. The first line uses the previously established lower bound for $f(x)+g(x)$ and subtracts $f(z)+g(z)$ from both sides:

$$
f(x)+g(x)-(f(z)+g(z))
\ge
\Bigl(f(y)+\langle\nabla f(y),x-y\rangle+g(z)+\langle-\nabla f(y)-La,b\rangle\Bigr)
-(f(z)+g(z)).
$$

This is a linear inequality step discharged by `linarith`.

The second line uses `hcond`. After unfolding `compositeObjective` and `quadraticApprox` with `dsimp`, the hypothesis `hcond` says

$$
f(z)+g(z)\le f(y)+\langle\nabla f(y),z-y\rangle+\frac L2\|z-y\|^2+g(z).
$$

Therefore the right-hand side of the first inequality is at least the right-hand side obtained by replacing $f(z)+g(z)$ with the larger quantity from the quadratic approximation. This gives

$$
\begin{aligned}
&\Bigl(f(y)+\langle\nabla f(y),x-y\rangle+g(z)+\langle-\nabla f(y)-La,b\rangle\Bigr)
-(f(z)+g(z))\\
&\ge
\Bigl(f(y)+\langle\nabla f(y),x-y\rangle+g(z)+\langle-\nabla f(y)-La,b\rangle\Bigr)\\
&\qquad
-\Bigl(f(y)+\langle\nabla f(y),z-y\rangle+\frac L2\|z-y\|^2+g(z)\Bigr).
\end{aligned}
$$

Again `linarith` carries out this linear comparison.

The third line invokes the algebraic identity `h_algebra` to identify the last expression with

$$
\frac L2\|z-y\|^2+L\langle y-x,z-y\rangle.
$$

Combining the three steps through the transitivity of the inequalities gives exactly

$$
f(x)+g(x)-(f(z)+g(z))
\ge
\frac L2\|z-y\|^2+L\langle y-x,z-y\rangle,
$$

which is the stated conclusion for the composite objective.

