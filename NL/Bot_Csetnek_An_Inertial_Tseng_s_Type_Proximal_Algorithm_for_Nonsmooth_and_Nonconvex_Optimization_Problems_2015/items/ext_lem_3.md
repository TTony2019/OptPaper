## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_lem_3.lean`

## Lean statement
```lean
theorem lemma_3_1_descent {m : Nat} (h : EuclideanSpace m -> Real) (L : Real)
    (hL : HasLipschitzContinuousGradient h L) :
    ∀ x y : EuclideanSpace m,
      h y <= h x + inner Real (gradient h x) (y - x) + (L / 2) * ‖y - x‖ ^ 2
```

## Statement explanation
The declaration `lemma_3_1_descent` is a theorem about a real-valued function $h$ on a finite-dimensional Euclidean space. The natural number $m$ gives the dimension: `EuclideanSpace m` abbreviates the real Euclidean space $\mathbb R^m$, modeled in Lean as functions from `Fin m` to $\mathbb R$. The function is $h:\mathbb R^m\to\mathbb R$, and $L$ is a real constant. The hypothesis `hL : HasLipschitzContinuousGradient h L` says that $h$ has an $L$-Lipschitz continuous gradient. In the proof this hypothesis is used through two concrete consequences: first, $h$ is differentiable at points, and second, for all $u,v\in\mathbb R^m$,

$$
\|\nabla h(u)-\nabla h(v)\|\le L\|u-v\|.
$$

The conclusion is that for every $x,y\in\mathbb R^m$,

$$
h(y)\le h(x)+\langle \nabla h(x),y-x\rangle+\frac{L}{2}\|y-x\|^2.
$$

This is the standard descent lemma: the value of $h$ at $y$ is bounded above by the first-order Taylor polynomial of $h$ at $x$, plus a quadratic correction term determined by the Lipschitz constant of the gradient. The inner product is the real inner product on $\mathbb R^m$, and $\|\cdot\|$ is the associated Euclidean norm.

## Lean proof
```lean
by
  intro x y
  let φ : Real -> EuclideanSpace m := fun t => AffineMap.lineMap x y t
  let q : Real -> Real := fun t =>
    h (φ t) - h x - t * inner Real (gradient h x) (y - x) -
      (L / 2) * t ^ 2 * ‖y - x‖ ^ 2
  have hq0 : q 0 = 0 := by
    simp [q, φ]
  have h_deriv (t₀ : Real) :
      HasDerivAt (fun t : Real => h (φ t))
        (inner Real (gradient h (φ t₀)) (y - x)) t₀ := by
    have hh_diffAt : DifferentiableAt Real h (φ t₀) := hL.2.1.differentiableAt
    have hline : HasDerivAt φ (y - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t₀))
    have hcomp :
        HasDerivAt (fun t : Real => h (φ t)) ((fderiv Real h (φ t₀)) (y - x)) t₀ :=
      hh_diffAt.hasFDerivAt.comp_hasDerivAt t₀ hline
    have hgrad :
        (fderiv Real h (φ t₀)) (y - x) =
          inner Real (gradient h (φ t₀)) (y - x) := by
      exact (inner_gradient_left hh_diffAt).symm
    simpa [hgrad] using hcomp
  have hq_deriv (t : Real) :
      HasDerivAt q
        (inner Real (gradient h (φ t) - gradient h x) (y - x) -
          L * t * ‖y - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : Real => h (φ s))
        (inner Real (gradient h (φ t)) (y - x)) t := h_deriv t
    have h2 : HasDerivAt (fun _ : Real => h x) 0 t := hasDerivAt_const t (h x)
    have h3 : HasDerivAt (fun s : Real => s * inner Real (gradient h x) (y - x))
        (inner Real (gradient h x) (y - x)) t := by
      simpa using
        (hasDerivAt_id t |>.mul_const (inner Real (gradient h x) (y - x)))
    have h4 : HasDerivAt (fun s : Real => (L / 2) * s ^ 2 * ‖y - x‖ ^ 2)
        (L * t * ‖y - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : Real => s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖y - x‖ ^ 2) using 1
      ring
    have hderiv := ((h1.sub h2).sub h3).sub h4
    simpa [q, sub_sub, inner_sub_left] using hderiv
  have hq_diff (t : Real) : DifferentiableAt Real q t :=
    (hq_deriv t).differentiableAt
  have hq_cont : Continuous q :=
    continuous_iff_continuousAt.mpr fun t => (hq_diff t).continuousAt
  have hq_contOn : ContinuousOn q (Set.Icc (0 : Real) 1) := hq_cont.continuousOn
  have hq_diffOn : DifferentiableOn Real q (Set.Ioo (0 : Real) 1) :=
    fun t _ => (hq_diff t).differentiableWithinAt
  have h_deriv_nonpos {t : Real} (ht : 0 < t) :
      inner Real (gradient h (φ t) - gradient h x) (y - x) -
          L * t * ‖y - x‖ ^ 2 <= 0 := by
    have h_cauchy :
        inner Real (gradient h (φ t) - gradient h x) (y - x) <=
          ‖gradient h (φ t) - gradient h x‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient h (φ t) - gradient h x‖ <= L * ‖φ t - x‖ :=
      hL.2.2 (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖y - x‖ := by
      have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y :=
        dist_left_lineMap x y t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner Real (gradient h (φ t) - gradient h x) (y - x) <=
          L * t * ‖y - x‖ ^ 2 := by
      calc
        inner Real (gradient h (φ t) - gradient h x) (y - x)
            <= ‖gradient h (φ t) - gradient h x‖ * ‖y - x‖ := h_cauchy
        _ <= (L * ‖φ t - x‖) * ‖y - x‖ := by
          nlinarith [h_lip, norm_nonneg (y - x)]
        _ = L * t * ‖y - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : Real) 1, deriv q c = (q 1 - q 0) / (1 - 0) :=
    exists_deriv_eq_slope q (by norm_num : (0 : Real) < 1) hq_contOn hq_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c :
      deriv q c =
        inner Real (gradient h (φ c) - gradient h x) (y - x) -
          L * c * ‖y - x‖ ^ 2 :=
    (hq_deriv c).deriv
  have h_deriv_c_nonpos : deriv q c <= 0 := by
    rw [h_deriv_c]
    exact h_deriv_nonpos hc.1
  rw [show (1 : Real) - 0 = 1 by norm_num, div_one, hq0, sub_zero] at hc_eq
  have hq1_nonpos : q 1 <= 0 := by linarith
  simp [q, φ] at hq1_nonpos
  linarith
```

## Proof explanation
The proof begins with `intro x y`, so it fixes arbitrary points $x,y\in\mathbb R^m$. It then defines the affine line

$$
\varphi(t)=\operatorname{lineMap}_{x,y}(t),
$$

which is the straight segment from $x$ to $y$, and the auxiliary real-valued function

$$
q(t)=h(\varphi(t))-h(x)-t\langle \nabla h(x),y-x\rangle-\frac{L}{2}t^2\|y-x\|^2.
$$

The purpose of $q$ is to measure the difference between the left-hand side and the desired upper bound along the line. At $t=1$, we have $\varphi(1)=y$, and

$$
q(1)=h(y)-h(x)-\langle \nabla h(x),y-x\rangle-\frac{L}{2}\|y-x\|^2.
$$

Thus the desired inequality is equivalent to $q(1)\le 0$. The rest of the proof establishes exactly this.

First, `hq0` proves $q(0)=0$. Since $\varphi(0)=x$, substituting $t=0$ into the definition of $q$ gives

$$
q(0)=h(x)-h(x)-0-0=0.
$$

Next, `h_deriv` computes the derivative of $t\mapsto h(\varphi(t))$. For each $t_0$, it shows

$$
\frac{d}{dt}\Big|_{t=t_0} h(\varphi(t))
=
\langle \nabla h(\varphi(t_0)),y-x\rangle.
$$

The proof uses the differentiability part of `hL`: from `hL.2.1.differentiableAt`, the function $h$ is differentiable at $\varphi(t_0)$. It also invokes `AffineMap.hasDerivAt_lineMap`, which says that the affine line $\varphi$ has derivative $y-x$ at $t_0$. The chain rule, via `comp_hasDerivAt`, then gives the derivative of the composition as

$$
(fderiv_{\mathbb R} h(\varphi(t_0)))(y-x).
$$

Finally, `inner_gradient_left` is the lemma relating the Fréchet derivative of a differentiable real-valued function to its gradient: applied here, it says

$$
(fderiv_{\mathbb R} h(\varphi(t_0)))(y-x)
=
\langle \nabla h(\varphi(t_0)),y-x\rangle.
$$

That gives the stated derivative.

Then `hq_deriv` differentiates the whole expression $q$. The derivative of the first term is the expression just computed. The derivative of the constant $h(x)$ is $0$, using `hasDerivAt_const`. The derivative of

$$
t\mapsto t\langle \nabla h(x),y-x\rangle
$$

is $\langle \nabla h(x),y-x\rangle$, using `hasDerivAt_id` and multiplication by a constant. The derivative of

$$
t\mapsto \frac{L}{2}t^2\|y-x\|^2
$$

is $L t\|y-x\|^2$, using `hasDerivAt_pow` for the derivative of $t^2$, then constant multiplication and simplification with `ring`. Combining these derivatives by subtraction and using `inner_sub_left`, which is linearity of the inner product in its first argument, gives

$$
q'(t)
=
\langle \nabla h(\varphi(t))-\nabla h(x),y-x\rangle
-
L t\|y-x\|^2.
$$

Next, `hq_diff`, `hq_cont`, `hq_contOn`, and `hq_diffOn` use the fact that $q$ has a derivative at every real $t$. Therefore $q$ is differentiable everywhere, hence continuous everywhere, hence continuous on the interval $[0,1]$, and differentiable on the open interval $(0,1)$. In Lean, `continuous_iff_continuousAt.mpr` reduces continuity to continuity at every point, and `DifferentiableAt.continuousAt` supplies continuity at each point.

The key estimate is `h_deriv_nonpos`. For any real $t>0$, it proves

$$
q'(t)\le 0.
$$

The argument is as follows. By `real_inner_le_norm`, the real Cauchy–Schwarz inequality,

$$
\langle \nabla h(\varphi(t))-\nabla h(x),y-x\rangle
\le
\|\nabla h(\varphi(t))-\nabla h(x)\|\,\|y-x\|.
$$

By the Lipschitz-gradient hypothesis `hL.2.2` applied to $\varphi(t)$ and $x$,

$$
\|\nabla h(\varphi(t))-\nabla h(x)\|
\le
L\|\varphi(t)-x\|.
$$

The proof then computes $\|\varphi(t)-x\|$. Using `dist_left_lineMap`, the distance from $x$ to $\varphi(t)=\operatorname{lineMap}_{x,y}(t)$ is

$$
\operatorname{dist}(x,\varphi(t))=|t|\operatorname{dist}(x,y).
$$

Since $t>0$, $|t|=t$, and therefore

$$
\|\varphi(t)-x\|=t\|y-x\|.
$$

Combining these inequalities yields

$$
\langle \nabla h(\varphi(t))-\nabla h(x),y-x\rangle
\le
L t\|y-x\|^2.
$$

Subtracting $L t\|y-x\|^2$ gives $q'(t)\le 0$. The tactic `nlinarith` is used to combine the Cauchy–Schwarz bound, the Lipschitz bound, and the nonnegativity of $\|y-x\|$.

The mean value theorem is then applied through `exists_deriv_eq_slope`. Since $q$ is continuous on $[0,1]$ and differentiable on $(0,1)$, there exists $c\in(0,1)$ such that

$$
q'(c)=\frac{q(1)-q(0)}{1-0}.
$$

The proof destructs this existential with `rcases`, obtaining $c$, the fact $c\in(0,1)$, and the slope equality. It then rewrites $q'(c)$ using `hq_deriv c`:

$$
q'(c)
=
\langle \nabla h(\varphi(c))-\nabla h(x),y-x\rangle
-
L c\|y-x\|^2.
$$

Since $c\in(0,1)$, in particular $c>0$, and `h_deriv_nonpos` gives $q'(c)\le 0$. The slope equality is rewritten using $1-0=1$, `div_one`, and $q(0)=0$, so it becomes $q'(c)=q(1)$. Therefore $q(1)\le 0$. This is the essential conclusion.

Finally, `simp [q, φ] at hq1_nonpos` simplifies $q(1)$. Since $\varphi(1)=y$, the inequality $q(1)\le 0$ becomes

$$
h(y)-h(x)-\langle \nabla h(x),y-x\rangle-\frac{L}{2}\|y-x\|^2\le 0.
$$

The tactic `linarith` rearranges this linear inequality into

$$
h(y)\le h(x)+\langle \nabla h(x),y-x\rangle+\frac{L}{2}\|y-x\|^2,
$$

which is exactly the desired conclusion for the arbitrary fixed $x,y$. Thus the theorem is proved.

