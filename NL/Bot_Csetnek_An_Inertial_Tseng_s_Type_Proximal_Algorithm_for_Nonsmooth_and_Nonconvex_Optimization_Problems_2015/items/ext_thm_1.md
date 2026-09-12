## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_thm_1.lean`

## Lean statement
```lean
theorem bregmanDistance_quadratic_bounds {m : Nat} (u : EuclideanSpace m -> Real)
    (sigma Lgrad_u : Real)
    (hstrong : StronglyConvexWith sigma u)
    (hgrad : HasLipschitzContinuousGradient u Lgrad_u) :
    ∀ x y : EuclideanSpace m,
      (sigma / 2) * ‖x - y‖ ^ 2 <= bregmanDistance u x y ∧
        bregmanDistance u x y <= (Lgrad_u / 2) * ‖x - y‖ ^ 2
```

## Statement explanation
The theorem `bregmanDistance_quadratic_bounds` states the following. For a natural number $m$, a function $u:\mathbb R^m\to\mathbb R$, and real parameters $\sigma$ and $L$, written in Lean as `sigma` and `Lgrad_u`, assume that $u$ is $\sigma$-strongly convex, `hstrong : StronglyConvexWith sigma u`, and that $u$ has $L$-Lipschitz continuous gradient, `hgrad : HasLipschitzContinuousGradient u Lgrad_u`. Then for every pair $x,y\in\mathbb R^m$, the Bregman distance of $u$ satisfies the two-sided quadratic bound

$$
\frac{\sigma}{2}\|x-y\|^2
\;\le\;
D_u(x,y)
\;\le\;
\frac{L}{2}\|x-y\|^2,
$$

where the Bregman distance is defined by

$$
D_u(x,y)
=u(x)-u(y)-\langle \nabla u(y),x-y\rangle .
$$

Here `EuclideanSpace m` is the finite-dimensional real Euclidean space $\mathbb R^m$, `gradient u y` is the gradient $\nabla u(y)$, and `inner Real` is the real inner product $\langle \cdot,\cdot\rangle$.

The lower bound is the quadratic growth estimate coming from strong convexity: it says that the Bregman distance, whose gradient is taken at the second argument $y$, is bounded below by $(\sigma/2)\|x-y\|^2$. The upper bound is the smoothness estimate coming from the Lipschitz continuity of the gradient: it says that the same Bregman distance is bounded above by $(L/2)\|x-y\|^2$. The proof uses the second component `hstrong.2` of strong convexity to know that

$$
G(z)=u(z)-\frac{\sigma}{2}\|z\|^2
$$

is convex. It uses the first component `hstrong.1` only as an auxiliary real inequality about $\sigma$ in the final arithmetic. It uses `hgrad.2.1` to extract global differentiability of $u$, and it uses the full Lipschitz-gradient hypothesis through the descent lemma in the upper-bound part.

## Lean proof
```lean
by
  intro x y
  constructor
  · let G : EuclideanSpace m -> Real :=
      fun z => u z - (sigma / 2) * ‖z‖ ^ 2
    let φ : Real -> Real := fun t => G (AffineMap.lineMap y x t)
    have hφ_conv : ConvexOn Real Set.univ φ := by
      simpa [G, φ] using
        (hstrong.2.comp_affineMap (AffineMap.lineMap y x : Real →ᵃ[Real] EuclideanSpace m))
    have hu_diff : Differentiable Real u := hgrad.2.1
    have hu_line :
        HasDerivAt (fun t : Real => u (AffineMap.lineMap y x t))
          (inner Real (gradient u y) (x - y)) 0 := by
      have huy : HasFDerivAt u (fderiv Real u y) y := (hu_diff y).hasFDerivAt
      have hline : HasDerivAt (AffineMap.lineMap y x : Real -> EuclideanSpace m) (x - y) 0 :=
        AffineMap.hasDerivAt_lineMap
      have hcomp :=
        HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : Real)) huy hline (by simp)
      have hfderiv_apply :
          fderiv Real u y (x - y) = inner Real (gradient u y) (x - y) := by
        exact (inner_gradient_left (𝕜 := Real) (f := u) (x := y) (y := x - y)
          (hu_diff y)).symm
      simpa [Function.comp_def, hfderiv_apply] using hcomp
    have hnorm_line :
        HasDerivAt (fun t : Real => ‖AffineMap.lineMap y x t‖ ^ 2)
          (2 * inner Real y (x - y)) 0 := by
      simpa using
        (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := (0 : Real))).norm_sq
    have hφ_deriv :
        HasDerivAt φ
          (inner Real (gradient u y) (x - y) -
            (sigma / 2) * (2 * inner Real y (x - y))) 0 := by
      unfold φ G
      exact hu_line.sub (hnorm_line.const_mul (sigma / 2))
    have hderiv_eq :
        deriv φ 0 =
          inner Real (gradient u y) (x - y) -
            (sigma / 2) * (2 * inner Real y (x - y)) :=
      hφ_deriv.deriv
    have hφ_diff : DifferentiableAt Real φ 0 := hφ_deriv.differentiableAt
    have hslope := hφ_conv.deriv_le_slope (x := (0 : Real)) (y := (1 : Real))
      (by simp) (by simp) (by norm_num) hφ_diff
    rw [hderiv_eq] at hslope
    dsimp [slope, φ, G, bregmanDistance] at hslope ⊢
    rw [show AffineMap.lineMap y x (0 : Real) = y by simp,
      show AffineMap.lineMap y x (1 : Real) = x by simp] at hslope
    norm_num at hslope
    have hnorm_id : ‖x‖ ^ 2 = ‖y‖ ^ 2 + 2 * inner Real y (x - y) + ‖x - y‖ ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_sq_real y (x - y))
    nlinarith [hnorm_id, hstrong.1]
  · have hdescent :=
      descent_of_hasLipschitzContinuousGradient u Lgrad_u hgrad y x
    dsimp [bregmanDistance] at hdescent ⊢
    linarith
```

## Proof explanation
The proof begins with `intro x y`, introducing arbitrary points $x,y\in\mathbb R^m$, and then `constructor`, splitting the goal into the two conjuncts: first the lower bound, then the upper bound.

For the lower bound, the proof defines

$$
G(z)=u(z)-\frac{\sigma}{2}\|z\|^2,
$$

and then composes $G$ with the affine line

$$
\phi(t)=G(y+t(x-y)).
$$

In Lean this line is written as `AffineMap.lineMap y x t`, so $\phi(t)=G(\mathrm{lineMap}_{y,x}(t))$. The hypothesis `hstrong.2` is the convexity part of strong convexity, namely convexity of $G$. The cited result `ConvexOn.comp_affineMap` says that precomposing a convex function with an affine map preserves convexity. Applying it to $G$ and the affine map $t\mapsto y+t(x-y)$ gives `hφ_conv : ConvexOn Real Set.univ φ`, i.e. $\phi$ is convex on all of $\mathbb R$. In ordinary terms, this is the standard Jensen convexity property of $\phi$:

$$
\phi((1-\lambda)s+\lambda t)
\le
(1-\lambda)\phi(s)+\lambda\phi(t)
$$

for all $s,t\in\mathbb R$ and all $0<\lambda<1$.

Next the proof obtains differentiability. From `hgrad.2.1` it gets `hu_diff : Differentiable Real u`, so $u$ is differentiable everywhere. This is needed for the chain rule and for identifying the Fréchet derivative with the gradient.

The proof then computes the derivative of $t\mapsto u(y+t(x-y))$ at $0$. It uses:
- `huy : HasFDerivAt u (fderiv Real u y) y`, the Fréchet derivative of $u$ at $y$;
- `hline : HasDerivAt (AffineMap.lineMap y x) (x-y) 0`, namely the derivative of the affine line $t\mapsto y+t(x-y)$ at $0$ is $x-y$;
- the chain rule `HasFDerivAt.comp_hasDerivAt_of_eq`, which composes these and gives that $t\mapsto u(y+t(x-y))$ has derivative

$$
\mathrm{fderiv}u(y)(x-y)
$$

at $0$.

The lemma `inner_gradient_left`, used here with $(f,x,y)=(u,y,x-y)$, gives the gradient–Fréchet derivative identity

$$
\mathrm{fderiv}u(y)(x-y)
=\langle \nabla u(y),x-y\rangle .
$$

Thus the derivative of the composed map $t\mapsto u(y+t(x-y))$ at $0$ is

$$
\langle \nabla u(y),x-y\rangle .
$$

This is `hu_line`.

The proof also computes the derivative of $t\mapsto \|y+t(x-y)\|^2$ at $0$. The result `AffineMap.hasDerivAt_lineMap` gives that the line $t\mapsto y+t(x-y)$ has derivative $x-y$ at $0$. The `.norm_sq` lemma for derivatives says that if a curve $c$ has derivative $v$ at $t$, then $t\mapsto \|c(t)\|^2$ has derivative

$$
2\langle c(t),v\rangle .
$$

At $t=0$, the curve value is $c(0)=y$ and $v=x-y$, so the derivative is

$$
2\langle y,x-y\rangle .
$$

This is `hnorm_line`.

Combining these two derivative computations with the subtraction rule and constant multiplication gives

$$
\phi'(0)
=\langle \nabla u(y),x-y\rangle
-\frac{\sigma}{2}\,2\langle y,x-y\rangle .
$$

The proof records this as `hφ_deriv`, then converts it to the equality `hderiv_eq` for `deriv φ 0`, and notes `hφ_diff : DifferentiableAt Real φ 0`.

Now convexity is used quantitatively. The cited result `ConvexOn.deriv_le_slope` says that for a convex differentiable function $\phi$, the derivative at a point is at most the secant slope to a later point. Applied to the points $0$ and $1$, it gives

$$
\phi'(0)\le \frac{\phi(1)-\phi(0)}{1-0}=\phi(1)-\phi(0).
$$

This is exactly the inequality `hslope`.

After rewriting the derivative and unfolding `slope`, `φ`, `G`, and `bregmanDistance`, the proof simplifies the endpoints:

$$
\phi(0)=G(y)=u(y)-\frac{\sigma}{2}\|y\|^2,
\qquad
\phi(1)=G(x)=u(x)-\frac{\sigma}{2}\|x\|^2.
$$

The endpoint evaluations are justified by rewriting

$$
\mathrm{lineMap}_{y,x}(0)=y,\qquad
\mathrm{lineMap}_{y,x}(1)=x.
$$

After `norm_num`, the slope inequality becomes

$$
\langle \nabla u(y),x-y\rangle-\sigma\langle y,x-y\rangle
\le
u(x)-u(y)-\frac{\sigma}{2}\bigl(\|x\|^2-\|y\|^2\bigr).
$$

The proof then uses the elementary real inner-product identity

$$
\|a+b\|^2=\|a\|^2+2\langle a,b\rangle+\|b\|^2,
$$

specialized through `norm_add_sq_real y (x-y)` to

$$
\|x\|^2
=\|y\|^2+2\langle y,x-y\rangle+\|x-y\|^2.
$$

This identity is `hnorm_id`. Substituting it into the previous inequality and cancelling the common term $-\sigma\langle y,x-y\rangle$ yields

$$
\langle \nabla u(y),x-y\rangle
\le
u(x)-u(y)-\frac{\sigma}{2}\|x-y\|^2,
$$

which is equivalent to

$$
\frac{\sigma}{2}\|x-y\|^2
\le
u(x)-u(y)-\langle \nabla u(y),x-y\rangle
=D_u(x,y).
$$

The final nonlinear arithmetic is closed by `nlinarith [hnorm_id, hstrong.1]`. The call to `nlinarith` performs this algebraic combination involving the squared norms and the scalar $\sigma$. The extra hypothesis `hstrong.1` is the scalar inequality about $\sigma$ supplied by the strong-convexity structure; it is used as auxiliary real arithmetic information in this final step.

For the upper bound, the proof invokes `descent_of_hasLipschitzContinuousGradient u Lgrad_u hgrad y x`. That cited descent lemma says that if $u$ has $L$-Lipschitz continuous gradient, then for all $a,b$,

$$
u(b)
\le
u(a)+\langle \nabla u(a),b-a\rangle+\frac{L}{2}\|b-a\|^2.
$$

With $a=y$ and $b=x$, it gives

$$
u(x)
\le
u(y)+\langle \nabla u(y),x-y\rangle+\frac{L}{2}\|x-y\|^2.
$$

The proof then uses `dsimp [bregmanDistance] at hdescent ⊢` to unfold the definition of Bregman distance in both the hypothesis and the goal. The goal at that point is

$$
u(x)-u(y)-\langle \nabla u(y),x-y\rangle
\le
\frac{L}{2}\|x-y\|^2.
$$

This is a direct linear rearrangement of the descent inequality: subtracting $u(y)+\langle \nabla u(y),x-y\rangle$ from both sides gives exactly the desired upper bound. The tactic `linarith` closes this linear arithmetic goal.

Thus the proof establishes both conjuncts: strong convexity gives the lower quadratic bound on the Bregman distance, and Lipschitz continuity of the gradient gives the upper quadratic bound.

