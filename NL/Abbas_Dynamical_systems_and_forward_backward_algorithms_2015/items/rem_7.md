## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_7.lean`

## Lean statement
```lean
theorem gradient_rate_comparison {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → ℝ) (xSemigroup xNewton : ℝ → H) (c : ℝ)
    (hconvex : ConvexOn ℝ Set.univ Phi) (hgradient : Differentiable ℝ Phi)
    (hc : 0 < c)
    (hmin : ∃ z : H, ∀ y : H, Phi z ≤ Phi y)
    (hsemigroup : ∀ t, 0 ≤ t → HasDerivAt xSemigroup (-∇ Phi (xSemigroup t)) t)
    (hsemigroup_vclassical : ∀ t, 0 ≤ t →
      HasDerivAt (fun s ↦ ∇ Phi (xSemigroup s))
        (deriv (fun s ↦ ∇ Phi (xSemigroup s)) t) t)
    (hnewton_xclassical : ∀ t, 0 ≤ t → HasDerivAt xNewton (deriv xNewton t) t)
    (hnewton_vclassical : ∀ t, 0 ≤ t →
      HasDerivAt (fun s ↦ ∇ Phi (xNewton s)) (deriv (fun s ↦ ∇ Phi (xNewton s)) t) t)
    (hnewton : ∀ t, 0 ≤ t → (c * Real.exp (-t)) • deriv xNewton t +
      deriv (fun s ↦ ∇ Phi (xNewton s)) t + ∇ Phi (xNewton t) = 0) :
    (∃ C : ℝ, ∀ t, 0 < t → ‖∇ Phi (xSemigroup t)‖ ≤ C / t) ∧
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖∇ Phi (xNewton t)‖ ≤ C * Real.exp (-t)
```

## Statement explanation
The declaration is a theorem about two different gradient-based dynamics in a complete real inner product space $H$, hence in a real Hilbert space. It fixes a real-valued function $\Phi : H \to \mathbb R$, two trajectories $x_{\mathrm{sg}} : \mathbb R \to H$ and $x_{\mathrm{nt}} : \mathbb R \to H$, and a real scalar $c$. The names suggest $x_{\mathrm{sg}}$ is a semigroup/gradient-flow trajectory and $x_{\mathrm{nt}}$ is a Newton-type trajectory.

The common hypotheses on $\Phi$ are:

- $\Phi$ is convex on the whole space $H$, i.e. `ConvexOn ℝ Set.univ Phi`.
- $\Phi$ is differentiable, i.e. `Differentiable ℝ Phi`.
- $\Phi$ has a global minimum: there exists $z \in H$ such that $\Phi(z) \le \Phi(y)$ for every $y \in H$.
- The scalar $c$ is positive: $c > 0$.

The hypotheses on the semigroup trajectory $x_{\mathrm{sg}}$ are:

- For every $t \ge 0$, $x_{\mathrm{sg}}$ has derivative

  $$
  -\nabla \Phi(x_{\mathrm{sg}}(t))
  $$

  at $t$. Thus $x_{\mathrm{sg}}$ solves the gradient-flow equation

  $$
  \dot{x}_{\mathrm{sg}}(t) = -\nabla \Phi(x_{\mathrm{sg}}(t)).
  $$

- For every $t \ge 0$, the map

  $$
  s \mapsto \nabla \Phi(x_{\mathrm{sg}}(s))
  $$

  is differentiable at $t$, with derivative its classical Lean derivative `deriv`.

The hypotheses on the Newton trajectory $x_{\mathrm{nt}}$ are:

- For every $t \ge 0$, $x_{\mathrm{nt}}$ is differentiable at $t$, with derivative `deriv xNewton t`.
- For every $t \ge 0$, the map

  $$
  s \mapsto \nabla \Phi(x_{\mathrm{nt}}(s))
  $$

  is differentiable at $t$, with derivative its classical Lean derivative `deriv`.
- For every $t \ge 0$, the Newton-type equation holds:

  $$
  c e^{-t} \dot{x}_{\mathrm{nt}}(t)
  + \frac{d}{dt}\nabla \Phi(x_{\mathrm{nt}}(t))
  + \nabla \Phi(x_{\mathrm{nt}}(t))
  = 0.
  $$

  Here the addition and the zero are those of the vector space $H$, while $c e^{-t}$ is a real scalar multiplying the velocity vector.

The conclusion is a conjunction of two rate statements:

$$
\Bigl(\exists C \in \mathbb R,\ \forall t > 0,\ 
\lVert \nabla \Phi(x_{\mathrm{sg}}(t)) \rVert \le C/t\Bigr)
\land
\Bigl(\exists C \in \mathbb R,\ \forall t \ge 0,\ 
\lVert \nabla \Phi(x_{\mathrm{nt}}(t)) \rVert \le C e^{-t}\Bigr).
$$

Thus the semigroup/gradient-flow trajectory has gradient norm decaying like $O(1/t)$ for positive times, while the Newton-type trajectory has gradient norm decaying exponentially like $O(e^{-t})$ for nonnegative times. The two existential constants $C$ are independent; the statement does not assert that they are equal or that one estimate implies the other. It simply packages both decay rates under the shared convexity, differentiability, and minimum assumptions.

## Lean proof
```lean
by
  refine ⟨?_, newton_gradient_exponential_rate Phi xNewton c hconvex hgradient hc hmin
    hnewton_xclassical hnewton_vclassical hnewton⟩
  exact semigroup_gradient_rate Phi xSemigroup hconvex hgradient hmin hsemigroup
    hsemigroup_vclassical
```

## Proof explanation
The proof is a direct combination of the two previously established rate theorems.

First, the target is a conjunction. The tactic

- `refine` is used to introduce the conjunction. The anonymous constructor splits the goal into two components: the first component is left as a placeholder goal, and the second component is filled by the term
  `newton_gradient_exponential_rate Phi xNewton c hconvex hgradient hc hmin hnewton_xclassical hnewton_vclassical hnewton`.

The theorem `newton_gradient_exponential_rate`, specialized to the current variables, says the following. If $H$ is a complete real inner product space, $\Phi$ is convex on the whole space and differentiable, $c>0$, $\Phi$ has a global minimum, the trajectory $x$ satisfies

$$
\dot{x}(t)=\text{deriv }x(t)
$$

at every $t\ge0$, the gradient field $s\mapsto \nabla\Phi(x(s))$ is differentiable at every $t\ge0$, and the Newton-type system

$$
c e^{-t}\dot{x}(t)
+ \frac{d}{dt}\nabla\Phi(x(t))
+ \nabla\Phi(x(t))=0
$$

holds for every $t\ge0$, then there exists a constant $C$ such that

$$
\lVert \nabla\Phi(x(t))\rVert \le C e^{-t}
$$

for every $t\ge0$.

In the current proof this theorem is applied with $x = x_{\mathrm{nt}}$. The hypotheses supplied to it are exactly `hconvex`, `hgradient`, `hc`, `hmin`, `hnewton_xclassical`, `hnewton_vclassical`, and `hnewton`. Its conclusion is precisely the second conjunct of the target:

$$
\exists C,\ \forall t\ge0,\ 
\lVert \nabla \Phi(x_{\mathrm{nt}}(t)) \rVert \le C e^{-t}.
$$

So after the `refine`, the second part of the conjunction is proved, and only the first part remains.

The remaining goal is then closed by

- `exact semigroup_gradient_rate Phi xSemigroup hconvex hgradient hmin hsemigroup hsemigroup_vclassical`.

The theorem `semigroup_gradient_rate`, specialized here, says that if $\Phi$ is convex on the whole space and differentiable, $\Phi$ has a global minimum, the trajectory $x$ satisfies

$$
\dot{x}(t)=-\nabla\Phi(x(t))
$$

for every $t\ge0$, and the gradient field $s\mapsto \nabla\Phi(x(s))$ is differentiable at every $t\ge0$, then there exists a constant $C$ such that

$$
\lVert \nabla\Phi(x(t))\rVert \le C/t
$$

for every $t>0$.

In the current proof this theorem is applied with $x = x_{\mathrm{sg}}$. The hypotheses supplied to it are `hconvex`, `hgradient`, `hmin`, `hsemigroup`, and `hsemigroup_vclassical`. Its conclusion is exactly the first conjunct:

$$
\exists C,\ \forall t>0,\ 
\lVert \nabla \Phi(x_{\mathrm{sg}}(t)) \rVert \le C/t.
$$

Therefore the placeholder goal is solved, and the full conjunction follows.

No `intro`, `rw`, `simp`, or `linarith` tactic is used in this proof. The proof is purely term-style: `refine` performs conjunction introduction and leaves one subgoal, and `exact` closes that subgoal by supplying the appropriate rate theorem.

