## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/def_1.lean`

## Lean statement
```lean
def IsStrongOrbitWithVelocity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (B : H → H) (lam : ℝ)
    (x v dx dv : ℝ → H) : Prop :=
  (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b) ∧
  (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b) ∧
  (∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t)) ∧
  (∀ᵐ t ∂volume.restrict (Set.Ici 0),
    HasDerivAt x (dx t) t ∧ HasDerivAt v (dv t) t ∧
      lam • dx t + dv t + v t + B (x t) = 0)
```

## Statement explanation
The declaration defines a predicate `IsStrongOrbitWithVelocity`. It is parameterized by an implicit type $H$ with the typeclass assumptions `[NormedAddCommGroup H]` and `[InnerProductSpace ℝ H]`, so $H$ is a real inner product space and a normed additive commutative group. Its explicit arguments are an extended-real-valued function

```math
\Phi : H \to \{\, y \in \mathrm{EReal} \mid y > \bot \,\},
```

where $\bot$ is the bottom element of the extended real order and `Set.Ioi (⊥ : EReal)` is the subtype of extended reals strictly above $\bot$; a map $B : H \to H$; a real parameter $\lambda \in \mathbb{R}$; and four curves $x, v, dx, dv : \mathbb{R} \to H$.

For these data, the proposition `IsStrongOrbitWithVelocity Phi B lam x v dx dv` is the conjunction of four conditions. First, for every positive real $b$, the curve $x$ is absolutely continuous on the interval from $0$ to $b$. Second, for every positive real $b$, the curve $v$ is absolutely continuous on the same kind of interval. Third, for every $t$ with $0 \le t$, the vector $v(t)$ belongs to the subdifferential of $\Phi$ at $x(t)$, i.e.

$$
v(t) \in \partial \Phi(x(t)),
$$

using the imported subdifferential operator `ERealFunction.subdifferential`. Fourth, for almost every $t$ with respect to the Lebesgue measure restricted to $[0,\infty)$, the curve $x$ has derivative $dx(t)$ at $t$, the curve $v$ has derivative $dv(t)$ at $t$, and the vector equation

$$
\lambda \cdot dx(t) + dv(t) + v(t) + B(x(t)) = 0
$$

holds in $H$.

In ordinary language, the predicate says that the pair of curves $(x,v)$ is a strong orbit with velocity $v$: both $x$ and $v$ are absolutely continuous on every finite interval starting at $0$; the velocity $v(t)$ is always a subgradient of $\Phi$ at $x(t)$ for nonnegative times; and almost everywhere on $[0,\infty)$, the supplied curves $dx$ and $dv$ are the derivatives of $x$ and $v$, and these derivatives satisfy the differential equation $\lambda dx + dv + v + B(x) = 0$. The subgradient condition is imposed pointwise for every $t \ge 0$, whereas the derivative and differential equation condition is imposed only almost everywhere.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, and its body is exactly the four-conjunct proposition described above. Consequently there are no proof steps, no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named lemmas or previously established facts are invoked. The entire mathematical content is the definitional unfolding of `IsStrongOrbitWithVelocity` into the four conditions: absolute continuity of $x$, absolute continuity of $v$, the pointwise subgradient condition $v(t) \in \partial \Phi(x(t))$ for all $t \ge 0$, and the almost-everywhere derivative and differential equation condition on $[0,\infty)$.

