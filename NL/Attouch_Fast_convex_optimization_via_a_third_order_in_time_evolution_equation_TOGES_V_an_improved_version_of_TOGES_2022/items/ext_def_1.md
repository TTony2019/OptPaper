## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_def_1.lean`

## Lean statement
```lean
structure ConvexDifferentiableObjective (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  f : H → ℝ
  differentiable : ∀ x : H, DifferentiableAt ℝ f x
  convex : ∀ x y : H, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    f ((1 - s) • x + s • y) ≤ (1 - s) * f x + s * f y
  firstOrder : ∀ x y : H, f y ≥ f x + inner ℝ (gradient f x) (y - x)
```

## Statement explanation
The declaration `ConvexDifferentiableObjective` defines a structure, i.e. a type of records, parametrized by a type $H$. The typeclass assumptions say that $H$ is a normed additive commutative group, a real normed vector space, a real inner product space, and complete. Together these mean that $H$ is a real Hilbert space. There is no finite-dimensionality assumption.

An inhabitant of this structure consists of the following data and proofs:

- A function

  $$
  f : H \to \mathbb{R},
  $$

  called the objective function.

- A proof field `differentiable` asserting that for every $x \in H$, the function $f$ is differentiable at $x$ over $\mathbb{R}$. In analytic terms, this is Fréchet differentiability at every point of $H$.

- A proof field `convex` asserting that for all $x,y \in H$ and all $s \in \mathbb{R}$ with

  $$
  0 \le s \le 1,
  $$

  one has

  $$
  f\bigl((1-s)x + s y\bigr)
  \le
  (1-s) f(x) + s f(y).
  $$

  This is precisely the usual definition of convexity of the real-valued function $f$ along line segments in $H$.

- A proof field `firstOrder` asserting that for all $x,y \in H$,

  $$
  f(y)
  \ge
  f(x) + \langle \nabla f(x),\, y-x\rangle .
  $$

  Here $\nabla f(x)$ is the gradient of $f$ at $x$, and $\langle \cdot,\cdot\rangle$ is the real inner product on $H$. This is the first-order lower bound inequality: the value of $f$ at $y$ is at least the value of its first-order Taylor approximation at $x$, evaluated at $y$.

Thus the structure packages together a real-valued differentiable convex function on a real Hilbert space together with the standard first-order inequality. The declaration itself does not assert that such a function exists for a given $H$; it only specifies what it means to be such an objective function.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part in the source. The declaration is a `structure`, not a theorem, so there are no proof steps, tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named lemmas or theorems invoked. The mathematical content is entirely contained in the fields of the structure: a function $f : H \to \mathbb{R}$, a proof that $f$ is differentiable at every point, a proof that $f$ is convex, and a proof of the first-order inequality

$$
f(y) \ge f(x) + \langle \nabla f(x), y-x\rangle
$$

for all $x,y \in H$. To construct an inhabitant of `ConvexDifferentiableObjective`, one would have to supply exactly those four components.

