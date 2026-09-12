## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_def_1.lean`

## Lean statement
```lean
noncomputable def HasLipschitzContinuousGradient {m : Nat}
    (h : EuclideanSpace m -> Real) (L : Real) : Prop :=
  0 <= L ∧ Differentiable Real h ∧
    ∀ x y : EuclideanSpace m,
      ‖gradient h x - gradient h y‖ <= L * ‖x - y‖
```

## Statement explanation
The declaration defines the predicate `HasLipschitzContinuousGradient`. It takes three parameters: a natural number $m$, a function $h:\mathbb R^m\to\mathbb R$ from the $m$-dimensional Euclidean space to the real numbers, and a real constant $L$. It returns a proposition asserting that the gradient of $h$ is Lipschitz continuous with constant $L$.

The proposition is the conjunction of three conditions:

1. The constant is nonnegative:

$$
0 \le L.
$$

2. The function $h$ is differentiable over $\mathbb R$ as a map $h:\mathbb R^m\to\mathbb R$.
3. For every pair of points $x,y\in\mathbb R^m$,

```math
\|\nabla h(x)-\nabla h(y)\| \le L\|x-y\|.
```

   Here $\nabla h(x)$ denotes the gradient vector of $h$ at $x$, and both norms are the Euclidean norms on the relevant Euclidean spaces.

Thus, mathematically, `HasLipschitzContinuousGradient h L` says that $L\ge 0$, that $h$ is differentiable, and that the gradient map

$$
x\mapsto \nabla h(x)
$$

is Lipschitz continuous with Lipschitz constant $L$. The definition does not assert convexity, stronger smoothness, or that $L$ is the smallest possible Lipschitz constant. It only records these three requirements as a proposition. The Lean keyword `noncomputable` indicates that the definition is marked as noncomputational, but this does not change its mathematical content.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, and the supplied source contains only the defining proposition with a comment indicating that no proof is provided. Consequently, there are no proof steps, no `intro` or `rw` or `simp` or `exact` or `linarith` commands, and no cited lemmas or theorems to explain. No named local result is invoked.

If one wanted to prove that some particular pair $h,L$ satisfies `HasLipschitzContinuousGradient h L`, one would have to establish each of the three conjuncts: first $0\le L$, second that $h$ is differentiable, and third the gradient Lipschitz estimate

```math
\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|
```

for all $x,y\in\mathbb R^m$. The definition itself simply states that these three conditions are required. Since no proof is supplied in the source, there are no further mathematical proof obligations or tactic applications to describe.

