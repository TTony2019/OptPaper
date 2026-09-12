## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_def_7.lean`

## Lean statement
```lean
noncomputable def bregmanDistance {m : Nat} (u : EuclideanSpace m -> Real)
    (x y : EuclideanSpace m) : Real :=
  u x - u y - inner Real (gradient u y) (x - y)
```

## Statement explanation
The declaration `bregmanDistance` is a noncomputable definition. It takes an implicit natural number $m$, a real-valued function

$$
u : \mathbb{R}^m \to \mathbb{R}
$$

on the real Euclidean space of dimension $m$, and two points

$$
x,y \in \mathbb{R}^m.
$$

It returns the real number

$$
\operatorname{bregmanDistance}(u,x,y)
= u(x)-u(y)-\langle \nabla u(y), x-y\rangle_{\mathbb{R}}.
$$

Here `gradient u y` is the gradient of $u$ at $y$, viewed as a vector in $\mathbb{R}^m$, and `inner Real` is the real inner product. Thus the definition subtracts from $u(x)$ the value at $x$ of the first-order affine approximation

$$
u(y)+\langle \nabla u(y), x-y\rangle
$$

of $u$ based at $y$. Equivalently, it is the error in the linear approximation of $u$ at $y$ when evaluated at $x$. The expression is asymmetric in $x$ and $y$, and the Lean declaration itself asserts no convexity, differentiability, nonnegativity, symmetry, or metric properties; it simply introduces this real-valued function of $u,x,y$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, so its mathematical content is exactly the defining equation already displayed. The keyword `noncomputable def` indicates that the definition is noncomputable, as is typical when using the `gradient` operator in the ambient library; it does not add hypotheses or conclusions. The right-hand side is the displayed Bregman expression

$$
u(x)-u(y)-\langle \nabla u(y), x-y\rangle_{\mathbb{R}}.
$$

No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named lemmas or previously established results are invoked. Consequently, there are no proof steps to explain beyond the definition itself.

