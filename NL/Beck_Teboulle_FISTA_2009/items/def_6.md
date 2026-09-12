## Source file
`Beck_Teboulle_FISTA_2009/items/def_6.lean`

## Lean statement
```lean
noncomputable def quadraticApprox {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f y + ⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2 + g x
```

## Statement explanation
The declaration `quadraticApprox` is a noncomputable definition. It has an implicit natural-number parameter $n : \mathbb N$, which determines the Euclidean space $\mathbb R^n$, formalized in Lean as `EuclideanSpace ℝ (Fin n)`. It takes two functions

$$
f : \mathbb R^n \to \mathbb R,
\qquad
g : \mathbb R^n \to \mathbb R,
$$

a real scalar $L : \mathbb R$, and two vectors $x,y \in \mathbb R^n$. It returns a real number. The defining equality is

$$
\operatorname{quadraticApprox}(f,g,L,x,y)
=
f(y)
+\left\langle \nabla f(y),\, x-y \right\rangle
+\frac{L}{2}\left\lVert x-y \right\rVert^2
+g(x).
$$

Here $\nabla f(y)$ is the Lean/Mathlib gradient term `gradient f y`, interpreted as an element of the same Euclidean space $\mathbb R^n$, and $\langle \cdot,\cdot\rangle$ is the Euclidean inner product. The expression is a sum of four real terms: the value of $f$ at the base point $y$, the first-order correction obtained from the gradient of $f$ at $y$, a quadratic penalty $(L/2)\lVert x-y\rVert^2$ measuring the squared distance from $x$ to $y$, and the value of $g$ at $x$. Thus the definition has the shape of a quadratic approximation to $f$ around $y$, with an additional term $g(x)$. No hypotheses are imposed: $f$ and $g$ need not be differentiable or convex, and $L$ need not be positive. The definition is total, assigning a real number to every choice of $n,f,g,L,x,y$; the `noncomputable` marker indicates that Lean does not extract executable code from it, not that the mathematical expression is undefined.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source consists only of a `noncomputable def`, so there are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorem, lemma, or local cited result is invoked. The only mathematical content is the definition itself.

The right-hand side is assembled as a real-valued expression from four real summands. First, `f y` is the value of the real-valued function $f$ at $y$. Second, `⟪gradient f y, x - y⟫` is the Euclidean inner product of the vector `gradient f y` with the difference vector $x-y$; both arguments lie in $\mathbb R^n$, so the inner product is a real number. Third, `(L / 2) * ‖x - y‖ ^ 2` is the real scalar $L/2$ multiplied by the square of the Euclidean norm of $x-y$, again a real number. Fourth, `g x` is the value of the real-valued function $g$ at $x$. Adding these four real numbers yields the real number that the definition assigns to $\operatorname{quadraticApprox}(f,g,L,x,y)$. No further verification is required beyond the fact that all terms have type $\mathbb R$ and that the ambient definitions, such as the gradient and the inner product, are available in the noncomputable setting.

