## Source file
`Beck_Teboulle_FISTA_2009/items/def_3.lean`

## Lean statement
```lean
structure IsC11 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : outParam ℝ) : Prop where
  hL_pos : 0 < L
  contDiff : ContDiff ℝ 1 f
  grad_lipschitz : LipschitzWith (Real.toNNReal L) (fun x : EuclideanSpace ℝ (Fin n) => gradient f x)
```

## Statement explanation
The declaration defines a Lean structure named `IsC11`. It has an implicit natural-number parameter $n$, a function

$$
f : \mathbb R^n \to \mathbb R
$$

where the Lean type `EuclideanSpace ℝ (Fin n)` is the usual $n$-dimensional real Euclidean space, and a real parameter $L$. The annotation `outParam` on $L$ is a Lean elaboration mechanism for typeclass inference; mathematically it merely means that $L$ is a real constant associated with $f$. The structure is declared in `Prop`, so an inhabitant of `IsC11 f L` is a proof that $f$ satisfies the listed conditions with constant $L$.

The structure has exactly three fields:

1. `hL_pos : 0 < L`, meaning the constant $L$ is positive.

2. `contDiff : ContDiff ℝ 1 f`, meaning $f$ is $C^1$ over $\mathbb R$. The order $1$ records one continuous derivative: $f$ is differentiable and its derivative is continuous.

3. `grad_lipschitz : LipschitzWith (Real.toNNReal L) (fun x : EuclideanSpace ℝ (Fin n) => gradient f x)`, meaning the gradient map

$$
x \mapsto \nabla f(x)
$$

   is Lipschitz with constant `Real.toNNReal L`. Since `LipschitzWith` takes a nonnegative real constant and `Real.toNNReal L` is the nonnegative version of $L$, the first field $0\lt L$ makes this constant literally $L$. Thus this field says that for all $x,y\in\mathbb R^n$,

```math
\|\nabla f(x)-\nabla f(y)\| \le L\|x-y\|.
```

Cohesively, `IsC11 f L` says that $f$ is a $C^1$ function on $\mathbb R^n$ whose gradient is Lipschitz continuous with modulus $L$, and that this modulus is positive. This is the $C^{1,1}$ regularity condition with a specified Lipschitz constant for the gradient.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a structure definition, not a theorem with a proof script, so there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no local named result is invoked.

In Lean, a structure in `Prop` is a named package of propositions. To construct a term of type `IsC11 f L`, one must supply exactly the three fields: a proof of $0\lt L$, a proof that $f$ is $C^1$, and a proof that the gradient map $x\mapsto \nabla f(x)$ is Lipschitz with constant `Real.toNNReal L`. Conversely, if $h : \text{IsC11 } f \ L$, then `h.hL_pos` gives $0\lt L$, `h.contDiff` gives the $C^1$ regularity of $f$, and `h.grad_lipschitz` gives the Lipschitz estimate for the gradient. The `outParam` annotation on $L$ has no mathematical proof content; it only affects how Lean infers the constant $L$ during elaboration.

