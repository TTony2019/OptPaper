## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/def_4.lean`

## Lean statement
```lean
noncomputable def energySeq (x : ℕ → H) (lam : ℕ → ℝ) (f : H → EReal) (n : ℕ) : EReal :=
  (((2 * (lam n)^2)⁻¹) * ‖x (n+1) - x n‖^2 : ℝ) + f (x (n+1))
```

## Statement explanation
The declaration `energySeq` defines an extended-real-valued energy expression associated with a sequence of iterates $x$, a sequence of real parameters $\lambda$, and an extended-real-valued objective function $f$. The variables are:

- $x : \mathbb{N} \to H$, a sequence of points in an ambient type $H$. The expression uses $x_{n+1}-x_n$ and its norm, so $H$ is being treated as a type on which subtraction and a norm are available.
- $\lambda : \mathbb{N} \to \mathbb{R}$, a sequence of real numbers. Its $n$-th value is written $\lambda_n$.
- $f : H \to \overline{\mathbb{R}}$, an extended-real-valued function on $H$. Here `EReal` is the Lean type of extended real numbers, so values may be finite or infinite.
- $n : \mathbb{N}$, the index at which the energy is evaluated. There is no restriction that $n$ be positive.

The definition returns an element of `EReal`, namely

$$
\operatorname{energySeq}(x,\lambda,f,n)
=
\left(\left(2(\lambda_n)^2\right)^{-1}\left\|x_{n+1}-x_n\right\|^2\right)
+
f(x_{n+1}).
$$

The first summand is explicitly forced to be a real number by the type ascription $: \mathbb{R}$. Thus Lean computes

$$
\left(2(\lambda_n)^2\right)^{-1}\left\|x_{n+1}-x_n\right\|^2
$$

as real arithmetic, and then this real number is regarded as an extended real in order to be added to $f(x_{n+1})$. Mathematically, when $\lambda_n \neq 0$, this real term is

$$
\frac{1}{2\lambda_n^2}\left\|x_{n+1}-x_n\right\|^2.
$$

Lean's real inverse is total, so if $\lambda_n = 0$, the value of $\left(2(\lambda_n)^2\right)^{-1}$ is $0$ in the real numbers rather than an undefined reciprocal. No nonzero hypothesis is included. The definition also imposes no finiteness, convexity, differentiability, or minimization assumption on $f$. It simply packages the weighted squared displacement between consecutive iterates together with the objective value at the next iterate. The keyword `noncomputable` indicates that Lean treats this as a noncomputable definition rather than executable data.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The source states that there is no proof, and the declaration is a `def`, so its mathematical content is exactly the defining equation displayed above. There are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, because no proof script is present. No named theorem, lemma, or previously established local result is invoked. Unfolding `energySeq` with arguments $x$, $\lambda$, $f$, and $n$ simply replaces $\operatorname{energySeq}(x,\lambda,f,n)$ by

$$
\left(\left(2(\lambda_n)^2\right)^{-1}\left\|x_{n+1}-x_n\right\|^2\right)
+
f(x_{n+1}),
$$

with the first term understood as a real number and the whole expression understood in the extended reals. Thus the declaration is a notational and structural definition of an energy quantity, not a theorem requiring proof.

