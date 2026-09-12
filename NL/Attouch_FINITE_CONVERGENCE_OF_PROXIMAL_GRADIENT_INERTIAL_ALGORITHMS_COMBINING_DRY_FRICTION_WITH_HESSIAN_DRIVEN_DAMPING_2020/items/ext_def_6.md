## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/ext_def_6.lean`

## Lean statement
```lean
noncomputable def softThreshold (a : ℝ) (_ha : 0 ≤ a) (t : ℝ) : ℝ :=
  Real.sign t * max (|t| - a) 0
```

## Statement explanation
The declaration defines a real-valued function named `softThreshold`. It takes three arguments: a real number $a$, a proof $h_a$ of the hypothesis $0 \le a$, and a real number $t$. The hypothesis argument is named `_ha`; the leading underscore indicates that the defining expression does not use it, but the type still requires such a proof whenever the function is applied. The result is the real number

$$
\mathrm{sign}(t)\max(|t|-a,0),
$$

where $\mathrm{sign}(t)$ is the real sign function, $|t|$ is the absolute value of $t$, and $\max(|t|-a,0)$ is the positive part of $|t|-a$. Thus the definition is

$$
\mathrm{softThreshold}(a,h_a,t)
=\mathrm{sign}(t)\max(|t|-a,0).
$$

Mathematically this is the soft-thresholding operator with threshold $a$. Since $a$ is assumed nonnegative, it can be described piecewise as

$$
\mathrm{softThreshold}(a,h_a,t)
=\begin{cases}
t-a, & t>a,\\
0, & |t|\le a,\\
t+a, & t<-a.
\end{cases}
$$

So inputs whose magnitude is at most $a$ are sent to $0$, while inputs whose magnitude exceeds $a$ are shifted toward zero by $a$ while retaining their sign. When $a=0$, the formula reduces to $t$ for every real $t$. The proof argument $h_a$ records the nonnegativity of the threshold but does not enter the computed value.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a definition, and the proof block explicitly says that there is no separate proof part. Therefore no tactic such as `intro`, `rw`, `simp`, or `exact` is used, no hypothesis is introduced in a proof step, and no named theorem or lemma is invoked.

The mathematical content is exactly the defining equality

$$
\mathrm{softThreshold}(a,h_a,t)
=\mathrm{sign}(t)\max(|t|-a,0).
$$

In Lean, this equality holds by definitional unfolding: any occurrence of `softThreshold a h_a t` can be replaced by the right-hand side. The argument `_ha`, which carries the proof of $0 \le a$, is part of the function signature but is ignored by the body, so the value of the function does not depend on which proof of $0 \le a$ is supplied. The marker `noncomputable` classifies the definition for Lean’s purposes; it does not add any mathematical hypothesis or conclusion. Since no proof is provided, no further mathematical facts are used.

