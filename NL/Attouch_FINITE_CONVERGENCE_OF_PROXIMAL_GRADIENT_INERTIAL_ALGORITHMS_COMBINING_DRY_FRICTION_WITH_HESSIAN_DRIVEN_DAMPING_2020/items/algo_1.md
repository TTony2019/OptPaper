## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_1.lean`

## Lean statement
```lean
structure IPAHDD {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (h gamma beta : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  x : ℕ → H
  initial0 : H
  initial1 : H
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩
      ((1 / (h * (1 + h * gamma))) • (x (k + 1) - x k) -
       (beta / (1 + h * gamma)) • (gradient f (x (k + 1)) - gradient f (x k)) -
       (h / (1 + h * gamma)) • gradient f (x (k + 1)) )
```

## Statement explanation
The declaration `IPAHDD` is a structure, i.e. a record type, describing an iterative algorithm rather than proving a theorem. Its ambient space is a real Hilbert space $H$: the assumptions `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H` say that $H$ is a complete real inner-product space. The structure is parameterized by:

- an objective function $f : H \to \mathbb R$;
- an extended-real-valued function $\phi : H \to \operatorname{Ioi}(\bot_{\overline{\mathbb R}})$, whose codomain is the set of extended reals strictly larger than the bottom element; in ordinary notation this means $\phi$ takes values in $(-\infty,+\infty]$ and never takes the value $-\infty$;
- a proof $hφ$ that $\phi$ lies in $\Gamma_0(H)$, the class of proper, convex, lower semicontinuous extended-real-valued functions on $H$;
- real parameters $h,\gamma,\beta$.

The fields of the structure impose the following conditions.

First, $h$ and $\gamma$ are positive:

$$
h>0,\qquad \gamma>0.
$$

There is no corresponding sign condition on $\beta$ in this declaration.

Second, the structure contains a sequence

$$
x : \mathbb N \to H
$$

and two initial points `initial0`, `initial1`, together with assertions that

$$
x_0=\text{initial0},\qquad x_1=\text{initial1}.
$$

Thus the sequence is seeded by two initial iterates.

Third, for every natural number $k$, the field `update` asserts the recurrence

$$
x_{k+2}
=
x_{k+1}
+
h\,
P_{\phi,\, h/(1+h\gamma)}
\left(
\frac{x_{k+1}-x_k}{h(1+h\gamma)}
-
\frac{\beta}{1+h\gamma}
\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
-
\frac{h}{1+h\gamma}
\nabla f(x_{k+1})
\right),
$$

where $P_{\phi,\lambda}$ denotes the scaled proximity operator of $\phi$ with scale $\lambda$, namely the operator named `ERealFunction.scaledProximityOperator` in the source. The scale used here is

$$
\lambda=\frac{h}{1+h\gamma}.
$$

The recurrence combines a momentum or inertial term $(x_{k+1}-x_k)/(h(1+h\gamma))$, a gradient-difference correction involving $\beta$, and a gradient step at $x_{k+1}$, then applies the scaled proximity operator of $\phi$ and adds the result to $x_{k+1}$ after multiplication by $h$.

In summary, an inhabitant of `IPAHDD f φ hφ h gamma beta` is an algorithm trajectory $x$ on a real Hilbert space, starting from two prescribed initial points and satisfying the displayed proximal-gradient recurrence for every $k\in\mathbb N$. The declaration itself does not assert that such a trajectory exists; it specifies what it means to be one.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof of the declaration as a whole, because it is a `structure` declaration. A structure declaration introduces a record type: it lists data fields and proof fields that any inhabitant of the structure must supply. It does not prove existence of an inhabitant. The only proof script appearing in the source is the `by` block inside the `update` field, where Lean must prove that a certain real number is positive before it can be passed to the scaled proximity operator.

That proof obligation is to show

$$
0<\frac{h}{1+h\gamma}.
$$

It is handled as follows. First, Lean introduces the local fact `hden`:

$$
0<1+h\gamma.
$$

This is proved by `nlinarith`, supplied with the fact obtained from `mul_pos h_pos gamma_pos`. The lemma `mul_pos` says that the product of two positive real numbers is positive, so from $h>0$ and $\gamma>0$ it gives

$$
0<h\gamma.
$$

The tactic `nlinarith` then uses $0<h\gamma$ to prove $0<1+h\gamma$, since $1$ is positive and adding a positive quantity preserves positivity.

Second, Lean uses `exact div_pos h_pos hden`. The lemma `div_pos` states that if the numerator and denominator are positive, then the quotient is positive. Here the numerator is $h>0$, and the denominator is $1+h\gamma>0$, so it yields

$$
0<\frac{h}{1+h\gamma}.
$$

This proof is exactly the second component of the subtype expression

$$
\left\langle \frac{h}{1+h\gamma},\ \text{proof of positivity}\right\rangle,
$$

which packages the positive scale required by `ERealFunction.scaledProximityOperator`. The `exact` command closes the proof goal by providing this term directly.

After that positivity proof has been supplied, the `update` field simply asserts the recurrence for an arbitrary $k\in\mathbb N$. The right-hand side depends only on $x_{k+1}$, $x_k$, the gradient of $f$ at those two points, and the scaled proximity operator of $\phi$. The scalar coefficients are

$$
\frac{1}{h(1+h\gamma)},\qquad -\frac{\beta}{1+h\gamma},\qquad -\frac{h}{1+h\gamma},
$$

multiplying respectively the inertial difference, the gradient difference, and the gradient at $x_{k+1}$. The resulting vector is passed through the scaled proximity operator with scale $h/(1+h\gamma)$, multiplied by $h$, and added to $x_{k+1}$ to define $x_{k+2}$. The initial fields `init0` and `init1` supply the two starting values $x_0$ and $x_1$, so the recurrence determines the rest of the sequence. No `intro`, `rw`, `simp`, or `linarith` command occurs in this declaration; the only proof-relevant commands are the `by` block, `have`, `nlinarith`, and `exact`.

