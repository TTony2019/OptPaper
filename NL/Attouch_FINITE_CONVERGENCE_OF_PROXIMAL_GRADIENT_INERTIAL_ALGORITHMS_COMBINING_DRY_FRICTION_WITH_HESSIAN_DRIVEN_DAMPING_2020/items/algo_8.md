## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_8.lean`

## Lean statement
```lean
structure IPAHDDLasso {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → Set.Ioi (⊥ : EReal)) (hΦ : Φ ∈ Γ₀(H))
    (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H) (lam h gamma beta : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  lam_pos : 0 < lam
  x : ℕ → H
  y : ℕ → H
  z : ℕ → H
  initial0 : H
  initial1 : H
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  metric : M = ContinuousLinearMap.id ℝ H - lam • (A.adjoint.comp A)
  lam_norm_sq : 0 < lam * ‖A‖ ^ 2 ∧ lam * ‖A‖ ^ 2 < 1
  z_def (k : ℕ) : z k = (1 / lam) • M (x k -
    ERealFunction.scaledProximityOperator G hG ⟨lam, lam_pos⟩
      (x k - lam • A.adjoint (A (x k) - b)))
  aux (k : ℕ) : y k = (1 / (h * (1 + h * gamma))) • (x (k + 1) - x k) -
    (beta / (1 + h * gamma)) • (z (k + 1) - z k) - (h / (1 + h * gamma)) • z (k + 1)
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator Φ hΦ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩ (y k)
```

## Statement explanation
The declaration defines a `structure` named `IPAHDDLasso`. It is not a theorem; rather, it packages the data and equations that describe one run of an algorithm. The structure is parameterized by a complete real inner product space $H$, functions

$$
\Phi, G : H \to \{r : \mathrm{EReal} \mid \bot < r\},
$$

proofs $h_\Phi : \Phi \in \Gamma_0(H)$ and $h_G : G \in \Gamma_0(H)$, continuous linear operators $A, M : H \to H$, a vector $b \in H$, and real parameters $\lambda, h, \gamma, \beta \in \mathbb R$. The typeclass assumptions make $H$ a real Hilbert space, so adjoints and proximal operators are available.

The fields of the structure impose the following requirements on any inhabitant of the type.

- Positivity: $h>0$, $\gamma>0$, and $\lambda>0$. There is no positivity assumption on $\beta$.
- Sequences: $x, y, z : \mathbb N \to H$.
- Initial vectors: vectors $x_0, x_1 \in H$, recorded by the fields `initial0` and `initial1`, together with the equations $x_0 = \text{initial0}$ and $x_1 = \text{initial1}$.
- Metric operator: $M = I - \lambda A^* A$, where $I$ is the identity operator on $H$, $A^*$ is the adjoint of $A$, and $A^*A$ means $A^* \circ A$.
- Norm condition: $0 < \lambda \|A\|^2 < 1$, where $\|A\|$ is the operator norm of $A$.
- Definition of $z$: for every $k \in \mathbb N$,

$$
z_k = \frac{1}{\lambda} M\left(x_k - \mathrm{prox}_{\lambda G}\left(x_k - \lambda A^*(A x_k - b)\right)\right).
$$

Here $\mathrm{prox}_{\lambda G}$ denotes the scaled proximal operator of $G$ with scale $\lambda$, namely the Lean expression `ERealFunction.scaledProximityOperator G hG ⟨lam, lam_pos⟩`.
- Definition of $y$: for every $k \in \mathbb N$,

$$
y_k = \frac{1}{h(1+h\gamma)}(x_{k+1}-x_k)
      -\frac{\beta}{1+h\gamma}(z_{k+1}-z_k)
      -\frac{h}{1+h\gamma}z_{k+1}.
$$

- Update for $x$: for every $k \in \mathbb N$,

$$
x_{k+2} = x_{k+1} + h\,\mathrm{prox}_{\frac{h}{1+h\gamma}\Phi}(y_k),
$$

where $\mathrm{prox}_{\frac{h}{1+h\gamma}\Phi}$ is the scaled proximal operator of $\Phi$ with scale $h/(1+h\gamma)$.

Thus the structure says: a valid `IPAHDDLasso` run consists of two initial points, three sequences, positive step/damping parameters $h,\gamma,\lambda$, the operator identity $M=I-\lambda A^*A$, the smallness condition $\lambda\|A\|^2<1$, and the pointwise recurrences above. It does not assert existence of such a run, nor convergence, nor any algorithmic theorem.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so its fields are not proved by the Lean code; they are the data and equations that an inhabitant must supply. The only actual proof term inside the declaration is the inline proof in the `update` field that the scale $h/(1+h\gamma)$ is positive.

That inline proof appears because `ERealFunction.scaledProximityOperator` expects its scaling argument to be a positive real packaged with a proof of positivity. In the `update` field the scale is $h/(1+h\gamma)$, so Lean must verify

$$
0 < \frac{h}{1+h\gamma}.
$$

The proof proceeds as follows.

First, `have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]` introduces a local proof named `hden`. The lemma `mul_pos` is applied to `h_pos`, which says $0<h$, and `gamma_pos`, which says $0<\gamma$, giving $0<h\gamma$. The tactic `nlinarith` is a nonlinear arithmetic tactic; using the fact $0<h\gamma$, it proves the goal $0<1+h\gamma$. This is valid because $h\gamma>0$, hence $1+h\gamma>1>0$.

Next, `exact div_pos h_pos hden` uses the lemma `div_pos`, which states that if the numerator and denominator are positive, then their quotient is positive. Here the numerator is $h$, positive by `h_pos`, and the denominator is $1+h\gamma$, positive by `hden`. Therefore `div_pos` proves

$$
0 < \frac{h}{1+h\gamma}.
$$

This proof is needed only to satisfy the positivity side condition of the scaled proximal operator. It does not prove any property of the algorithm itself.

No `intro`, `rw`, or `simp` commands occur in this declaration. The equations `init0`, `init1`, `metric`, `z_def`, `aux`, and `update` are fields, so they are required equalities rather than derived conclusions. The inequalities `h_pos`, `gamma_pos`, `lam_pos`, and `lam_norm_sq` are likewise required fields, not results proved by the structure.

