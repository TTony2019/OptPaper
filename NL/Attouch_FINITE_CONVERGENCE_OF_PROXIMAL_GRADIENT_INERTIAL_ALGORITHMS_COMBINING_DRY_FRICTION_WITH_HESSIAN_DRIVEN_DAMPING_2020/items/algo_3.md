## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_3.lean`

## Lean statement
```lean
structure IPAHDDVar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (h gamma beta : ℝ) where
  h_pos : 0 < h
  x : ℕ → H
  initial0 : H
  initial1 : H
  init0 : x 0 = initial0
  init1 : x 1 = initial1
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ ⟨h, h_pos⟩
    (((1 - h * gamma) / h) • (x (k + 1) - x k) -
      beta • (gradient f (x (k + 1)) - gradient f (x k)) - h • gradient f (x (k + 1)))
```

## Statement explanation
The declaration introduces a structure named `IPAHDDVar`. It is a type of data for a discrete inertial proximal-gradient algorithm with Hessian-driven damping. The ambient space $H$ is a complete real inner product space: the assumptions `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H` make $H$ a real Hilbert space. The parameters are:

- $f : H \to \mathbb{R}$, the real-valued smooth part of the objective;
- $\phi : H \to \{ y : \overline{\mathbb R} \mid \bot < y \}$, an extended-real-valued function whose values lie strictly above the bottom element $\bot$ of the extended real type `EReal`. Thus $\phi$ never takes the bottom value, which in the extended-real order is the $-\infty$ end;
- `hφ`, a hypothesis that $\phi$ belongs to the class denoted $\Gamma_0(H)$. The declaration itself does not unfold $\Gamma_0(H)$; it uses this membership proof as an admissibility argument for the scaled proximity operator;
- $h, \gamma, \beta \in \mathbb{R}$, real algorithm parameters.

A term of `IPAHDDVar f φ hφ h gamma beta` consists of the following fields:

- `h_pos : 0 < h`, a proof that the step size $h$ is positive;
- `x : ℕ → H`, a sequence of iterates $x_k$;
- `initial0 : H` and `initial1 : H`, two initial vectors;
- `init0 : x 0 = initial0`, the assertion that the zeroth iterate is `initial0`;
- `init1 : x 1 = initial1`, the assertion that the first iterate is `initial1`;
- `update (k : ℕ)`, for every natural number $k$, a proof of the recurrence equation

  $$
  x_{k+2}
  =
  x_{k+1}
  + h\,P_{\phi,h}\!\left(
      \frac{1-h\gamma}{h}(x_{k+1}-x_k)
      - \beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
      - h\nabla f(x_{k+1})
    \right).
  $$

Here $P_{\phi,h}$ denotes the map obtained from `ERealFunction.scaledProximityOperator φ hφ ⟨h, h_pos⟩`, i.e. the scaled proximity operator associated to $\phi$ with scaling $h$, carrying the proof that $h>0$. The notation $\nabla f$ stands for the Lean gradient operator `gradient f`; the structure itself adds no separate differentiability hypothesis on $f$. The expression $\langle h,h_{\rm pos}\rangle$ packages the real number $h$ together with the proof that it is positive.

Mathematically, the declaration says that an `IPAHDDVar` is exactly a second-order discrete trajectory $x_0,x_1,x_2,\dots$ in $H$, together with named initial points and proofs that the first two terms are those points, satisfying the displayed recurrence for every $k\in\mathbb N$. The recurrence combines an inertial difference $x_{k+1}-x_k$, a damping term built from the finite difference of gradients $\nabla f(x_{k+1})-\nabla f(x_k)$, and a forward gradient step $-h\nabla f(x_{k+1})$, all passed through the scaled proximity operator of $\phi$, then scaled by $h$ and added to $x_{k+1}$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part: the Lean source contains only the structure declaration, with the comment that there is no proof. Accordingly, no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or local lemma is invoked. The mathematical content of the declaration is therefore entirely contained in its parameters and fields.

The parameter $H$ is fixed as a complete real inner product space. This supplies the Hilbert-space structure needed to speak about the gradient vector of a real-valued function and about proximal operations on $H$.

The function $f : H \to \mathbb{R}$ provides the smooth part of the objective. The expression $\nabla f(x_{k+1})$ is the gradient vector `gradient f (x (k+1))`, and similarly for $x_k$. The recurrence uses their difference $\nabla f(x_{k+1})-\nabla f(x_k)$, which is the discrete analogue of a second-order damping term.

The function $\phi$ is the nonsmooth extended-real-valued part. Its codomain is the subtype of extended real numbers strictly greater than $\bot$, so $\phi(x)$ is always above the bottom element. The hypothesis `hφ` records that $\phi$ belongs to $\Gamma_0(H)$. The declaration does not unfold this class; its visible role is to provide the required membership proof when forming the scaled proximity operator.

The real parameters $h,\gamma,\beta$ enter the recurrence as coefficients. The field `h_pos` is the only sign or positivity assumption in the structure: it proves $0<h$. This positivity is mathematically necessary for the coefficient $(1-h\gamma)/h$ to be defined and for the scaled proximity operator to be called with the positive-step witness $\langle h,h_{\rm pos}\rangle$.

The field `x : ℕ → H` is the discrete sequence of iterates. The fields `initial0` and `initial1` are two vectors in $H$, and the fields `init0` and `init1` assert that $x_0=\text{initial0}$ and $x_1=\text{initial1}$. Thus the sequence is a second-order recurrence with two prescribed initial terms.

For each $k\in\mathbb N$, the field `update k` asserts the equality defining $x_{k+2}$. The vector inside the scaled proximity operator is

$$
\frac{1-h\gamma}{h}(x_{k+1}-x_k)
- \beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
- h\nabla f(x_{k+1}).
$$

The first term is an inertial/momentum contribution involving $x_{k+1}-x_k$. The second is a Hessian-driven damping contribution formed from the difference of gradients. The third is a gradient-descent step at $x_{k+1}$. The scaled proximity operator of $\phi$, with step $h$, is applied to this combined vector. The result is multiplied by $h$ and added to $x_{k+1}$ to produce $x_{k+2}$.

Since the equation is required for every natural number $k$, the field `update` defines all later iterates recursively from the two initial values: $x_2$ from $x_1$ and $x_0$, then $x_3$ from $x_2$ and $x_1$, and so on. The declaration does not assert convergence, existence, or uniqueness of such a sequence; it only packages the data and equations that a sequence satisfying this IPA-HDD recurrence must satisfy.

