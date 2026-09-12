## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_5.lean`

## Lean statement
```lean
structure IPAHDDN {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (h gamma beta : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  extrapolate (k : ℕ) : y k = x (k + 1) + (1 / (1 + h * gamma)) • (x (k + 1) - x k)
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩
    ((1 / h) • (y k - x (k + 1)) - (beta / (1 + h * gamma)) •
      (gradient f (x (k + 1)) - gradient f (x k)) - (h / (1 + h * gamma)) • gradient f (y k))
```

## Statement explanation
The declaration `IPAHDDN` is a structure, i.e. a record type, rather than a theorem. It is parameterized by a type `H` equipped with the typeclass assumptions `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H`, so $H$ is a complete real inner product space, i.e. a real Hilbert space. It also takes a function $f : H \to \mathbb{R}$, a function $\phi : H \to \overline{\mathbb{R}}$ whose codomain is the subtype `Set.Ioi (⊥ : EReal)` of extended real numbers strictly greater than $\bot = -\infty$, a proof $hφ : \phi \in \Gamma_0(H)$, and real parameters $h,\gamma,\beta$. The condition $\phi \in \Gamma_0(H)$ is the usual convex-analytic regularity assumption that $\phi$ is a proper, convex, lower semicontinuous extended-real-valued function; the subtype codomain already excludes the value $-\infty$.

An element of `IPAHDDN f φ hφ h gamma beta` consists of proofs $0\lt h$ and $0\lt \gamma$, two sequences $x,y : \mathbb{N} \to H$, two vacuous equality proofs $x(0)=x(0)$ and $x(1)=x(1)$, and, for every $k \in \mathbb{N}$, proofs of the following two equations. First, the extrapolation equation is

$$
y_k = x_{k+1} + \frac{1}{1+h\gamma}(x_{k+1}-x_k).
$$

Second, the update equation is

```math
x_{k+2} = x_{k+1} + h\, \mathrm{prox}_{\frac{h}{1+h\gamma}\phi}\left(
\frac{1}{h}(y_k-x_{k+1})
-\frac{\beta}{1+h\gamma}\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
-\frac{h}{1+h\gamma}\nabla f(y_k)
\right),
```

where $\nabla f$ denotes Lean's `gradient f`, and the scaled proximity operator is the formal object `ERealFunction.scaledProximityOperator φ hφ` evaluated at the positive scale $h/(1+h\gamma)$. The scale is positive because $h\gt 0$ and $\gamma\gt 0$, which imply $1+h\gamma\gt 0$. Mathematically, the structure specifies a discrete inertial proximal-gradient algorithm with Hessian-driven damping: $y_k$ is an extrapolated point, and $x_{k+2}$ is obtained from $x_{k+1}$ by adding $h$ times a scaled proximal step applied to a vector combining a momentum-like term $\frac{1}{h}(y_k-x_{k+1})$, a Hessian-driven damping term $-\frac{\beta}{1+h\gamma}(\nabla f(x_{k+1})-\nabla f(x_k))$, and a gradient term $-\frac{h}{1+h\gamma}\nabla f(y_k)$. The fields `x0` and `x1` are named as if they were initial conditions, but their types are the tautologies $x(0)=x(0)$ and $x(1)=x(1)$, so they impose no restriction and do not fix initial values. The structure does not assert existence, uniqueness, convergence, or finite convergence of the sequences, and it does not assume differentiability or convexity of $f$; the only regularity hypothesis on the nonsmooth part is $hφ : \phi \in \Gamma_0(H)$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. It is a `structure`, so there is no theorem to prove; the only proof terms are the fields requiring proofs and the inline proof of positivity inside the `update` field.

The fields `h_pos` and `gamma_pos` require any element of the structure to contain proofs of $0\lt h$ and $0\lt \gamma$. The fields `x` and `y` are data fields giving the two sequences. The fields `x0` and `x1` are proof fields for $x(0)=x(0)$ and $x(1)=x(1)$; these are true by reflexivity and do not constrain the algorithm. The fields `extrapolate` and `update` are not proved in the surrounding code: they are field types stating that the corresponding equations hold for every $k \in \mathbb{N}$. Thus the mathematical content of the declaration is exactly the two recurrence equations, together with the positivity assumptions on $h$ and $\gamma$.

The only nontrivial proof term appears inside the `update` field, where the positive scale for the scaled proximity operator is supplied as the subtype element

$$
\left\langle \frac{h}{1+h\gamma},\ \text{proof that } \frac{h}{1+h\gamma}>0 \right\rangle.
$$

The proof begins with
`have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]`.
Here `mul_pos h_pos gamma_pos` is the lemma that a product of two positive real numbers is positive, so it gives $0\lt h\gamma$. The tactic `nlinarith` then uses that fact to prove $0\lt 1+h\gamma$. Next, the command
`exact div_pos h_pos hden`
applies the lemma `div_pos`, which states that a quotient of two positive real numbers is positive. With $0\lt h$ and $0\lt 1+h\gamma$, it produces $0\lt h/(1+h\gamma)$, exactly the positivity condition required by the subtype argument. The `have` command introduces the intermediate fact $0\lt 1+h\gamma$, and `exact` closes the goal using `div_pos`. No `intro`, `rw`, or `simp` occurs in the supplied proof part; the quantification over $k$ is already present in the field types, so no explicit introduction of $k$ is needed in the displayed code. The scaled proximity operator is then applied with this positive scale to the vector in $H$ displayed in the update equation, and the result is multiplied by $h$ and added to $x_{k+1}$.

