## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_4.lean`

## Lean statement
```lean
structure IPAHDDPert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (e : ℕ → H) (h gamma beta : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  aux (k : ℕ) : y k = (1 / (h * (1 + h * gamma))) • (x (k + 1) - x k) -
    (beta / (1 + h * gamma)) • (gradient f (x (k + 1)) - gradient f (x k)) -
    (h / (1 + h * gamma)) • gradient f (x (k + 1)) + (h / (1 + h * gamma)) • e k
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩ (y k)
```

## Statement explanation
The declaration introduces a record type `IPAHDDPert`. Its parameters are: a type $H$ equipped with `NormedAddCommGroup`, `InnerProductSpace ℝ`, and `CompleteSpace`, so $H$ is a real Hilbert space; a scalar function $f : H \to \mathbb R$; an extended-real function $\phi : H \to \{\xi \in \mathrm{EReal} : \bot < \xi\}$, meaning that each value $\phi(x)$ is an extended real strictly above bottom; a proof $h_\phi$ that $\phi \in \Gamma_0(H)$; a perturbation sequence $e : \mathbb N \to H$; and real parameters $h,\gamma,\beta$. An element of the structure contains the positivity assumptions $0<h$ and $0<\gamma$, two sequences $x,y:\mathbb N\to H$, two vacuous fields $x_0=x_0$ and $x_1=x_1$, and the following two families of identities for every $k\in\mathbb N$. The auxiliary relation is

$$
y_k=\frac{1}{h(1+h\gamma)}(x_{k+1}-x_k)
-\frac{\beta}{1+h\gamma}\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
-\frac{h}{1+h\gamma}\nabla f(x_{k+1})
+\frac{h}{1+h\gamma}e_k .
$$

The update relation is

$$
x_{k+2}=x_{k+1}+h\cdot
\mathcal P_{\phi,h_\phi}\!\left(\frac{h}{1+h\gamma}\right)(y_k),
$$

where $\mathcal P_{\phi,h_\phi}(a)(z)$ denotes the value `ERealFunction.scaledProximityOperator φ hφ a z`, the scaled proximity operator of $\phi$ with scaling $a$, applied to $z$. The scaling $h/(1+h\gamma)$ is passed together with a proof that it is positive. Mathematically, the structure describes a perturbed inertial proximal-gradient algorithm with Hessian-driven damping: $y_k$ is built from the inertial displacement $x_{k+1}-x_k$, the gradient difference $\nabla f(x_{k+1})-\nabla f(x_k)$, the current gradient $\nabla f(x_{k+1})$, and the perturbation $e_k$; then $x_{k+2}$ is obtained from $x_{k+1}$ by adding a scaled proximal step of size $h$ evaluated at $y_k$. The structure does not assert convergence or finite convergence; it only specifies the data and identities that an algorithm instance must satisfy. The proof $h_\phi$ is not a numerical condition but the certificate required by the scaled proximity operator that $\phi$ belongs to the class $\Gamma_0(H)$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so its fields are not conclusions proved from hypotheses; they are the components and required identities of a record. The only nontrivial proof term appears inside the field `update`, where the scaling

$$
a=\frac{h}{1+h\gamma}
$$

must be supplied to `ERealFunction.scaledProximityOperator` as an element of a subtype requiring positivity. The proof proceeds as follows. From the fields `h_pos` and `gamma_pos` we have $0<h$ and $0<\gamma$. The lemma `mul_pos` applied to these gives $0<h\gamma$. Then `nlinarith` uses the fact $0<h\gamma$ to derive $0<1+h\gamma$. Finally `div_pos` applied to $0<h$ and $0<1+h\gamma$ gives $0<h/(1+h\gamma)$. This is exactly the positivity certificate for $a$, and the subtype constructor wraps the value $a$ with this proof. The proof uses `have`, `nlinarith`, and `exact`; it does not use `intro`, `rw`, `simp`, or `linarith`. The fields `x0` and `x1` have types $x_0=x_0$ and $x_1=x_1$, so they are reflexive equalities and impose no mathematical restriction. The fields `aux` and `update` are universal statements over $k\in\mathbb N$; they are not derived from earlier fields but are required equalities that any instance of the structure must satisfy. The field `aux` says that for each $k$, $y_k$ is related to $x_{k+1}$, $x_k$, the gradients of $f$ at those points, and $e_k$ by the displayed formula. The field `update` says that for each $k$, $x_{k+2}$ is obtained from $x_{k+1}$ by the displayed scaled-proximal step. The declaration establishes no convergence property; it only assembles the record.

