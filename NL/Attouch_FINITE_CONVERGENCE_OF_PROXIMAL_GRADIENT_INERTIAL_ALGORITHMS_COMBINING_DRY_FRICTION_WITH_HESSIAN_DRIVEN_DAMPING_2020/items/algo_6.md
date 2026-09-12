## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_6.lean`

## Lean statement
```lean
structure IPAHDDNVar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (h gamma beta : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  extrapolate (k : ℕ) : y k = x (k + 1) + (1 / (h * (1 + h * gamma))) • (x (k + 1) - x k)
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩
    (y k - x (k + 1) - (beta / (1 + h * gamma)) •
      (gradient f (x (k + 1)) - gradient f (x k)) - (h / (1 + h * gamma)) • gradient f (y k))
```

## Statement explanation
The declaration introduces the structure `IPAHDDNVar`. It is not a theorem but a record type packaging the data and consistency equations for a trajectory of an inertial proximal-gradient algorithm.

The parameters of the structure are:

- A type $H$ equipped with the typeclass assumptions `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H`; together these say that $H$ is a complete real inner product space, i.e. a real Hilbert space.
- A finite-valued objective function $f:H\to\mathbb R$.
- A function $\phi:H\to\overline{\mathbb R}$ whose values are required to lie in the subtype `Set.Ioi (⊥ : EReal)`. Here $\overline{\mathbb R}$ denotes the extended reals, $\bot$ is their bottom element $-\infty$, and `Set.Ioi (⊥ : EReal)` is the type of extended reals strictly greater than $\bot$, so $\phi$ never takes the value $-\infty$.
- A proof $h_\phi$ that $\phi\in\Gamma_0(H)$. In this context $\Gamma_0(H)$ is the class of proper lower semicontinuous convex extended-real-valued functions on $H$. Thus the membership hypothesis records the convexity, lower semicontinuity, and properness assumptions on $\phi$.
- Real parameters $h,\gamma,\beta\in\mathbb R$. The declaration itself imposes no sign condition on $\beta$; positivity conditions are required only for $h$ and $\gamma$.

A term of type `IPAHDDNVar f φ hφ h γ β` consists of the following fields:

- A proof $0\lt h$.
- A proof $0\lt \gamma$.
- Two sequences $x:\mathbb N\to H$ and $y:\mathbb N\to H$. Write $x_k=x(k)$ and $y_k=y(k)$.
- Two vacuous equality fields $x_0=x_0$ and $x_1=x_1$. These are self-equalities; up to proof irrelevance they impose no mathematical condition on the initial terms.
- For every $k\in\mathbb N$, an extrapolation equation

$$
y_k=x_{k+1}+\frac{1}{h(1+h\gamma)}(x_{k+1}-x_k).
$$

This defines the auxiliary sequence $y$ as an inertial extrapolation from two consecutive iterates of $x$.
- For every $k\in\mathbb N$, an update equation

```math
x_{k+2}=x_{k+1}+h\,G_{\frac{h}{1+h\gamma}\phi}\!\left(
y_k-x_{k+1}
-\frac{\beta}{1+h\gamma}\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
-\frac{h}{1+h\gamma}\nabla f(y_k)
\right),
```

where $G_{s\phi}$ denotes the scaled proximity operator `ERealFunction.scaledProximityOperator φ hφ ⟨s, s>0⟩` at the positive scale

$$
s=\frac{h}{1+h\gamma}.
$$

In the standard convex-analytic normalization, the scaled proximity operator is related to the proximal map by

$$
G_{s\phi}(z)=\frac{z-\mathrm{prox}_{s\phi}(z)}{s},
$$

where

$$
\mathrm{prox}_{s\phi}(z)=\arg\min_{u\in H}\left(\phi(u)+\frac{1}{2s}\lVert u-z\rVert^2\right).
$$

The terms $\nabla f(x_k)$, $\nabla f(x_{k+1})$, and $\nabla f(y_k)$ are the gradient vectors produced by Mathlib's `gradient f`; the structure does not separately assume that $f$ is differentiable.

Thus the declaration says: given a real Hilbert space $H$, a finite objective $f$, a proper lower semicontinuous convex extended-real function $\phi$, and real parameters $h,\gamma,\beta$ with $h\gt 0$ and $\gamma\gt 0$, the sequences $x$ and $y$ form an admissible trajectory of an inertial proximal-gradient algorithm. The sequence $y$ is obtained by an inertial extrapolation from $x_k$ and $x_{k+1}$, and $x_{k+2}$ is obtained from $x_{k+1}$ by adding $h$ times a scaled proximal step evaluated at a vector built from $y_k$, $x_{k+1}$, and the gradient differences appearing in the update.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so it introduces a record type and its fields; it does not prove a theorem. The mathematical content is entirely contained in the required fields of the structure.

The fields `h_pos` and `gamma_pos` are not derived in the source; they are components that any record of this structure must supply. Mathematically they are the assumptions $0\lt h$ and $0\lt \gamma$. The fields `x0` and `x1` have types $x_0=x_0$ and $x_1=x_1$. Such equalities are true by reflexivity and therefore add no restriction beyond the existence of a proof of a self-equality.

The fields `extrapolate` and `update` are equality requirements, one for each natural number $k$. They are not proved by tactics in the declaration; rather, they define the algorithm equations that a record must satisfy. The `extrapolate` field states that for every $k$,

$$
y_k=x_{k+1}+\frac{1}{h(1+h\gamma)}(x_{k+1}-x_k).
$$

The `update` field states that for every $k$,

```math
x_{k+2}=x_{k+1}+h\,G_{\frac{h}{1+h\gamma}\phi}(z_k),
```

where

$$
z_k=
y_k-x_{k+1}
-\frac{\beta}{1+h\gamma}\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
-\frac{h}{1+h\gamma}\nabla f(y_k).
$$

The only proof script embedded in the declaration occurs inside the `update` field, where the positivity of the scale

$$
s=\frac{h}{1+h\gamma}
$$

must be supplied to `ERealFunction.scaledProximityOperator`. The term

$$
\left\langle \frac{h}{1+h\gamma},\text{proof}\right\rangle
$$

is an element of the subtype of positive real numbers. The proof proceeds as follows.

First, the command `mul_pos h_pos gamma_pos` uses the theorem that the product of two positive real numbers is positive. Since the fields give $h\gt 0$ and $\gamma\gt 0$, this establishes

$$
h\gamma>0.
$$

Next, the tactic `nlinarith [mul_pos h_pos gamma_pos]` uses that inequality to prove

$$
0<1+h\gamma.
$$

Indeed, from $h\gamma\gt 0$ one gets $1+h\gamma\gt 1$, hence $1+h\gamma\gt 0$. The result is named `hden`.

Finally, `exact div_pos h_pos hden` applies the theorem that a quotient of positive real numbers is positive. With numerator $h\gt 0$ and denominator $1+h\gamma\gt 0$, it proves

$$
0<\frac{h}{1+h\gamma}.
$$

This completes the subtype proof and allows the positive scale $s=h/(1+h\gamma)$ to be passed to the scaled proximity operator.

The role of `ERealFunction.scaledProximityOperator` in the update is therefore to apply the scaled proximal map of $\phi$ at the positive scale $s=h/(1+h\gamma)$ to the vector $z_k$. The update equation then says that $x_{k+2}$ is obtained from $x_{k+1}$ by adding $h$ times this scaled proximal quantity. The `gradient f` terms supply the gradient differences and the gradient at $y_k$ used in the vector $z_k$; no additional differentiability assumption is present in this structure declaration. Apart from the positivity proof described above, no named local result or separate proof is invoked in this declaration.

