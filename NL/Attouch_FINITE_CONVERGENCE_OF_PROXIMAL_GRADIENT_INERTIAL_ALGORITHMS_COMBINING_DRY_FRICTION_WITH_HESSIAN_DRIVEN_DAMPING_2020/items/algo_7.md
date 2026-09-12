## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/algo_7.lean`

## Lean statement
```lean
structure IPAHDDNonsmooth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (h gamma beta lam : ℝ) where
  h_pos : 0 < h
  gamma_pos : 0 < gamma
  lam_pos : 0 < lam
  x : ℕ → H
  y : ℕ → H
  x0 : x 0 = x 0
  x1 : x 1 = x 1
  aux (k : ℕ) : y k = (1 / (1 + h * gamma)) •
    (((lam - beta * h) / (lam * h)) • (x (k + 1) - x k) +
      (beta / lam) • (ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ (x (k + 1)) -
        ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ (x k)) -
      (h / lam) • (x (k + 1) -
        ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ (x (k + 1))))
  update (k : ℕ) : x (k + 2) = x (k + 1) + h •
    ERealFunction.scaledProximityOperator φ hφ
      ⟨h / (1 + h * gamma), by
        have hden : 0 < 1 + h * gamma := by nlinarith [mul_pos h_pos gamma_pos]
        exact div_pos h_pos hden⟩ (y k)
```

## Statement explanation
The declaration introduces a structure named `IPAHDDNonsmooth`. It is not a theorem with a conclusion; it packages data and equations describing one kind of inertial proximal-gradient algorithm. The ambient object is a type \(H\) equipped with the assumptions that make it a complete real inner product space. The parameters are two functions
\[
f,\varphi : H \to \{r : \mathrm{EReal} \mid \bot < r\},
\]
so their values are extended-real numbers strictly above the bottom element \(\bot\) of \(\mathrm{EReal}\), together with proofs \(f\in\Gamma_0(H)\) and \(\varphi\in\Gamma_0(H)\). The statement does not expand the definition of \(\Gamma_0(H)\); it only records membership in that class. The real parameters are \(h,\gamma,\beta,\lambda\), written in Lean as `h`, `gamma`, `beta`, and `lam`.

The fields of the structure are:

- `h_pos : 0 < h`, `gamma_pos : 0 < gamma`, and `lam_pos : 0 < lam`. Thus \(h\), \(\gamma\), and \(\lambda\) are required to be positive. There is no corresponding positivity assumption on \(\beta\).
- `x : ℕ → H` and `y : ℕ → H`, so \(x\) and \(y\) are sequences in \(H\), indexed by natural numbers.
- `x0 : x 0 = x 0` and `x1 : x 1 = x 1`. These are tautological equalities. They impose no initial condition on \(x_0\) or \(x_1\); they would be satisfied by reflexivity for any sequence \(x\).
- `aux (k : ℕ)`, which for every \(k\in\mathbb N\) asserts
\[
y_k =
\frac{1}{1+h\gamma}
\left(
\frac{\lambda-\beta h}{\lambda h}(x_{k+1}-x_k)
+\frac{\beta}{\lambda}\bigl(P_{\lambda,f}(x_{k+1})-P_{\lambda,f}(x_k)\bigr)
-\frac{h}{\lambda}\bigl(x_{k+1}-P_{\lambda,f}(x_{k+1})\bigr)
\right).
\]
Here \(P_{\lambda,f}(z)\) abbreviates the term
`ERealFunction.scaledProximityOperator f hf ⟨lam, lam_pos⟩ z`,
namely the scaled proximity operator of \(f\) applied with the positive scale \(\lambda\). The exact definition of that operator is not expanded in the statement; only its use with \(f\), the proof \(hf\), the positive scale \(\lambda\), and a point \(z\) is visible.
- `update (k : ℕ)`, which for every \(k\in\mathbb N\) asserts
\[
x_{k+2}=x_{k+1}+h\,P_{\frac{h}{1+h\gamma},\varphi}(y_k),
\]
where \(P_{\frac{h}{1+h\gamma},\varphi}\) abbreviates
`ERealFunction.scaledProximityOperator φ hφ ⟨h / (1 + h * gamma), ...⟩`.
Thus the next iterate \(x_{k+2}\) is obtained from \(x_{k+1}\) by adding \(h\) times the scaled proximity operator of \(\varphi\), evaluated at \(y_k\), with scale \(h/(1+h\gamma)\).

Mathematically, a term of this structure is a bundle consisting of the functions \(f\) and \(\varphi\), their membership proofs in \(\Gamma_0(H)\), the real parameters, the sequences \(x\) and \(y\), and pointwise proofs that the two recurrence equations hold for all \(k\in\mathbb N\). The structure therefore specifies an algorithm instance satisfying those recurrences. It does not assert existence of such sequences, nor convergence, nor any property of the initial values; the fields `x0` and `x1` are vacuous equalities.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a structure, so it has no theorem body and no sequence of tactic steps to explain. The only embedded proof term is inside the `update` field: the scaled proximity operator of \(\varphi\) expects a positive scale, and the scale used is
\[
\frac{h}{1+h\gamma}.
\]
The source proves this is positive by introducing a local proof
`hden : 0 < 1 + h * gamma`
using `nlinarith [mul_pos h_pos gamma_pos]`. The expression `mul_pos h_pos gamma_pos` is the fact that a product of positive real numbers is positive, so it gives \(0<h\gamma\). From that, `nlinarith` derives \(0<1+h\gamma\). Then the command `exact div_pos h_pos hden` applies the lemma that a quotient of positive real numbers is positive, with numerator \(h\) and denominator \(1+h\gamma\), to conclude
\[
0<\frac{h}{1+h\gamma}.
\]
That positivity proof is exactly what is needed to build the subtype element \(\langle h/(1+h\gamma),\ldots\rangle\) passed as the scale argument to `ERealFunction.scaledProximityOperator`. It does not add any mathematical assumption beyond the already present facts \(0<h\) and \(0<\gamma\). No separate use of `intro`, `rw`, `simp`, `linarith`, or any named local theorem occurs, and no named local result is cited.

