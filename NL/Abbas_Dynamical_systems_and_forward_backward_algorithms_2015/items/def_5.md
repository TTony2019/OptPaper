## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/def_5.lean`

## Lean statement
```lean
structure ProximalGradientDynamics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) where
  mu_pos : 0 < mu
  x : ℝ → H
  differential_equation : ∀ t,
    deriv x t + x t - ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, mu_pos⟩
      (x t - mu • B (x t)) = 0
```

## Statement explanation
The declaration `ProximalGradientDynamics` is a structure. Its ambient space is a type \(H\) equipped with a normed abelian group structure, a real inner product, and completeness; together these make \(H\) a complete real inner product space, i.e. a real Hilbert space. The symbol `EReal` denotes the extended real numbers. The function \(\Phi\) sends each point \(x\in H\) to an extended real value strictly greater than the bottom element \(\bot\) of `EReal`; the Lean type `Set.Ioi (⊥ : EReal)` is exactly the subtype of extended reals satisfying that strict inequality. The hypothesis \(hPhi\) says that \(\Phi\) belongs to the class `ERealFunction.gammaZero H`. The supplied source does not define that class, so its internal conditions are not expanded here; its visible role is to certify that \(\Phi\) is admissible for the scaled proximity operator.

The parameter \(B:H\to H\) is an operator on \(H\), and \(\mu\) is a real parameter. A term of the structure `ProximalGradientDynamics Phi hPhi B mu` packages three things: a proof that \(\mu>0\); a trajectory \(x:\mathbb R\to H\); and a proof that for every real number \(t\), the following equality in \(H\) holds:
\[
\operatorname{deriv}x(t)+x(t)
-\operatorname{scaledProx}_{\mu,\Phi}\!\left(x(t)-\mu B(x(t))\right)=0.
\]
Here \(\operatorname{scaledProx}_{\mu,\Phi}\) denotes the value of `ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, mu_pos⟩` as an operator on \(H\). The component `⟨mu, mu_pos⟩` packages the real number \(\mu\) together with the proof that it is positive; this is passed as the positive scale to the scaled proximity operator. The term \(x(t)-\mu B(x(t))\) is the point at which that scaled proximity operator is evaluated.

Equivalently, the field `differential_equation` says that for every \(t\in\mathbb R\),
\[
\operatorname{deriv}x(t)
=
\operatorname{scaledProx}_{\mu,\Phi}\!\left(x(t)-\mu B(x(t))\right)-x(t).
\]
Thus the declaration describes a continuous-time trajectory whose velocity at time \(t\) is the difference between the scaled proximal step applied to \(x(t)-\mu B(x(t))\) and the current point \(x(t)\). The same positive parameter \(\mu\) appears both as the coefficient of \(B(x(t))\) and as the scale in the proximity operator. The structure does not by itself assert that such a trajectory exists or is unique; it defines the type of data consisting of a positive \(\mu\), a trajectory \(x\), and a proof that the trajectory satisfies the displayed differential equation.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `structure`, so the text after `where` lists fields rather than proving a theorem. The line `-- No separate proof part.` confirms that no proof body is supplied. Consequently there are no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorem or lemma is invoked.

The mathematical content is entirely contained in the fields. The field `mu_pos` records the hypothesis \(0<\mu\). The field `x` records the trajectory from \(\mathbb R\) to \(H\). The field `differential_equation` records the universal statement that for every \(t\in\mathbb R\), the equality
\[
\operatorname{deriv}x(t)+x(t)
-\operatorname{scaledProx}_{\mu,\Phi}\!\left(x(t)-\mu B(x(t))\right)=0
\]
holds. The proof `mu_pos` is also used as the positivity certificate inside the subtype element `⟨mu, mu_pos⟩` supplied to the scaled proximity operator, ensuring that the scale is positive. A term of the structure can therefore be built only by providing these three components.

