## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/ext_def_1.lean`

## Lean statement
```lean
noncomputable def dissipativeEnergy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H} {u0 v0 : H}
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) (t : Set.Ici (0 : ℝ)) : ℝ :=
  (1 / 2 : ℝ) * ‖fderiv ℝ sys.u (t : ℝ) 1‖ ^ 2 + Phi (sys.u (t : ℝ))
```

## Statement explanation
The declaration introduces a `noncomputable def` named `dissipativeEnergy`. Its ambient context is a type \(H\) equipped with a normed additive commutative group structure, a real inner product space structure, and completeness; thus \(H\) is a complete real inner product space, i.e. a real Hilbert space. Besides \(H\), there are parameters \(\gamma \in \mathbb{R}\), a potential \(\Phi : H \to \mathbb{R}\), a gradient field \(\operatorname{gradPhi} : H \to H\), and initial data \(u_0, v_0 \in H\). These are the data used to form a system `sys` of type `DissipativeSystem gamma Phi gradPhi u0 v0`.

In the body, `sys.u` is the trajectory component of the system. The definition applies it to a real time and then applies \(\Phi\), so in this declaration it is used as a curve \(\operatorname{sys.u} : \mathbb{R} \to H\). The argument \(t\) has type `Set.Ici (0 : ℝ)`, meaning it is a real number together with the condition \(0 \le t\); the coercion `(t : ℝ)` extracts its underlying real time. For this system and nonnegative time \(t\), the declared value is

\[
\operatorname{dissipativeEnergy}(\mathrm{sys},t)
=
\frac{1}{2}
\left\|
\operatorname{fderiv}_{\mathbb{R}}(\mathrm{sys.u})(t)(1)
\right\|^2
+
\Phi\bigl(\mathrm{sys.u}(t)\bigr).
\]

Here \(\operatorname{fderiv}_{\mathbb{R}}(\mathrm{sys.u})(t)\) is the Fréchet derivative of the curve \(\mathrm{sys.u}\) at time \(t\), a continuous linear map \(\mathbb{R} \to H\). Applying it to the scalar \(1\) gives the velocity vector of the trajectory at that time. Thus the first term is one half the squared norm of that velocity, and the second term is the potential \(\Phi\) evaluated at the position at time \(t\). The definition therefore assigns to each dissipative system and each nonnegative time the real number consisting of one half the squared speed plus the potential energy at the current position. The parameters \(\gamma\), `gradPhi`, \(u_0\), and \(v_0\) enter only through the system `sys`; they are not used explicitly in the displayed formula.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a definition, not a theorem, so its content is exactly the right-hand side displayed above. There are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named local result is cited.

The only Lean-specific processing is elaboration of the defining term. The projection `sys.u` selects the trajectory field of the dissipative system. The coercion `(t : ℝ)` changes the element \(t\) of the subtype \(\{s : \mathbb{R} \mid 0 \le s\}\) into its underlying real time. The expression `fderiv ℝ sys.u (t : ℝ)` forms the Fréchet derivative of that trajectory at \(t\), and applying it to \(1\) evaluates the derivative in the scalar direction \(1\). The norm squared of that derivative is multiplied by the real number \(\frac{1}{2}\), and then the value \(\Phi(\mathrm{sys.u}(t))\) is added. The resulting real number is returned as the value of `dissipativeEnergy sys t`. The marker `noncomputable` records that this definition uses noncomputable real-analytic data such as norms and Fréchet derivatives, but it imposes no additional mathematical hypothesis and requires no proof.

