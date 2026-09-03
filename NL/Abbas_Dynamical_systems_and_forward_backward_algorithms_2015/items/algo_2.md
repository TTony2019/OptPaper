## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/algo_2.lean`

## Lean statement
```lean
theorem backward_forward_unit_step {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (alg : BackwardForwardDiscretization f hf B mu 1) :
    ∀ k, alg.x (k + 1) =
      ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.x k - mu • B (alg.x k))
```

## Statement explanation
The theorem states a single step of a forward–backward type algorithm with step parameter equal to 1.

Let `H` be a complete real inner product space: the hypotheses give `H` a normed additive commutative group structure, an inner product space over `ℝ`, and completeness. Let `f : H → Set.Ioi (⊥ : EReal)` be a function whose values are extended real numbers strictly greater than the bottom element of the extended real line. Let `hf` be a proof that `f` belongs to the set/class `ERealFunction.gammaZero H`. Let `B : H → H` be an arbitrary map, and let `mu : ℝ` be a real number.

Let `alg` be an object of type `BackwardForwardDiscretization f hf B mu 1`. Here the final argument `1` is the method’s unit step parameter. The expression `alg.x` denotes the main sequence produced by the discretization, indexed by natural numbers; `alg.y` is the auxiliary sequence appearing in the definition/properties of `alg`. The object `alg` also contains a proof `alg.mu_pos` that `mu > 0`.

The conclusion is: for every natural number `k`,
\[
\alg.x(k+1) =
\operatorname{scaledProximityOperator}_{f,hf}(\mu)
\left(\alg.x(k) - \mu\, B(\alg.x(k))\right).
\]
In words, the next iterate `alg.x (k+1)` equals the scaled proximity operator of `f` with step size `mu`, applied to the vector obtained from `alg.x k` by one explicit gradient-like step using `B` with step size `mu`.

## Lean proof
```lean
by
  intro k
  calc
    alg.x (k + 1) = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.y (k + 1)) := alg.prox_step (k + 1)
    _ = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        ((1 - (1 : ℝ)) • alg.y k + (1 : ℝ) • (alg.x k - mu • B (alg.x k))) := by
      rw [alg.equation_step]
    _ = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.x k - mu • B (alg.x k)) := by simp
```

## Proof explanation
The proof begins with `intro k`, fixing an arbitrary natural number `k`. No induction is used; the argument works for every fixed `k`.

The proof is a `calc` chain with three terms.

First, it uses the property
\[
\alg.x(k+1) =
\operatorname{scaledProximityOperator}(f,hf)(\mu)
\bigl(\alg.y(k+1)\bigr)
\]
by applying `alg.prox_step (k+1)`. This says that, in the discretization, the updated point `alg.x(k+1)` is obtained by applying the scaled proximity operator to the auxiliary point `alg.y(k+1)`.

Second, the proof rewrites the occurrence of `alg.y(k+1)` inside the proximity operator, using `rw [alg.equation_step]`. This equation expresses `alg.y(k+1)` in terms of the previous auxiliary point `alg.y k` and the explicit step direction. Because the step parameter is `1`, the rewritten expression is
\[
(1 - (1 : \mathbb{R})) \bullet \alg.y k
+
(1 : \mathbb{R}) \bullet
(\alg.x k - \mu \bullet B(\alg.x k)).
\]
Thus the intermediate equality is
\[
\alg.x(k+1) =
\operatorname{scaledProximityOperator}(f,hf)(\mu)
\left(
(1-(1:\mathbb{R}))\bullet \alg.y k
+
(1:\mathbb{R})\bullet
(\alg.x k - \mu \bullet B(\alg.x k))
\right).
\]

Third, the proof closes with `simp`. The simplifier uses the real-number fact `1 - 1 = 0`, the vector-space identities `0 \bullet v = 0` and `0 + v = v`, and `1 \bullet v = v`. Therefore the vector inside the proximity operator simplifies exactly to
\[
\alg.x k - \mu \bullet B(\alg.x k).
\]
So the final equality of the `calc` chain is precisely the theorem’s conclusion. No `exact` or `linarith` command appears in this proof.

