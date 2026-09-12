## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/def_5.lean`

## Lean statement
```lean
theorem def_5 {Λ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : Λ → SetValuedOperator H H)
    (hA : ∀ μ, (A μ).IsMaximalMonotone) (lam : ERealFunction.PosReal) (μ : Λ) :
      SetValuedOperator.yosidaRegularization (A μ) (hA μ) (lam : ℝ) lam.2 =
        fun x => (lam : ℝ)⁻¹ •
          (x - SetValuedOperator.resolventMap (A μ) (hA μ) (lam : ℝ) lam.2 x)
```

## Statement explanation
The declaration is parametric over an arbitrary indexing type \(\Lambda\), a real Hilbert space \(H\), a family of set-valued operators \(A=(A_\mu)_{\mu\in\Lambda}\) from \(H\) to \(H\), a proof `hA` that each \(A_\mu\) is maximal monotone, a positive-real datum `lam` whose underlying real parameter is \(\lambda=(\texttt{lam}:\mathbb{R})\), and an index \(\mu\in\Lambda\). The term `lam.2` is the proof component stored in the positive-real datum `lam`; it is the positivity certificate that the resolvent and Yosida constructions require for the parameter \(\lambda\).

The conclusion is an equality of functions \(H\to H\). It says that the Yosida regularization of the operator \(A_\mu\) with parameter \(\lambda\) is exactly the map

\[
x \mapsto \lambda^{-1}\cdot\bigl(x - J_\lambda^{A_\mu}(x)\bigr),
\]

where

\[
J_\lambda^{A_\mu}(x)
\]

is the value at \(x\) of the resolvent map of \(A_\mu\) with parameter \(\lambda\), written in Lean as `SetValuedOperator.resolventMap (A μ) (hA μ) (lam : ℝ) lam.2 x`. The scalar multiplication is by the reciprocal real number \(\lambda^{-1}\), and the subtraction is the vector subtraction in \(H\).

In ordinary language, the theorem states that for every maximal monotone set-valued operator \(A_\mu\) and every positive real parameter \(\lambda\), the Yosida regularization \(A_{\mu,\lambda}\) is the single-valued map obtained by taking the identity minus the resolvent and multiplying by \(1/\lambda\). The maximal-monotonicity proof `hA μ` and the positivity component `lam.2` are carried as arguments because the relevant definitions require them, but the mathematical content of the conclusion is precisely this formula for the Yosida regularization.

## Lean proof
```lean
rfl
```

## Proof explanation
The proof is exactly `rfl`. In Lean, `rfl` proves a goal of the form \(a=a\) by reflexivity, and it succeeds when the two sides are definitionally equal after unfolding definitions. Here the left-hand side is the term

\[
\text{SetValuedOperator.yosidaRegularization}(A_\mu, \text{maximal monotonicity proof}, \lambda, \text{positivity proof}),
\]

while the right-hand side is the explicit map

\[
x \mapsto \lambda^{-1}\cdot\bigl(x - J_\lambda^{A_\mu}(x)\bigr).
\]

By the definition of `SetValuedOperator.yosidaRegularization`, the left-hand side unfolds to exactly this map. Therefore the two sides are not merely equal after a mathematical argument; they are the same by definition, and `rfl` closes the goal immediately.

No other Lean commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur in the proof. No named theorem is invoked. In particular, the proof does not use maximal monotonicity to establish any new existence, uniqueness, or regularity statement; the maximal-monotonicity proof is merely passed as an argument to the Yosida-regularization and resolvent constructions. The declaration thereby records the definitional identity that the Yosida regularization is the map \(x\mapsto \lambda^{-1}(x-J_\lambda^{A_\mu}(x))\).

