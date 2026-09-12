## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/rem_2.lean`

## Lean statement
```lean
theorem variable_moreau_index_lower_bound (h gamma beta lam : ℝ)
    (hgamma : 0 < gamma) (hlam : 0 < lam)
    (hbound : lam ≥ (h / 2 + beta) / gamma) :
    lam ≥ (h / 2 + beta) / gamma
```

## Statement explanation
This Lean declaration is a theorem named `variable_moreau_index_lower_bound`. Its parameters are five real numbers: $h$, $\gamma$, $\beta$, and $\lambda$ (written `h gamma beta lam : ℝ` in Lean). The hypotheses are:

- $h_{\gamma}$: $0 < \gamma$ (Lean name `hgamma`),
- $h_{\lambda}$: $0 < \lambda$ (Lean name `hlam`),
- $h_{\text{bound}}$: $\lambda \ge \dfrac{h/2 + \beta}{\gamma}$ (Lean name `hbound`).

The single conclusion is again the inequality

$$
\lambda \;\ge\; \frac{h/2 + \beta}{\gamma}.
$$

Mathematically, the statement expresses a lower bound on the quantity $\lambda$ in terms of $h$, $\beta$ and $\gamma$. The right-hand side is the quotient of $h/2 + \beta$ by $\gamma$; positivity of $\gamma$ guarantees that this quotient is a well-defined real number. The content of the theorem is precisely this lower bound: whenever $\lambda$ already satisfies $\lambda \ge (h/2+\beta)/\gamma$, the theorem restates that same bound as its conclusion. The hypotheses $0 < \gamma$ and $0 < \lambda$ are carried along but play no role in reaching the conclusion; they encode the contextual expectations that the damping/index coefficient $\lambda$ and the parameter $\gamma$ are positive, which matters for interpreting the inequality but is not needed to derive it from the assumption.

## Lean proof
```lean
by
  exact hbound
```

## Proof explanation
The proof consists of a single tactic line:
```lean
by
  exact hbound
```

The `by` keyword opens a tactic-mode proof block. The tactic `exact hbound` closes the goal by supplying a term of exactly the required type. Here the goal after entering the proof is the proposition

$$
\lambda \;\ge\; \frac{h/2 + \beta}{\gamma},
$$

and `hbound` is a local hypothesis whose type is literally that same proposition:

$$
\lambda \;\ge\; \frac{h/2 + \beta}{\gamma}.
$$

Since the goal and the hypothesis have the identical type, `exact hbound` discharges the goal immediately, and the proof is complete.

No named theorem, lemma, or previously established fact is invoked: the local declarations listed for context contain no statements, and the proof does not reference any of them. The hypotheses $0 < \gamma$ and $0 < \lambda$ are not used by the tactic; they are hypotheses of the declaration but are not needed to derive the conclusion. There is no rewriting (`rw`), simplification (`simp`), or arithmetic reasoning (`linarith`) involved; the entire proof is the direct identification of the goal with the hypothesis. In other words, the theorem is an immediate restatement of its own assumption $h_{\text{bound}}$.

