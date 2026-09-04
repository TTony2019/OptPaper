## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/thm_1.lean`

## Lean statement
```lean
theorem inertial_proximal_point_converges
    {A : SetValuedOperator H H} (hA : A.IsMaximalMonotone)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ)
    (hiteration : InertialProximalPointAlgorithm A x alpha lambda)
    (hzeros : A.zeros.Nonempty)
    (hlambda : ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ k : ℕ, lambda0 ≤ lambda k)
    (halpha : ∃ alpha0 : ℝ, 0 ≤ alpha0 ∧ alpha0 < 1 ∧
      ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0)
    (hsummable : Summable (fun k : ℕ => alpha (k + 1) * ‖x (k + 1) - x k‖ ^ 2)) :
    ∃ xhat : H, xhat ∈ A.zeros ∧
      Tendsto (fun k => toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xhat))
```

## Statement explanation
The theorem asserts a weak convergence result for an inertial proximal point algorithm. It assumes an implicit type `H`, equipped with whatever normed and weak-topological structure is needed for the notation used. The variables and hypotheses are as follows.

- `A : SetValuedOperator H H` is a set-valued operator on `H`.
- `hA : A.IsMaximalMonotone` states that `A` is maximal monotone.
- `x : ℕ → H` is a sequence in `H`.
- `alpha lambda : ℕ → ℝ` are real sequences of algorithm parameters.
- `hiteration : InertialProximalPointAlgorithm A x alpha lambda` states that `x`, `alpha`, and `lambda` satisfy the inertial proximal point algorithm for `A`.
- `hzeros : A.zeros.Nonempty` states that the zero set of `A` is nonempty.
- `hlambda : ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ k : ℕ, lambda0 ≤ lambda k` says there is a positive real lower bound \(\lambda_0\) for all parameters \(\lambda_k\).
- `halpha : ∃ alpha0 : ℝ, 0 ≤ alpha0 ∧ alpha0 < 1 ∧ ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0` says there is a constant \(\alpha_0\) with \(0 \le \alpha_0 < 1\) such that every parameter \(\alpha_k\) lies in the interval \([0,\alpha_0]\).
- `hsummable : Summable (fun k : ℕ => alpha (k + 1) * ‖x (k + 1) - x k‖ ^ 2)` says the series
  \[
  \sum_{k} \alpha_{k+1} \|x_{k+1}-x_k\|^2
  \]
  is summable.

The conclusion is that there exists a point `xhat : H` such that `xhat` belongs to `A.zeros` and the sequence \( \operatorname{toWeakSpace}_{\mathbb R,H}(x_k) \) tends to \( \operatorname{toWeakSpace}_{\mathbb R,H}(\hat x) \) in the weak topology as \(k\) tends to infinity. In other words, the iterates converge weakly to a zero of `A`.

## Lean proof
```lean
by
  have halg : InertialProximalAlgorithm A x alpha lambda := by
    intro k hk
    exact hiteration.update k hk
  exact convergence_of_inertial_proximal_method hA x alpha lambda halg hzeros hlambda halpha
    hsummable
```

## Proof explanation
The proof is very short and consists of two steps.

First, it creates an intermediate hypothesis
`halg : InertialProximalAlgorithm A x alpha lambda`
from the given hypothesis
`hiteration : InertialProximalPointAlgorithm A x alpha lambda`.
This reconciles the packaged point-algorithm formulation with the stepwise algorithm formulation expected by the main convergence theorem. The proof of `halg` uses `intro k hk` to introduce an arbitrary index `k` and any side-condition proof `hk`, and then applies `hiteration.update k hk` to obtain the required update condition at that index.

Second, it applies the previously proved general theorem `convergence_of_inertial_proximal_method` to the assumptions
`hA`, the sequences `x`, `alpha`, `lambda`, the derived hypothesis `halg`, and the remaining hypotheses `hzeros`, `hlambda`, `halpha`, and `hsummable`.
This yields exactly the stated conclusion: existence of a zero `xhat` of `A` such that the sequence converges weakly to `xhat`.

Only `intro` and `exact` are used in this proof. The commands `rw`, `simp`, and `linarith` do not appear here.

