## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/def_7.lean`

## Lean statement
```lean
def IsRealAnalyticOn {N : Type*} [Fintype N] (Ω : Set (EuclideanSpace ℝ N))
    (Φ : EuclideanSpace ℝ N → ℝ) : Prop :=
  IsOpen Ω ∧ AnalyticOnNhd ℝ Φ Ω
```

## Statement explanation
The declaration introduces a predicate named `IsRealAnalyticOn`. It is parametrized by a finite index type $N$, a subset $\Omega \subseteq \mathbb{R}^N$, and a real-valued function $\Phi : \mathbb{R}^N \to \mathbb{R}$. Here $\mathbb{R}^N$ is the Euclidean coordinate space indexed by $N$; the finiteness of $N$ makes this a finite-dimensional real Euclidean space. The predicate returns a proposition, not a piece of data.

Its definition is the conjunction

$$
\operatorname{IsOpen}(\Omega) \land \operatorname{AnalyticOnNhd}_{\mathbb{R}}(\Phi,\Omega).
$$

The first conjunct asserts that $\Omega$ is open in the Euclidean topology. The second conjunct is the Mathlib neighborhood-analyticity predicate `AnalyticOnNhd`, applied to the real scalar field $\mathbb{R}$, the function $\Phi$, and the set $\Omega$. Mathematically, this means that $\Phi$ is real analytic at every point of $\Omega$: near each such point it has a convergent power-series expansion in the coordinates. Because the definition also requires $\Omega$ to be open, the whole proposition says exactly that $\Phi$ is real analytic on the open set $\Omega$. There is no additional assertion that $\Phi$ is analytic outside $\Omega$, nor any global analyticity statement on all of $\mathbb{R}^N$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The source is a definition, so its body is simply the proposition

$$
\operatorname{IsOpen}(\Omega) \land \operatorname{AnalyticOnNhd}_{\mathbb{R}}(\Phi,\Omega).
$$

No theorem, lemma, or local result is invoked. No proof steps, case splits, rewrites, simplifications, or arithmetic reasoning occur. In particular, Lean commands such as `intro`, `rw`, `simp`, `exact`, and `linarith` do not appear.

Semantically, the declaration only records the meaning of the predicate `IsRealAnalyticOn`. If one wanted to prove $\operatorname{IsRealAnalyticOn}(\Omega,\Phi)$ for a concrete $\Omega$ and $\Phi$, the definition would reduce that goal to two subgoals: prove that $\Omega$ is open, and prove that $\Phi$ is real analytic at every point of $\Omega$. This declaration supplies that reduction, but it does not itself establish either subgoal.

