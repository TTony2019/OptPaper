## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_2.lean`

## Lean statement
```lean
theorem bregman_distance_remark {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → ℝ) (mu : ℝ) (x : ℝ → H) (z : H) (v : ℝ → H) (Gamma : ℝ → ℝ)
    (hGamma : ∀ t, Gamma t = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * (Phi z - Phi (x t) - inner ℝ (z - x t) (v t)))
    (hdecreasing : Antitone Gamma) :
    (∀ t, Gamma t = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * (Phi z - Phi (x t) - inner ℝ (z - x t) (v t))) ∧ Antitone Gamma
```

## Statement explanation
The declaration `bregman_distance_remark` is a theorem in a real inner product space. It fixes a type $H$ which is both a normed additive commutative group and an inner product space over $\mathbb R$, so $H$ has a norm $\lVert\cdot\rVert$ and a real inner product $\langle\cdot,\cdot\rangle$. The variables are:

- $\Phi : H \to \mathbb R$, a real-valued function on $H$;
- $\mu \in \mathbb R$, a real scalar;
- $x : \mathbb R \to H$, a curve or path in $H$;
- $z \in H$, a fixed point;
- $v : \mathbb R \to H$, a vector-valued function of time;
- $\Gamma : \mathbb R \to \mathbb R$, a real-valued function of time.

The hypotheses are:

1. `hGamma` states that for every $t \in \mathbb R$,

$$
\Gamma(t)=\frac12\lVert x(t)-z\rVert^2
+\mu\Bigl(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\Bigr).
$$

So $\Gamma$ is assumed to be given by this explicit Bregman-type expression involving the squared distance from $x(t)$ to $z$, the difference of values of $\Phi$, and the inner product of $z-x(t)$ with $v(t)$.

2. `hdecreasing` states that $\Gamma$ is antitone. Since $\Gamma : \mathbb R \to \mathbb R$, this means that for all $s,t \in \mathbb R$,

$$
s \le t \implies \Gamma(t) \le \Gamma(s).
$$

Equivalently, $\Gamma$ is nonincreasing.

The conclusion is the conjunction

$$
\Bigl(\forall t \in \mathbb R,\ \Gamma(t)=\frac12\lVert x(t)-z\rVert^2
+\mu\bigl(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\bigr)\Bigr)
\;\wedge\;
\mathrm{Antitone}(\Gamma).
$$

Thus the theorem says: under the assumptions that $\Gamma$ is defined by that formula at every $t$ and that $\Gamma$ is antitone, both of those facts hold together. It does not derive any further inequality or identity; it packages the two hypotheses into the corresponding conjunction.

## Lean proof
```lean
by
  exact ⟨hGamma, hdecreasing⟩
```

## Proof explanation
The proof is a single tactic:
```lean
by
  exact ⟨hGamma, hdecreasing⟩
```

At the beginning of the proof, the goal is exactly the conjunction

$$
\Bigl(\forall t,\ \Gamma(t)=\cdots\Bigr) \wedge \mathrm{Antitone}(\Gamma).
$$

The expression `⟨hGamma, hdecreasing⟩` is Lean’s anonymous constructor for a conjunction, equivalent to applying `And.intro hGamma hdecreasing`. It builds a proof of $A \wedge B$ from a proof of $A$ and a proof of $B$.

Here the left conjunct is precisely the type of the hypothesis `hGamma`, namely the statement that for every $t$,

$$
\Gamma(t)=\frac12\lVert x(t)-z\rVert^2
+\mu\bigl(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\bigr).
$$

The right conjunct is precisely the type of the hypothesis `hdecreasing`, namely that $\Gamma$ is antitone.

Therefore `exact` closes the goal by supplying the pair consisting of those two already available hypotheses. No rewriting, simplification, arithmetic reasoning, monotonicity reasoning, or inner-product manipulation is used. There are no cited local theorems or lemmas invoked in the proof; the only mathematical content used is the two hypotheses themselves.

