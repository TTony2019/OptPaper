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
Let \(H\) be a type with the structure of a normed additive commutative group and a real inner product space. Thus elements of \(H\) can be subtracted, have a norm \(\|\cdot\|\), and have a real inner product \(\langle \cdot,\cdot\rangle\), written in Lean as `inner ℝ`.

Let \(\Phi:H\to\mathbb R\) be a real-valued function on \(H\), \(\mu\in\mathbb R\) a real coefficient, \(x:\mathbb R\to H\) and \(v:\mathbb R\to H\) two functions of a real parameter \(t\), and \(z\in H\) a fixed point. Let \(\Gamma:\mathbb R\to\mathbb R\) be another real-valued function of \(t\).

The hypotheses are:

1. \(hGamma\): for every real \(t\),
\[
\Gamma(t)=\frac12\|x(t)-z\|^2+\mu\Bigl(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\Bigr).
\]
Here \(x(t)-z\) is the vector difference of \(x(t)\) and \(z\), \(z-x(t)\) is its negative, and \(\langle z-x(t),v(t)\rangle\) is the real inner product of the vector \(z-x(t)\) with the vector \(v(t)\).

2. \(hdecreasing\): \(\Gamma\) is antitone, meaning that if \(t\le s\), then \(\Gamma(s)\le \Gamma(t)\); equivalently, \(\Gamma\) is non-increasing as a real-valued function.

The conclusion is the conjunction of these two facts:
\[
\Bigl(\forall t,\ \Gamma(t)=\frac12\|x(t)-z\|^2+\mu\bigl(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\bigr)\Bigr)
\quad\wedge\quad
\text{\(\Gamma\) is antitone}.
\]
In other words, the theorem merely packages the assumption \(hGamma\) and the assumption \(hdecreasing\) together into one combined statement.

## Lean proof
```lean
by
  exact ⟨hGamma, hdecreasing⟩
```

## Proof explanation
The proof goal is exactly a conjunction \(P\wedge Q\), where
\[
P=\forall t,\ \Gamma(t)=\frac12\|x(t)-z\|^2+\mu\bigl(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\bigr)
\]
and
\[
Q=\text{\(\Gamma\) is antitone}.
\]

The hypothesis `hGamma` is already a proof of \(P\), and the hypothesis `hdecreasing` is already a proof of \(Q\). In Lean, a proof of a conjunction \(P\wedge Q\) is constructed by pairing a proof of \(P\) with a proof of \(Q\). The proof term \(\langle hGamma,hdecreasing\rangle\) does exactly that: its first component proves the equality statement for all \(t\), and its second component proves that \(\Gamma\) is antitone.

The command `exact` closes the goal because this pair has precisely the statement type appearing in the theorem. No rewriting, simplification, or arithmetic reasoning is needed. The proof is therefore a trivial direct packaging of the two assumptions into the required conjunction; it establishes no new mathematical fact beyond combining the given hypotheses.

