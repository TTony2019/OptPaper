## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_1.lean`

## Lean statement
```lean
theorem corollary9 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y)
    (hS : (Optimization.argminSet Θ).Nonempty) :
    ∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto u Filter.atTop (nhds q)
```

## Statement explanation
The theorem `corollary9` is a strong-convergence corollary for an inertial forward-backward trajectory in a finite-dimensional real Hilbert space.

Let $H$ be a real inner product space which is also a normed additive commutative group and is finite-dimensional over $\mathbb R$. The data are:
- $\phi,\Theta : H \to \overline{\mathbb R}$, where $\overline{\mathbb R}$ is the extended real line, represented in Lean by `EReal`;
- $\psi : H \to \mathbb R$;
- $\operatorname{gradPsi} : H \to H$;
- real parameters $a,b,\lambda,L_\psi$;
- sequences $u,y : \mathbb N \to H$.

The hypotheses are:
- `IFBHypothesis phi Theta psi gradPsi a b lam Lpsi`, an inertial forward-backward structural hypothesis. The proof uses only the consequences that it supplies a positive constant $L_\psi>0$ and a Lipschitz estimate for $\operatorname{gradPsi}$.
- `IsIFBTrajectory phi psi gradPsi a b lam u y`, saying that the sequences $u$ and $y$ form an inertial forward-backward trajectory associated to the displayed data.
- $( \operatorname{argminSet}(\Theta) ) \neq \varnothing$, meaning that the extended-real-valued function $\Theta$ has at least one global minimizer.

The conclusion is:

$$
\exists q \in \operatorname{argminSet}(\Theta),\quad
\operatorname{Tendsto} u \operatorname{atTop} (\operatorname{nhds} q).
$$

In ordinary terms, there is a minimizer $q$ of $\Theta$ such that the sequence $u_k$ converges strongly, i.e. in the norm topology of $H$, to $q$ as $k \to \infty$.

Thus the corollary says that, in finite dimension and under the stated inertial forward-backward hypotheses, if the objective $\Theta$ has a minimizer, then the trajectory $u$ converges strongly to some minimizer. The weak convergence is obtained from the general theorem for the algorithm, while finite-dimensionality is used to upgrade weak convergence to strong convergence.

## Lean proof
```lean
by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have hweakSymm : Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
    finite_dimensional_weak_inverse_continuous
  have hLpsi : 0 < Lpsi := ifb_lipschitz_constant_pos phi Θ psi gradPsi a b lam Lpsi hH
  have hLip : LipschitzWith Lpsi.toNNReal gradPsi := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [dist_eq_norm, Real.coe_toNNReal Lpsi hLpsi.le] using hH.psi_lipschitz x y
  have hgradCont : Continuous gradPsi := hLip.continuous
  have hgradWeak : IsWeakToWeakSequentiallyContinuous gradPsi := by
    unfold IsWeakToWeakSequentiallyContinuous
    intro x x₀ hx
    have hxStrong : Filter.Tendsto x Filter.atTop (nhds x₀) := by
      simpa using (hweakSymm.tendsto (toWeakSpace ℝ H x₀)).comp hx
    have hgradStrong : Filter.Tendsto (fun n => gradPsi (x n)) Filter.atTop
        (nhds (gradPsi x₀)) :=
      (hgradCont.tendsto x₀).comp hxStrong
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (gradPsi x₀)).comp hgradStrong
  rcases (theorem1 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB).2.1
      ⟨hS, Or.inr (Or.inr (Or.inl hgradWeak))⟩ with
    ⟨q, hqS, hweak⟩
  exact ⟨q, hqS, by simpa using (hweakSymm.tendsto (toWeakSpace ℝ H q)).comp hweak⟩
```

## Proof explanation
The proof first supplies the missing completeness instance. Since the theorem assumes $H$ is finite-dimensional over $\mathbb R$, the line

`letI : CompleteSpace H := FiniteDimensional.complete ℝ H`

uses the fact that every finite-dimensional real normed space is complete. This is needed because the cited theorem `theorem1` is formulated under a `CompleteSpace H` hypothesis.

Next, the proof establishes a useful continuity fact. Let

$$
\iota_H : H \to \operatorname{WeakSpace}_{\mathbb R} H
$$

be the canonical map from $H$ with its norm topology to the same underlying space with the weak topology, corresponding to Lean's `toWeakSpace ℝ H`. The cited result `finite_dimensional_weak_inverse_continuous` states that, because $H$ is finite-dimensional,

$$
\iota_H^{-1} : \operatorname{WeakSpace}_{\mathbb R} H \to H
$$

is continuous. The proof stores this as `hweakSymm`. Mathematically, in finite dimension the weak topology agrees with the norm topology, so weak convergence implies strong convergence. This fact is used twice: once to turn weak convergence of a sequence into strong convergence, and once at the end to turn the weak convergence of $u_k$ into strong convergence.

The proof then obtains positivity of the Lipschitz constant. The cited lemma `ifb_lipschitz_constant_pos` says that from

$$
\texttt{IFBHypothesis } \phi\ \Theta\ \psi\ \operatorname{gradPsi}\ a\ b\ \lambda\ L_\psi
$$

one has

$$
0 < L_\psi.
$$

This is recorded as `hLpsi`.

Using the same hypothesis, the proof shows that `gradPsi` is Lipschitz with constant $L_\psi$. It rewrites the goal using the characterization of `LipschitzWith` by the pointwise distance estimate. The resulting goal is

$$
\operatorname{dist}(\operatorname{gradPsi} x,\operatorname{gradPsi} y)
\le L_\psi^{\ge 0} \operatorname{dist}(x,y)
$$

for all $x,y$, where $L_\psi^{\ge 0}$ denotes the nonnegative-real version of $L_\psi$. The proof introduces arbitrary $x,y$ by `intro x y` and invokes the field `hH.psi_lipschitz x y`, which supplies the Lipschitz estimate for `gradPsi`. The simplification uses

$$
\operatorname{dist}(x,y)=\|x-y\|
$$

and the identity

$$
(L_\psi^{\ge 0} : \mathbb R)=L_\psi,
$$

which follows from $0\le L_\psi$. Thus `hLip` is established. Since every Lipschitz function is continuous, the proof immediately gets `hgradCont : Continuous gradPsi`.

The next step is to prove that `gradPsi` is weak-to-weak sequentially continuous. The definition `IsWeakToWeakSequentiallyContinuous` says that for every sequence $x_n$ and every point $x_0$, if

$$
\iota_H(x_n) \to \iota_H(x_0)
$$

in the weak topology, then

$$
\iota_H(\operatorname{gradPsi}(x_n)) \to \iota_H(\operatorname{gradPsi}(x_0))
$$

in the weak topology. The proof unfolds this definition and introduces an arbitrary sequence $x$, a point $x_0$, and the weak convergence hypothesis `hx`.

The line
```lean
have hxStrong : Filter.Tendsto x Filter.atTop (nhds x₀) := by
  simpa using (hweakSymm.tendsto (toWeakSpace ℝ H x₀)).comp hx
```
uses continuity of $\iota_H^{-1}$. Since $\iota_H^{-1}$ is continuous at $\iota_H(x_0)$, applying it to the weak convergence $\iota_H(x_n)\to \iota_H(x_0)$ gives strong convergence $x_n\to x_0$. The `simpa` step simplifies $(\iota_H^{-1}\circ \iota_H)(x_n)$ to $x_n$.

Then `hgradCont` is used:
```lean
have hgradStrong : Filter.Tendsto (fun n => gradPsi (x n)) Filter.atTop
    (nhds (gradPsi x₀)) :=
  (hgradCont.tendsto x₀).comp hxStrong
```
Because `gradPsi` is continuous in the norm topology, the strong convergence $x_n\to x_0$ implies strong convergence

$$
\operatorname{gradPsi}(x_n)\to \operatorname{gradPsi}(x_0).
$$

Finally, the proof converts this strong convergence into weak convergence. The canonical map `toWeakSpaceCLM ℝ H` is the continuous linear map $H\to \operatorname{WeakSpace}_{\mathbb R} H$. Continuous linear maps preserve sequential convergence, so applying it to the strong convergence

$$
\operatorname{gradPsi}(x_n)\to \operatorname{gradPsi}(x_0)
$$

gives

$$
\iota_H(\operatorname{gradPsi}(x_n))\to \iota_H(\operatorname{gradPsi}(x_0)).
$$

The simplification `toWeakSpaceCLM_eq_toWeakSpace` identifies the action of `toWeakSpaceCLM` with `toWeakSpace`. This proves `hgradWeak`, i.e. that `gradPsi` is weak-to-weak sequentially continuous.

The proof now applies `theorem1`. That theorem assumes the same inertial forward-backward hypotheses `hH` and `hIFB`, and under a completeness assumption on $H$ concludes, among other things, that if $\operatorname{argminSet}(\Theta)$ is nonempty and one of several regularity alternatives holds, then there exists a minimizer $q\in \operatorname{argminSet}(\Theta)$ such that

$$
\iota_H(u_k)\to \iota_H(q)
$$

weakly. The regularity alternatives include unique minimization, differentiability with weak-to-weak continuous gradient, weak-to-weak sequential continuity of `gradPsi`, or convexity of the epigraph of $\psi$. The proof uses the third alternative, `IsWeakToWeakSequentiallyContinuous gradPsi`, which was just proved as `hgradWeak`.

Thus the proof supplies to `theorem1` the pair consisting of `hS`, the nonemptiness of the argmin set, and the disjunct choosing `hgradWeak`. It then extracts, by `rcases`, a point $q$, the membership $q\in\operatorname{argminSet}(\Theta)$, and the weak convergence

$$
\iota_H(u_k)\to \iota_H(q).
$$

The final step is
```lean
exact ⟨q, hqS, by simpa using (hweakSymm.tendsto (toWeakSpace ℝ H q)).comp hweak⟩
```
Here continuity of $\iota_H^{-1}$ at $\iota_H(q)$ is composed with the weak convergence $\iota_H(u_k)\to \iota_H(q)$. This yields

$$
\iota_H^{-1}(\iota_H(u_k))\to \iota_H^{-1}(\iota_H(q)).
$$

Since $\iota_H^{-1}\circ \iota_H$ is the identity, this simplifies to the desired strong convergence

$$
u_k\to q.
$$

Together with $q\in\operatorname{argminSet}(\Theta)$, this gives exactly the conclusion of `corollary9`.

