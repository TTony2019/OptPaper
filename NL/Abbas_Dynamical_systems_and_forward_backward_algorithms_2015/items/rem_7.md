## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_7.lean`

## Lean statement
```lean
theorem gradient_rate_comparison {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → ℝ) (xSemigroup xNewton : ℝ → H) (c : ℝ)
    (hconvex : ConvexOn ℝ Set.univ Phi) (hgradient : Differentiable ℝ Phi)
    (hc : 0 < c)
    (hmin : ∃ z : H, ∀ y : H, Phi z ≤ Phi y)
    (hsemigroup : ∀ t, 0 ≤ t → HasDerivAt xSemigroup (-∇ Phi (xSemigroup t)) t)
    (hsemigroup_vclassical : ∀ t, 0 ≤ t →
      HasDerivAt (fun s ↦ ∇ Phi (xSemigroup s))
        (deriv (fun s ↦ ∇ Phi (xSemigroup s)) t) t)
    (hnewton_xclassical : ∀ t, 0 ≤ t → HasDerivAt xNewton (deriv xNewton t) t)
    (hnewton_vclassical : ∀ t, 0 ≤ t →
      HasDerivAt (fun s ↦ ∇ Phi (xNewton s)) (deriv (fun s ↦ ∇ Phi (xNewton s)) t) t)
    (hnewton : ∀ t, 0 ≤ t → (c * Real.exp (-t)) • deriv xNewton t +
      deriv (fun s ↦ ∇ Phi (xNewton s)) t + ∇ Phi (xNewton t) = 0) :
    (∃ C : ℝ, ∀ t, 0 < t → ‖∇ Phi (xSemigroup t)‖ ≤ C / t) ∧
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖∇ Phi (xNewton t)‖ ≤ C * Real.exp (-t)
```

## Statement explanation
Let \(H\) be a real inner product space that is also complete as a normed additive commutative group, so it is a real Hilbert space. The function \(\Phi : H \to \mathbb{R}\) is real-valued on \(H\). The functions \(x_{\text{Semigroup}} : \mathbb{R} \to H\) and \(x_{\text{Newton}} : \mathbb{R} \to H\) are curves in \(H\), and \(c\) is a real number.

The hypotheses are:
- \(h_{\text{convex}}\): \(\Phi\) is convex on the entire space \(H\).
- \(h_{\text{gradient}}\): \(\Phi\) is differentiable over \(\mathbb{R}\).
- \(h_c\): \(c > 0\).
- \(h_{\text{min}}\): \(\Phi\) attains a global minimum, i.e. there exists \(z \in H\) with \(\Phi(z) \le \Phi(y)\) for all \(y \in H\).
- \(h_{\text{semigroup}}\): For every \(t \ge 0\), the derivative of \(x_{\text{Semigroup}}\) at \(t\) equals \(-\nabla \Phi(x_{\text{Semigroup}}(t))\). Thus \(x_{\text{Semigroup}}\) is a gradient-flow trajectory.
- \(h_{\text{semigroup\_vclassical}}\): For every \(t \ge 0\), the composed curve \(s \mapsto \nabla \Phi(x_{\text{Semigroup}}(s))\) is differentiable at \(t\), and its derivative is the ordinary derivative of that curve at \(t\).
- \(h_{\text{newton\_xclassical}}\): For every \(t \ge 0\), \(x_{\text{Newton}}\) has derivative at \(t\) equal to \(\operatorname{deriv} x_{\text{Newton}}(t)\), a classical differentiability condition.
- \(h_{\text{newton\_vclassical}}\): For every \(t \ge 0\), the composed curve \(s \mapsto \nabla \Phi(x_{\text{Newton}}(s))\) is differentiable at \(t\), with derivative equal to its ordinary derivative at \(t\).
- \(h_{\text{newton}}\): For every \(t \ge 0\), the following forced Newton-like equation holds:
\[
(c e^{-t}) \operatorname{deriv} x_{\text{Newton}}(t) + \operatorname{deriv}\!\bigl(s \mapsto \nabla \Phi(x_{\text{Newton}}(s))\bigr)(t) + \nabla \Phi(x_{\text{Newton}}(t)) = 0.
\]

The conclusion is a conjunction of two rate estimates:
\[
(\exists C \in \mathbb{R},\ \forall t > 0,\ \|\nabla \Phi(x_{\text{Semigroup}}(t))\| \le C/t)
\]
and
\[
(\exists C \in \mathbb{R},\ \forall t \ge 0,\ \|\nabla \Phi(x_{\text{Newton}}(t))\| \le C e^{-t}).
\]
So the theorem states that under these convexity, differentiability, and dynamical assumptions, the gradient along the semigroup trajectory decays at least like \(O(1/t)\), and the gradient along the Newton trajectory decays at least exponentially like \(O(e^{-t})\).

## Lean proof
```lean
by
  refine ⟨?_, newton_gradient_exponential_rate Phi xNewton c hconvex hgradient hc hmin
    hnewton_xclassical hnewton_vclassical hnewton⟩
  exact semigroup_gradient_rate Phi xSemigroup hconvex hgradient hmin hsemigroup
    hsemigroup_vclassical
```

## Proof explanation
The proof is very short and relies entirely on two previously established theorems, one for the semigroup estimate and one for the Newton estimate. The command
```lean
refine ⟨?_, newton_gradient_exponential_rate Phi xNewton c hconvex hgradient hc hmin hnewton_xclassical hnewton_vclassical hnewton⟩
```
splits the conjunctive conclusion into two goals. The second conjunct is proved immediately by invoking the theorem `newton_gradient_exponential_rate` with the relevant arguments: the function \(\Phi\), the Newton curve \(x_{\text{Newton}}\), the constant \(c\), convexity, differentiability, \(c > 0\), existence of a minimizer, the two classical differentiability assumptions for the Newton curve, and the Newton equation. This supplies
\[
\exists C,\ \forall t \ge 0,\ \|\nabla \Phi(x_{\text{Newton}}(t))\| \le C e^{-t}.
\]
The first conjunct is left as the placeholder `?_`. The following command
```lean
exact semigroup_gradient_rate Phi xSemigroup hconvex hgradient hmin hsemigroup hsemigroup_vclassical
```
closes this first goal exactly by applying the theorem `semigroup_gradient_rate` to \(\Phi\), the semigroup curve, convexity, differentiability, existence of a minimizer, the semigroup differential equation, and the classical differentiability of the composed gradient curve. That theorem yields precisely
\[
\exists C,\ \forall t > 0,\ \|\nabla \Phi(x_{\text{Semigroup}}(t))\| \le C/t.
\]
There is no additional computational reasoning: the proof establishes the desired conjunction by combining two already available rate results.

Thus the proof consists of a structural split of the conjunction, followed by direct applications of the supporting theorems.Let \(H\) be a real inner product space that is also complete as a normed additive commutative group, so it is a real Hilbert space. The functions \(x_{\text{Semigroup}}, x_{\text{Newton}}\) are curves in \(H\), \(\Phi: H \to \mathbb{R}\) is a scalar field, and \(c\) is a real number.

The theorem assumes:
- \(\Phi\) is convex on all of \(H\).
- \(\Phi\) is differentiable over \(\mathbb{R}\).
- \(0 < c\).
- \(\Phi\) has a global minimizer: \(\exists z, \forall y, \Phi(z) \le \Phi(y)\).
- For every \(t \ge 0\), the derivative of \(x_{\text{Semigroup}}\) at \(t\) equals \(-\nabla \Phi(x_{\text{Semigroup}}(t))\), so \(x_{\text{Semigroup}}\) is a gradient-flow trajectory.
- For every \(t \ge 0\), the map \(s \mapsto \nabla \Phi(x_{\text{Semigroup}}(s))\) has derivative at \(t\) equal to its ordinary derivative at \(t\).
- For every \(t \ge 0\), the curve \(x_{\text{Newton}}\) has derivative at \(t\) equal to \(\operatorname{deriv} x_{\text{Newton}}(t)\).
- For every \(t \ge 0\), the map \(s \mapsto \nabla \Phi(x_{\text{Newton}}(s))\) has derivative at \(t\) equal to its ordinary derivative at \(t\).
- For every \(t \ge 0\), the vector equation
\[
(c e^{-t})\, \operatorname{deriv}(x_{\text{Newton}})(t) + \operatorname{deriv}\bigl(s\mapsto \nabla\Phi(x_{\text{Newton}}(s))\bigr)(t) + \nabla\Phi(x_{\text{Newton}}(t)) = 0
\]
holds.

The conclusion is:
\[
(\exists C\in\mathbb{R}, \forall t > 0,\ \|\nabla\Phi(x_{\text{Semigroup}}(t))\| \le C/t)
\]
and
\[
(\exists C\in\mathbb{R}, \forall t \ge 0,\ \|\nabla\Phi(x_{\text{Newton}}(t))\| \le C e^{-t}).
\]
Thus it gives a \(O(1/t)\) decay rate for the gradient along the semigroup flow and an exponential decay rate \(O(e^{-t})\) for the gradient along the Newton-type trajectory.

===PROOF_EXPLANATION===

The proof first uses `refine ⟨?_, ...⟩` to break the conjunctive conclusion into two independent goals. The second component, the Newton gradient rate, is proved by applying the previously established lemma `newton_gradient_exponential_rate` to the data \(\Phi\), \(x_{\text{Newton}}\), \(c\), and all the relevant hypotheses: convexity, differentiability, \(c>0\), existence of a minimizer, the two classical differentiability assumptions, and the Newton equation. This directly supplies
\[
\exists C,\ \forall t \ge 0,\ \|\nabla\Phi(x_{\text{Newton}}(t))\| \le C e^{-t}.
\]
The first component is left as a placeholder `?_` in the `refine` call.

The line `exact semigroup_gradient_rate Phi xSemigroup hconvex hgradient hmin hsemigroup hsemigroup_vclassical` fills that remaining goal exactly. It invokes the lemma `semigroup_gradient_rate`, supplying \(\Phi\), \(x_{\text{Semigroup}}\), convexity, differentiability, the global-minimizer assumption, the semigroup derivative law, and the classical differentiability of the gradient along the semigroup. That lemma yields precisely
\[
\exists C,\ \forall t > 0,\ \|\nabla\Phi(x_{\text{Semigroup}}(t))\| \le C/t.
\]
There is no separate computational reasoning beyond these applications of preexisting lemmas: the proof simply splits the conjunction and closes each side by exact application of the corresponding lemma.

