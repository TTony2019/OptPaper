## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/thm_3.lean`

## Lean statement
```lean
theorem strongly_convex_third_order_exponential_estimates {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (u : ℝ → H) (xStar : H) (mu t0 : ℝ)
    (hStrong : IsStronglyConvexWith (fun x : H => (f x : EReal)) mu)
    (hxStar : ∀ x : H, f xStar ≤ f x ∧ (f x = f xStar → x = xStar))
    (hTrajectory : IsStronglyConvexThirdOrderEvolution u mu f)
    (hFContDiff : ContDiff ℝ 1 f) (hUContDiff : ContDiff ℝ 3 u) :
    ∀ t ≥ t0,
      f (u t + (Real.sqrt mu)⁻¹ • deriv u t) - sInf (Set.range f) ≤
        stronglyConvexLyapunov f u xStar mu t0 hxStar * Real.exp (-Real.sqrt mu * (t - t0)) ∧
      f (u t) - sInf (Set.range f) ≤
        (stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t +
          Real.exp (Real.sqrt mu * t0) * initialObjectiveGap f u xStar t0 -
          stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t0) *
          Real.exp (-Real.sqrt mu * t) ∧
      ‖u t + (Real.sqrt mu)⁻¹ • deriv u t - xStar‖ ^ 2 ≤
        (Real.exp (Real.sqrt mu * t0) / Real.sqrt mu) *
          (Real.sqrt mu * ‖u t0 + (Real.sqrt mu)⁻¹ • deriv u t0 - xStar‖ ^ 2 +
            2 * stronglyConvexLyapunov f u xStar mu t0 hxStar * (t - t0)) *
          Real.exp (-Real.sqrt mu * t) ∧
      ‖u t - xStar‖ ^ 2 ≤ (2 / mu) *
        (stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t +
          Real.exp (Real.sqrt mu * t0) * initialObjectiveGap f u xStar t0 -
          stronglyConvexEnergyConstant f u xStar mu t0 hxStar * Real.sqrt mu * t0) *
          Real.exp (-Real.sqrt mu * t)
```

## Statement explanation
The theorem is stated in a real Hilbert space \(H\), with a real-valued objective \(f:H\to\mathbb R\), a curve \(u:\mathbb R\to H\), a point \(x^\star\in H\), and real parameters \(\mu\) and \(t_0\). The hypotheses are:

- `hStrong` says that the extended-real-valued function \(x\mapsto f(x)\) is strongly convex with parameter \(\mu\). The internal formula of `IsStronglyConvexWith` is not expanded in the supplied source; this hypothesis is the strong-convexity input.
- `hxStar` says that \(x^\star\) is a global minimizer of \(f\) and is unique: for every \(x\in H\),
  \[
  f(x^\star)\le f(x),
  \]
  and if \(f(x)=f(x^\star)\), then \(x=x^\star\).
- `hTrajectory` says that \(u\) is a strongly convex third-order evolution trajectory for \(\mu\) and \(f\). The exact differential inclusion/equation behind `IsStronglyConvexThirdOrderEvolution` is not shown in the excerpt; in the proof it is passed unchanged to the core lemma.
- `hFContDiff` says that \(f\) is continuously differentiable of order \(1\), i.e. \(f\) is \(C^1\).
- `hUContDiff` says that the curve \(u\) is \(C^3\).

The conclusion is that for every \(t\ge t_0\), four estimates hold simultaneously. Write
\[
L=\text{the value of } \texttt{stronglyConvexLyapunov f u xStar mu t0 hxStar},
\]
\[
E=\text{the value of } \texttt{stronglyConvexEnergyConstant f u xStar mu t0 hxStar},
\]
\[
G=\text{the value of } \texttt{initialObjectiveGap f u xStar t0}.
\]
The exact definitions of these three constants are not included in the supplied excerpt; only their roles in the estimates are visible. Also, \(\operatorname{sInf}(\operatorname{Set.range} f)\) is the infimum of the set of values of \(f\), i.e. \(\inf_{x\in H} f(x)\). The four estimates are:

1. an exponential decay bound for the objective gap at the shifted point \(u(t)+(\sqrt{\mu})^{-1}\dot u(t)\):
\[
f\!\left(u(t)+(\sqrt{\mu})^{-1}\dot u(t)\right)-\inf_{x\in H} f(x)
\le L\,e^{-\sqrt{\mu}(t-t_0)};
\]

2. a bound for the objective gap along the trajectory itself:
\[
f(u(t))-\inf_{x\in H} f(x)
\le
\left(
E\sqrt{\mu}\,t
+e^{\sqrt{\mu}t_0}G
-E\sqrt{\mu}\,t_0
\right)
e^{-\sqrt{\mu}t};
\]

3. an exponential decay bound for the squared distance of the shifted point to the minimizer:
\[
\left\|u(t)+(\sqrt{\mu})^{-1}\dot u(t)-x^\star\right\|^2
\le
\frac{e^{\sqrt{\mu}t_0}}{\sqrt{\mu}}
\left(
\sqrt{\mu}\left\|u(t_0)+(\sqrt{\mu})^{-1}\dot u(t_0)-x^\star\right\|^2
+2L(t-t_0)
\right)
e^{-\sqrt{\mu}t};
\]

4. an exponential decay bound for the squared distance of \(u(t)\) to \(x^\star\):
\[
\|u(t)-x^\star\|^2
\le
\frac{2}{\mu}
\left(
E\sqrt{\mu}\,t
+e^{\sqrt{\mu}t_0}G
-E\sqrt{\mu}\,t_0
\right)
e^{-\sqrt{\mu}t}.
\]

Thus the theorem says that, under strong convexity, uniqueness of the minimizer, the third-order evolution assumption, and regularity of \(f\) and \(u\), the objective gaps and squared distances to the minimizer obey explicit exponential decay estimates of the type associated with TOGES/third-order in time evolution equations.

## Lean proof
```lean
by
  have hGradient : ∀ x : H, HasFDerivAt f (innerSL ℝ (gradient f x)) x := by
    intro x
    simpa [innerSL_apply_apply] using
      ((hFContDiff.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have huDiff : Differentiable ℝ u := hUContDiff.differentiable (by norm_num)
  have hFirstDiff : Differentiable ℝ (deriv u) :=
    (hUContDiff.of_le (by norm_num)).differentiable_deriv_two
  have hSecondDiff : Differentiable ℝ (deriv (deriv u)) := by
    exact hUContDiff.deriv'.differentiable_deriv_two
  have hRegularity :
      (∀ t, t0 ≤ t → HasDerivAt u (deriv u t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv (deriv u))
        (deriv (deriv (deriv u)) t) t) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      exact (huDiff t).hasDerivAt
    · intro t _
      exact (hFirstDiff t).hasDerivAt
    · intro t _
      exact (hSecondDiff t).hasDerivAt
  exact strongly_convex_third_order_exponential_estimates_core f u (deriv u)
    (deriv (deriv u)) (deriv (deriv (deriv u))) (gradient f) xStar mu t0 hStrong hxStar
    hTrajectory hGradient hRegularity.1 hRegularity.2.1 hRegularity.2.2
    (fun t => ⟨rfl, rfl, rfl⟩)
```

## Proof explanation
The proof reduces the theorem to the private core lemma `strongly_convex_third_order_exponential_estimates_core`. The core lemma has the same four exponential estimates, but it assumes separately that certain functions are the first, second, and third derivatives of \(u\), and it assumes a gradient map \(g\) such that the Fréchet derivative of \(f\) at \(x\) is the inner-product functional `innerSL ℝ (g x)`. The main theorem supplies those missing data from the \(C^1\) assumption on \(f\) and the \(C^3\) assumption on \(u\).

First, the proof constructs the gradient information. It proves
\[
\texttt{hGradient}:\quad \forall x\in H,\quad \texttt{HasFDerivAt f (innerSL ℝ (gradient f x)) x}.
\]
For a fixed \(x\), the hypothesis `hFContDiff` gives differentiability of \(f\) at \(x\). The expression
\[
\texttt{(hFContDiff.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt}
\]
uses the fact that differentiability of a real-valued function on a Hilbert space yields a gradient `gradient f x`, and that the corresponding Fréchet derivative is the continuous linear functional `innerSL ℝ (gradient f x)`. The `simpa [innerSL_apply_apply]` step rewrites this functional into the standard inner-product form: for \(y\in H\),
\[
y\mapsto \langle \nabla f(x),y\rangle.
\]
So `hGradient` is exactly the core lemma's hypothesis `hGrad` with \(g=\nabla f\).

Next, the proof extracts differentiability of \(u\), \(\operatorname{deriv}u\), and \(\operatorname{deriv}(\operatorname{deriv}u)\). From `hUContDiff`, which says \(u\) is \(C^3\), it obtains `huDiff : Differentiable ℝ u`. It also proves
\[
\texttt{hFirstDiff}:\quad \texttt{Differentiable ℝ (deriv u)}
\]
by weakening the \(C^3\) assumption to \(C^2\) and applying the lemma `differentiable_deriv_two`, which says that a \(C^2\) curve has a differentiable first derivative. Then it proves
\[
\texttt{hSecondDiff}:\quad \texttt{Differentiable ℝ (deriv (deriv u))}
\]
using `hUContDiff.deriv'`, which lowers the regularity order after differentiating, followed again by `differentiable_deriv_two`. The tactic `by norm_num` discharges the numerical side conditions on the differentiability order. These three differentiability facts are precisely what is needed to turn the iterated derivatives into `HasDerivAt` statements.

The proof then assembles `hRegularity`, a conjunction of three derivative assertions:
\[
\forall t,\ t_0\le t\ \Rightarrow\ \texttt{HasDerivAt u (deriv u t) t},
\]
\[
\forall t,\ t_0\le t\ \Rightarrow\ \texttt{HasDerivAt (deriv u) (deriv (deriv u) t) t},
\]
\[
\forall t,\ t_0\le t\ \Rightarrow\ \texttt{HasDerivAt (deriv (deriv u)) (deriv (deriv (deriv u)) t) t}.
\]
The tactic `refine ⟨?_, ?_, ?_⟩` splits the conjunction into three goals. In each goal, `intro t _` introduces the time \(t\) and ignores the inequality \(t_0\le t\), since the differentiability results are global. Then `exact (huDiff t).hasDerivAt`, `exact (hFirstDiff t).hasDerivAt`, and `exact (hSecondDiff t).hasDerivAt` supply, respectively, the derivative of \(u\), of \(\operatorname{deriv}u\), and of \(\operatorname{deriv}(\operatorname{deriv}u)\). Thus the first, second, and third derivatives of \(u\) are represented by the iterated `deriv` operators.

Finally, the proof applies the core lemma:
\[
\texttt{strongly\_convex\_third\_order\_exponential\_estimates\_core}.
\]
It instantiates the core lemma's abstract derivative functions as
\[
\text{firstDerivative}=\operatorname{deriv}u,\qquad
\text{secondDerivative}=\operatorname{deriv}(\operatorname{deriv}u),\qquad
\text{thirdDerivative}=\operatorname{deriv}(\operatorname{deriv}(\operatorname{deriv}u)),
\]
and its gradient map as \(g=\nabla f\). The arguments `hStrong`, `hxStar`, and `hTrajectory` are passed through unchanged. The newly proved `hGradient` supplies the core lemma's `hGrad`. The three components of `hRegularity` supply the core lemma's `hu`, `hFirst`, and `hSecond`. The compatibility condition required by the core lemma is proved by
\[
\texttt{(fun t => ⟨rfl, rfl, rfl⟩)},
\]
because the chosen first, second, and third derivative functions are definitionally the same as the corresponding iterated `deriv` expressions. Therefore the core lemma yields exactly the four estimates stated in the theorem, with \(\operatorname{deriv}u\) appearing in the shifted point. The final `exact` closes the goal by this direct application. The proof does not use `rw` or `linarith`; the main tactics are `intro`, `simpa`, `refine`, and `exact`.

