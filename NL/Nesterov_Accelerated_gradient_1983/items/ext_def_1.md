## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_def_1.lean`

## Lean statement
```lean
theorem IsC11.hasGradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (h : IsC11 f L) (x : E) :
    HasGradientAt f (gradient f x) x
```

## Statement explanation
Let \(E\) be a complete real inner product space, i.e. a real Hilbert space, let \(f : E \to \mathbb{R}\) be a real-valued function, let \(L \in \mathbb{R}\), and let \(x \in E\). The hypothesis is \(h : \operatorname{IsC11} f L\), a bundled regularity condition on \(f\) with parameter \(L\). The conclusion is

\[
\operatorname{HasGradientAt} f (\operatorname{gradient} f x) x.
\]

In ordinary mathematical language, this says that if \(f\) satisfies the \(C^{1,1}\)-type condition encoded by \(\operatorname{IsC11} f L\), then at the point \(x\) the function \(f\) has a gradient, and that gradient is exactly the vector \(\operatorname{gradient} f x\). The statement is pointwise in \(x\). The parameter \(L\) does not appear in the conclusion, and the proof uses only the \(C^1\) smoothness component of the bundled hypothesis \(h\).

The meaning of \(\operatorname{HasGradientAt} f g x\) is that the Fréchet derivative of \(f\) at \(x\), when it exists, is represented by the vector \(g\) through the real inner product. Concretely, this means

\[
Df(x)(v) = \langle g, v\rangle
\]

for all \(v \in E\), equivalently

\[
f(x+v) = f(x) + \langle g, v\rangle + o(\|v\|)
\]

as \(v \to 0\). Here the vector \(g\) is \(\operatorname{gradient} f x\). The completeness assumption on \(E\) is part of the Hilbert-space setting in which the Riesz representative of a continuous linear functional is available.

## Lean proof
```lean
h.contDiff.differentiable_one.differentiableAt.hasGradientAt
```

## Proof explanation
The proof is a single term-mode composition of four steps; there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain.

First, the projection `h.contDiff` extracts from the hypothesis \(h : \operatorname{IsC11} f L\) the assertion that \(f\) is \(C^1\), Lean type \(\operatorname{ContDiff} \mathbb{R} 1 f\). Mathematically, this says \(f\) has a Fréchet derivative at every point and that this derivative depends continuously on the point. The rest of the bundle \(\operatorname{IsC11} f L\), including any role played by \(L\), is not used in this step.

Second, the lemma `ContDiff.differentiable_one` is applied to that \(C^1\) assertion. Its visible consequence here is \(\operatorname{Differentiable} \mathbb{R} f\), meaning \(f\) is differentiable everywhere. The mathematical content is the standard implication that continuous differentiability of order one implies ordinary differentiability at every point.

Third, applying `.differentiableAt` to this global differentiability at the given point \(x\) gives \(\operatorname{DifferentiableAt} \mathbb{R} f x\). This is the local assertion that \(f\) is differentiable at the particular point \(x\), so the Fréchet derivative \(Df(x)\) exists as a continuous linear map \(E \to \mathbb{R}\).

Finally, the lemma `DifferentiableAt.hasGradientAt` takes this local differentiability proof and returns

\[
\operatorname{HasGradientAt} f (\operatorname{gradient} f x) x.
\]

Its mathematical meaning is that for a differentiable real-valued function on a real inner product space, the Riesz representative of the Fréchet derivative \(Df(x)\) is precisely the vector \(\operatorname{gradient} f x\). Therefore the derivative is represented by \(\operatorname{gradient} f x\), which is exactly the desired gradient assertion. The final term has the required type, so the proof is complete. Only the \(C^1\) part of \(h\) is used; no Lipschitz estimate involving \(L\) is invoked.

