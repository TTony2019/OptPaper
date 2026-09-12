## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/ext_def_4.lean`

## Lean statement
```lean
theorem continuous_gradient_of_contDiff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f)
```

## Statement explanation
The declaration is about a complete real inner product space $H$, i.e. a real Hilbert space, and a function $f:H\to\mathbb{R}$. The hypothesis $\mathrm{ContDiff}_{\mathbb{R}} 1 f$ means that $f$ is continuously differentiable of order $1$ over $\mathbb{R}$: its Fréchet derivative exists and the derivative map is continuous. The conclusion is that the gradient map of $f$, denoted in Lean by `gradient f`, is continuous as a map $H\to H$.

Mathematically, for each $x\in H$, the Fréchet derivative $\mathrm{fderiv}_{\mathbb{R}} f(x)$ is a continuous linear functional on $H$, i.e. an element of $\mathcal L(H,\mathbb{R})$. Since $H$ is a complete real inner product space, Riesz representation identifies each such functional uniquely with a vector of $H$. The gradient $\nabla f(x)$ is exactly that representing vector, so that, up to the chosen real inner-product convention,

$$
\langle \nabla f(x), v\rangle = \mathrm{fderiv}_{\mathbb{R}} f(x)(v)
$$

for every $v\in H$. Thus the statement says: if $f$ is $C^1$, then the map $x\mapsto \nabla f(x)$ is continuous from $H$ to $H$.

## Lean proof
```lean
by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  simpa [gradient, Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.comp hfd
```

## Proof explanation
The proof begins with

```lean
have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
```

Here $\mathrm{fderiv}_{\mathbb{R}} f$ is the Fréchet derivative map

$$
x \mapsto \mathrm{fderiv}_{\mathbb{R}} f(x)\in \mathcal L(H,\mathbb{R}).
$$

The result `continuous_fderiv`, applied to the hypothesis $\mathrm{ContDiff}_{\mathbb{R}} 1 f$, gives continuity of this derivative map. The argument `(by norm_num)` discharges the numerical side condition that the differentiability order $1$ is nonzero. Thus `hfd` says exactly that the derivative map $Df$ is continuous.

Next the proof uses

```lean
(InnerProductSpace.toDual ℝ H).symm.continuous.comp hfd
```

The map $\mathrm{toDual}_{\mathbb{R},H}$ is the Riesz duality map from $H$ to its continuous dual $\mathcal L(H,\mathbb{R})$: it sends a vector to the continuous linear functional given by the inner product. Its inverse $(\mathrm{toDual}_{\mathbb{R},H})^{-1}$ sends a continuous linear functional back to the vector representing it. The field `.continuous` supplies the fact that this inverse map is continuous. Since `hfd` says that $x\mapsto \mathrm{fderiv}_{\mathbb{R}} f(x)$ is continuous into $\mathcal L(H,\mathbb{R})$, the general fact that a composition of continuous functions is continuous gives continuity of the composite map

$$
x \mapsto (\mathrm{toDual}_{\mathbb{R},H})^{-1}\bigl(\mathrm{fderiv}_{\mathbb{R}} f(x)\bigr).
$$

This composite is precisely the gradient map: it takes the derivative functional at $x$ and returns the unique vector representing it under Riesz duality.

Finally, the command

```lean
simpa [gradient, Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.comp hfd
```

uses simplification and then exactness. Unfolding `gradient` identifies $\nabla f(x)$ with the Riesz representative of $\mathrm{fderiv}_{\mathbb{R}} f(x)$, and unfolding `Function.comp_def` turns the composition

$$
(\mathrm{toDual}_{\mathbb{R},H})^{-1}\circ \mathrm{fderiv}_{\mathbb{R}} f
$$

into the explicit map

$$
x \mapsto (\mathrm{toDual}_{\mathbb{R},H})^{-1}\bigl(\mathrm{fderiv}_{\mathbb{R}} f(x)\bigr).
$$

Thus the previously constructed composed-continuity term has exactly the simplified form required to prove $\mathrm{Continuous}(\nabla f)$. The proof contains no explicit `intro`, `rw`, `simp`, `exact`, or `linarith` step; its main moves are the `have` establishing continuity of the derivative map and the final `simpa ... using` identifying that composition with the gradient.

