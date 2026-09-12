## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_thm_2.lean`

## Lean statement
```lean
theorem convex_firstOrder_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ u, HasGradientAt f (gradient f u) u) (u v : E) :
    f u + inner ℝ (gradient f u) (v - u) ≤ f v
```

## Statement explanation
The theorem `convex_firstOrder_inequality` is stated in a real inner product space $E$ which is also assumed complete, so $E$ is a real Hilbert space. The function is $f : E \to \mathbb{R}$. The hypothesis `hconv : ConvexOn ℝ Set.univ f` says that $f$ is convex on the whole space $E$. The hypothesis `hgrad : ∀ u, HasGradientAt f (gradient f u) u` says that at every point $u \in E$, the function $f$ has gradient `gradient f u`; equivalently, the Fréchet derivative of $f$ at $u$ is the continuous linear functional

$$
h \mapsto \langle \mathrm{gradient} f u, h\rangle .
$$

For arbitrary points $u,v \in E$, the conclusion is

$$
f(u) + \langle \mathrm{gradient} f u, v-u\rangle \le f(v).
$$

This is the first-order lower bound for a convex differentiable function: the tangent-plane approximation at $u$ lies below the graph of $f$ at the point $v$.

## Lean proof
```lean
by
  let φ : ℝ → ℝ := f ∘ AffineMap.lineMap u v
  have hφconvex : ConvexOn ℝ Set.univ φ := by
    simpa [φ] using hconv.comp_affineMap (AffineMap.lineMap u v)
  have hpath : HasDerivAt (fun t : ℝ ↦ u + t • (v - u)) (v - u) 0 := by
    convert (hasDerivAt_const (𝕜 := ℝ) 0 u).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (v - u)) using 1
    all_goals simp
  have houter : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f u))
      ((fun t : ℝ ↦ u + t • (v - u)) 0) := by
    simpa using (hgrad u).hasFDerivAt
  have hφderiv : HasDerivAt φ (inner ℝ (gradient f u) (v - u)) 0 := by
    simpa [φ, Function.comp_def, AffineMap.lineMap_apply, add_comm, one_smul,
      add_zero, InnerProductSpace.toDual_apply_apply] using
      houter.comp_hasDerivAt 0 hpath
  have hslope := hφconvex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hφderiv
  have hdir : inner ℝ (gradient f u) (v - u) ≤ f v - f u := by
    simpa [φ, slope, Function.comp_def, AffineMap.lineMap_apply, zero_smul,
      one_smul, zero_add, add_zero] using hslope
  linarith
```

## Proof explanation
The proof first restricts $f$ to the line segment from $u$ to $v$. It defines

$$
\varphi : \mathbb{R} \to \mathbb{R}, \qquad \varphi(t) = f(u+t(v-u)).
$$

In Lean this is written as `φ := f ∘ AffineMap.lineMap u v`, using the affine line map through $u$ and $v$, which sends $0$ to $u$ and $1$ to $v$.

The first step proves `hφconvex : ConvexOn ℝ Set.univ φ`. The invocation `hconv.comp_affineMap (AffineMap.lineMap u v)` uses the fact that composing a convex function with an affine map preserves convexity. Since `hconv` says $f$ is convex on all of $E$, the composed function $\varphi$ is convex on all of $\mathbb{R}$. The `simpa [φ]` unfolds the definition of $\varphi$ so that the resulting statement matches the goal.

Next, `hpath` establishes that the path

$$
t \mapsto u+t(v-u)
$$

has derivative $v-u$ at $t=0$. The proof uses `hasDerivAt_const` for the constant part $t \mapsto u$, whose derivative is $0$, and `hasDerivAt_id` for $t \mapsto t$, whose derivative is $1$. The method `.smul_const (v-u)` multiplies the identity function by the constant vector $v-u$, giving derivative $1 \cdot (v-u)$. Adding this to the constant function gives derivative

$$
0 + 1\cdot(v-u) = v-u.
$$

The `convert` and `simp` steps only reconcile the exact Lean expression of the function with $u+t(v-u)$.

The step `houter` converts the gradient assumption at $u$ into Fréchet differentiability. From `hgrad u`, the lemma `.hasFDerivAt` gives that $f$ has Fréchet derivative

$$
\mathrm{InnerProductSpace.toDual} (\mathrm{gradient} f u)
$$

at $u$. The map `InnerProductSpace.toDual` sends a vector $g$ to the continuous linear functional $h \mapsto \langle g,h\rangle$. Thus `houter` says that the derivative of $f$ at $u$, as a linear map, is the inner-product pairing with `gradient f u`. The `simpa` only rewrites the point $u$ as the value of the path at $0$.

The step `hφderiv` applies the chain rule. The result `houter.comp_hasDerivAt 0 hpath` says that the composition $f \circ (t \mapsto u+t(v-u))$ is differentiable at $0$, with derivative obtained by applying the Fréchet derivative of $f$ at $u$ to the derivative of the path at $0$, namely $v-u$. Therefore the derivative is

$$
(\mathrm{InnerProductSpace.toDual} (\mathrm{gradient} f u))(v-u).
$$

The lemma `InnerProductSpace.toDual_apply_apply` evaluates this as

$$
\langle \mathrm{gradient} f u, v-u\rangle.
$$

After unfolding $\varphi$ and the line map, this gives

$$
\mathrm{HasDerivAt} \varphi
  \bigl(\langle \mathrm{gradient} f u, v-u\rangle\bigr) 0.
$$

The crucial convexity estimate is

```math
\texttt{hslope} := \texttt{hφconvex.le\_slope\_of\_hasDerivAt}.
```

This theorem says that for a convex real function $\varphi$, if $0\lt 1$, then the derivative of $\varphi$ at the left endpoint $0$ is bounded above by the secant slope from $0$ to $1$:

```math
\varphi'(0) \le \mathrm{slope} \varphi\,0\,1.
```

The two `by simp` arguments prove that $0$ and $1$ lie in the domain `Set.univ`, and `zero_lt_one` supplies the inequality $0\lt 1$. Together with `hφderiv`, this yields

```math
\langle \mathrm{gradient} f u, v-u\rangle
  \le \mathrm{slope} \varphi\,0\,1.
```

The step `hdir` simplifies this slope. Since

$$
\varphi(0)=f(u), \qquad \varphi(1)=f(v),
$$

the slope is

```math
\mathrm{slope} \varphi\,0\,1
= \frac{\varphi(1)-\varphi(0)}{1-0}
= f(v)-f(u).
```

Thus `hdir` states

$$
\langle \mathrm{gradient} f u, v-u\rangle
  \le f(v)-f(u).
$$

Finally, `linarith` performs the elementary linear rearrangement of this inequality to the target:

$$
f(u) + \langle \mathrm{gradient} f u, v-u\rangle \le f(v).
$$

This completes the proof of the first-order convex inequality.

