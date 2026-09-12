## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/ext_thm_4.lean`

## Lean statement
```lean
abbrev ext_thm_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (gradf : H → H) (L : ℝ) (hL : 0 < L)
    (hconv : IsConvex f) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x, HasGradientAt f (gradf x) x)
    (hlip : LipschitzWith (Real.toNNReal L) gradf) :
    CocoerciveOn (1 / L) Set.univ (fun x : Set.univ => gradf x) :=
  baillon_haddad f gradf L hL (isConvexOn_univ_of_IsConvex hconv) hdiff hgrad hlip
```

## Statement explanation
`ext_thm_4` is an abbreviation stating a form of the Baillon–Haddad theorem for a real Hilbert space. The ambient space $H$ is assumed to be a complete real inner product space, i.e. a real Hilbert space: it has a normed additive commutative group structure, an inner product over $\mathbb R$, and completeness. The data are a function $f : H \to \mathbb R$, a map $\mathrm{gradf} : H \to H$, and a real number $L$ with $0 < L$. The hypotheses say:

- `hconv : IsConvex f`: the function $f$ is convex.
- `hdiff : Differentiable ℝ f`: $f$ is differentiable over $\mathbb R$.
- `hgrad : ∀ x, HasGradientAt f (gradf x) x`: for every point $x \in H$, the vector $\mathrm{gradf}(x)$ is a gradient of $f$ at $x$. Concretely, the derivative of $f$ at $x$ is the continuous linear functional

  $$
  v \mapsto \langle \mathrm{gradf}(x), v\rangle.
  $$

- `hlip : LipschitzWith (Real.toNNReal L) gradf`: the map $\mathrm{gradf}$ is Lipschitz with constant $\mathrm{Real.toNNReal} L$. Since $L>0$, this is the usual condition

  $$
  \|\mathrm{gradf}(x)-\mathrm{gradf}(y)\|
  \le L\,\|x-y\|
  $$

  for all $x,y \in H$.

The conclusion is

$$
\mathrm{CocoerciveOn}\!\left(\frac{1}{L},\ \mathrm{Set.univ},\ 
  \bigl(x \mapsto \mathrm{gradf}(x)\bigr)\right).
$$

Here the function is written on the subtype `Set.univ`, which is canonically identified with all of $H$. Thus the conclusion says that $\mathrm{gradf}$ is $\frac{1}{L}$-cocoercive on all of $H$: for all $x,y \in H$,

$$
\frac{1}{L}\|\mathrm{gradf}(x)-\mathrm{gradf}(y)\|^2
\le
\bigl\langle \mathrm{gradf}(x)-\mathrm{gradf}(y),\ x-y\bigr\rangle .
$$

So the declaration says: if $f$ is convex, differentiable, has gradient $\mathrm{gradf}$ everywhere, and $\mathrm{gradf}$ is $L$-Lipschitz, then $\mathrm{gradf}$ is $\frac{1}{L}$-cocoercive everywhere.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof body. The declaration is an `abbrev`, so its content is the defining term

```lean
baillon_haddad f gradf L hL (isConvexOn_univ_of_IsConvex hconv) hdiff hgrad hlip
```

which is directly assigned the required type. No tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur.

Step by step:

1. The term first evaluates

   ```lean
   isConvexOn_univ_of_IsConvex hconv
   ```

   from the hypothesis `hconv : IsConvex f`. The visible mathematical consequence is that $f$ is convex on the whole space, expressed in the form `ConvexOn ℝ Set.univ f`. In ordinary language, the global convexity of $f$ supplied by `IsConvex f` is converted into convexity on the set `Set.univ`, which is the form expected by the Baillon–Haddad result.

2. The result of that conversion is passed to `baillon_haddad`, together with `f`, `gradf`, `L`, the positivity proof `hL : 0 < L`, the differentiability proof `hdiff`, the gradient property `hgrad`, and the Lipschitz hypothesis `hlip`.

3. The visible consequence of applying `baillon_haddad` to these arguments is exactly the target conclusion:

   $$
   \mathrm{CocoerciveOn}\!\left(\frac{1}{L},\ \mathrm{Set.univ},\ 
     \bigl(x \mapsto \mathrm{gradf}(x)\bigr)\right).
   $$

   Mathematically this is the Baillon–Haddad implication: a convex differentiable function whose gradient is $L$-Lipschitz has a $\frac{1}{L}$-cocoercive gradient. The positivity assumption $0<L$ makes $\frac{1}{L}$ the intended positive cocoercivity modulus and makes $\mathrm{Real.toNNReal} L = L$ in the Lipschitz hypothesis.

4. The function `fun x : Set.univ => gradf x` is just $\mathrm{gradf}$ viewed as a function on the subtype of elements of `Set.univ`. Since `Set.univ` contains every element of $H$, this is the same as saying that the cocoercivity inequality holds globally on $H$.

Thus the abbreviation is a wrapper: it specializes the Baillon–Haddad theorem to the case where convexity is given as `IsConvex f` rather than directly as `ConvexOn ℝ Set.univ f`.

