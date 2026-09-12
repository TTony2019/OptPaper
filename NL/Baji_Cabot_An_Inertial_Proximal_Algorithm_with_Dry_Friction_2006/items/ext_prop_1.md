## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/ext_prop_1.lean`

## Lean statement
```lean
theorem interior_zero_iff_supportFunction (C : Set H) (hC : Convex ℝ C) :
    (0 ∈ interior C) ↔
      ∃ (α : ℝ), α > 0 ∧ ∀ x, supportFunction C x ≥ ((α * ‖x‖ : ℝ) : EReal)
```

## Statement explanation
The theorem `interior_zero_iff_supportFunction` is stated for a set $C\subseteq H$, together with a hypothesis named `hC` asserting that $C$ is convex over $\mathbb R$. Convexity here means that for every $x,y\in C$ and every $t\in[0,1]$, the convex combination $t x+(1-t)y$ again belongs to $C$. The ambient type $H$ is not detailed in the snippet, but the symbols used require the usual setting in which $\mathbb R$-convexity, the norm $\lVert\cdot\rVert$, the topological interior, and the support function all make sense. The point $0$ is the zero vector of $H$, and $0\in\operatorname{interior} C$ means that some open neighborhood of $0$ is contained in $C$.

The expression `supportFunction C x` denotes the support function of $C$ evaluated at $x$. Its values lie in `EReal`, the extended real numbers, so $h_C(x)$ may be finite or infinite. The right-hand side of the equivalence says that there exists a real number $\alpha$ with $\alpha>0$ such that, for every vector $x$, the extended-real support-function value at $x$ is at least the real number $\alpha\lVert x\rVert$, regarded as an extended real by the coercion $((\alpha * \lVert x\rVert : \mathbb R) : \mathrm{EReal})$. In ordinary notation, if $h_C(x)$ denotes the support function of $C$ at $x$, the theorem states

$$
0\in \operatorname{interior} C
\quad\Longleftrightarrow\quad
\exists \alpha>0,\ \forall x,\ h_C(x)\ge \alpha\lVert x\rVert ,
$$

where the final inequality is taken in the extended-real order. Thus the origin is an interior point of the convex set $C$ exactly when the support function of $C$ has a positive linear lower bound in every direction, uniformly in $x$. Since the comparison is in extended reals, values $h_C(x)=+\infty$ automatically satisfy the inequality.

## Lean proof
```lean
by
  sorry
```

## Proof explanation
The proof is not supplied. The proof field contains only Lean's `sorry` placeholder, which closes the goal without providing a mathematical argument. Consequently there are no proof steps to analyze: no use of the hypothesis that $C$ is convex, no argument that $0\in\operatorname{interior} C$ implies the existence of $\alpha>0$, and no converse argument from the lower bound $h_C(x)\ge \alpha\lVert x\rVert$ back to $0\in\operatorname{interior} C$. No named theorem or lemma is invoked, and there are no occurrences of tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`. The declaration therefore asserts the stated equivalence, but in the provided source its proof is omitted.

