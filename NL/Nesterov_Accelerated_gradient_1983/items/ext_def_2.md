## Source file
`Nesterov_Accelerated_gradient_1983/items/ext_def_2.lean`

## Lean statement
```lean
lemma mem_convexSubdifferential_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (u l : E) :
    l ∈ subdifferential (fun y => (F y : EReal)) u ↔
      ∀ v, F u + inner ℝ l (v - u) ≤ F v
```

## Statement explanation
The lemma `mem_convexSubdifferential_iff` is stated in a real inner product space \(E\), equipped in Lean with a normed additive commutative group structure and an inner product over \(\mathbb R\). It takes a real-valued function \(F:E\to\mathbb R\) and points \(u,l\in E\). Let \(\widetilde F:E\to\mathrm{EReal}\) be the extended-real-valued function defined by
\[
\widetilde F(y)=(F(y):\mathrm{EReal}),
\]
where the notation means that the real number \(F(y)\) is coerced into the extended real numbers. The left-hand side of the equivalence is
\[
l\in \partial \widetilde F(u),
\]
that is, \(l\) belongs to the subdifferential of the extended-real-valued function \(\widetilde F\) at \(u\). The right-hand side is
\[
\forall v\in E,\qquad F(u)+\langle l,v-u\rangle_{\mathbb R}\le F(v).
\]
Thus the lemma says that a point \(l\) is a subgradient of the extended-real version of \(F\) at \(u\) exactly when it satisfies the usual subgradient inequality for the real-valued function \(F\) at \(u\), tested against every \(v\in E\). Unfolding the subdifferential membership as used in the proof gives the equivalent extended-real inequality
\[
\forall v\in E,\qquad
\bigl(\langle v-u,l\rangle_{\mathbb R}:\mathrm{EReal}\bigr)
+(F(u):\mathrm{EReal})
\le (F(v):\mathrm{EReal}).
\]
The proof converts this to the displayed real inequality using symmetry of the real inner product and commutativity of addition. The statement itself contains no convexity hypothesis on \(F\); it is a bridge between extended-real subdifferential membership and the real-valued subgradient inequality.

## Lean proof
```lean
by
  constructor <;> intro h v
  · have hv := h v
    change (⟪v - u, l⟫_ℝ : EReal) + (F u : EReal) ≤ (F v : EReal) at hv
    norm_cast at hv
    simpa [real_inner_comm, add_comm] using hv
  · change (⟪v - u, l⟫_ℝ : EReal) + (F u : EReal) ≤ (F v : EReal)
    have hreal : ⟪v - u, l⟫_ℝ + F u ≤ F v := by
      simpa [real_inner_comm, add_comm] using h v
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact hreal
```

## Proof explanation
The proof begins with `by constructor <;> intro h v`. The tactic `constructor` splits the iff into two implications. The combinator `<;>` applies the following tactic to both resulting goals. In the forward direction, \(h\) is the hypothesis \(l\in\partial \widetilde F(u)\), and \(v\) is an arbitrary test point; the goal is the real inequality \(F(u)+\langle l,v-u\rangle_{\mathbb R}\le F(v)\). In the reverse direction, \(h\) is the universal real inequality \(\forall v,\ F(u)+\langle l,v-u\rangle_{\mathbb R}\le F(v)\), and \(v\) is the arbitrary test point coming from unfolding membership in the subdifferential.

For the forward direction, the proof first uses `have hv := h v`. Since membership in `subdifferential` unfolds to a universal statement over test points, applying \(h\) to \(v\) yields the extended-real inequality
\[
\bigl(\langle v-u,l\rangle_{\mathbb R}:\mathrm{EReal}\bigr)
+(F(u):\mathrm{EReal})
\le (F(v):\mathrm{EReal}).
\]
The command `change ... at hv` replaces `hv` by this definitionally equal expression, exposing the inequality hidden inside the subdifferential membership. Next, `norm_cast at hv` normalizes the coercions from \(\mathbb R\) to \(\mathrm{EReal}\). In this situation it converts the extended-real inequality into the real inequality
\[
\langle v-u,l\rangle_{\mathbb R}+F(u)\le F(v).
\]
This uses the fact that addition of two coerced real numbers agrees with the coercion of their real sum, and that the order between two real coercions in \(\mathrm{EReal}\) agrees with the original real order. Finally, `simpa [real_inner_comm, add_comm] using hv` proves the goal
\[
F(u)+\langle l,v-u\rangle_{\mathbb R}\le F(v).
\]
Here `real_inner_comm` replaces \(\langle v-u,l\rangle_{\mathbb R}\) by \(\langle l,v-u\rangle_{\mathbb R}\), using symmetry of the real inner product, and `add_comm` commutes the addition so that the left side matches \(F(u)+\langle l,v-u\rangle_{\mathbb R}\).

For the reverse direction, after `intro h v` the goal is the unfolded subdifferential inequality in \(\mathrm{EReal}\):
\[
\bigl(\langle v-u,l\rangle_{\mathbb R}:\mathrm{EReal}\bigr)
+(F(u):\mathrm{EReal})
\le (F(v):\mathrm{EReal}).
\]
The `change` command records exactly this goal. The proof then establishes the real inequality
\[
\langle v-u,l\rangle_{\mathbb R}+F(u)\le F(v)
\]
by `have hreal : ... := by simpa [real_inner_comm, add_comm] using h v`. Indeed, \(h v\) is
\[
F(u)+\langle l,v-u\rangle_{\mathbb R}\le F(v),
\]
and the simplifications using symmetry of the real inner product and commutativity of addition turn it into the displayed inequality with \(\langle v-u,l\rangle_{\mathbb R}+F(u)\) on the left.

It remains to convert this real inequality back into the extended-real goal. The proof uses `rw [← EReal.coe_add, EReal.coe_le_coe_iff]`. The first rewrite, using `EReal.coe_add` in reverse, combines the two separate coercions
\[
\bigl(\langle v-u,l\rangle_{\mathbb R}:\mathrm{EReal}\bigr)
+(F(u):\mathrm{EReal})
\]
into the single coercion
\[
\bigl(\langle v-u,l\rangle_{\mathbb R}+F(u):\mathrm{EReal}\bigr).
\]
The second rewrite, using `EReal.coe_le_coe_iff`, removes the coercions from the inequality: for real numbers \(a,b\), one has \((a:\mathrm{EReal})\le(b:\mathrm{EReal})\) if and only if \(a\le b\). The goal is therefore reduced to precisely the real inequality `hreal`, and `exact hreal` finishes the proof.

