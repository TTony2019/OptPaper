## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_1.lean`

## Lean statement
```lean
theorem cocoercive_lipschitz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (beta : ℝ) (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)) :
    LipschitzWith ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ B
```

## Statement explanation
The declaration is stated for an arbitrary type $H$ carrying a normed additive commutative group structure and a real inner-product-space structure. The operator is $B:H\to H$, a possibly nonlinear map from $H$ to itself. The real parameter is $\beta$. The hypothesis `hB` says that $B$, viewed on the whole space $H$, is cocoercive with constant $\beta$:

$$
\text{`CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x)`}.
$$

In this proof, the only explicit consequence of `hB` that is used directly is `hB.pos`, which provides

$$
0<\beta.
$$

The conclusion asserts that $B$ is Lipschitz with constant $1/\beta$. In Lean, the Lipschitz constant must be a nonnegative real, so the conclusion packages the real number $1/\beta$ as

$$
\left\langle \frac1\beta,\; \text{a proof that }0\le \frac1\beta\right\rangle.
$$

That nonnegativity proof is `le_of_lt (one_div_pos.mpr hB.pos)`: from $0<\beta$ one gets $0<1/\beta$, and hence $0\le 1/\beta$. Mathematically, the theorem says that if $B$ is cocoercive on all of $H$ with positive parameter $\beta$, then $B$ is Lipschitz with constant $1/\beta$, i.e.

$$
\forall x,y\in H,\qquad
\operatorname{dist}(B x,B y)\le \frac1\beta\,\operatorname{dist}(x,y).
$$

Since $H$ is a normed group, this is the usual inequality

$$
\|B x-B y\|\le \frac1\beta\,\|x-y\|.
$$

## Lean proof
```lean
by
  have heq : Real.toNNReal (1 / beta) =
      ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩ :=
    NNReal.eq (Real.coe_toNNReal (1 / beta) (one_div_nonneg.mpr hB.pos.le))
  rw [← heq]
  exact cocoercive_implies_lipschitz B beta hB
```

## Proof explanation
The proof first compares two ways of representing the same nonnegative real number. The left side is `Real.toNNReal (1 / beta)`, the nonnegative truncation of $1/\beta$ as an element of $\mathbb{R}_{\ge 0}$. Since the proof knows $0<\beta$, it also knows $0\le \beta$, so `one_div_nonneg.mpr hB.pos.le` gives

$$
0\le \frac1\beta.
$$

Therefore the nonnegative truncation of $1/\beta$ is just $1/\beta$ itself. The auxiliary fact `Real.coe_toNNReal (1 / beta) (one_div_nonneg.mpr hB.pos.le)` states exactly that the underlying real number of `Real.toNNReal (1 / beta)` is $1/\beta$. The right side `⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩` is the bundled nonnegative real with value $1/\beta$ and proof $0\le 1/\beta$, so its underlying real value is also $1/\beta$. Applying `NNReal.eq` turns the equality of the underlying real numbers into equality of the nonnegative real numbers themselves. Thus the line

```lean
have heq : Real.toNNReal (1 / beta) =
    ⟨1 / beta, le_of_lt (one_div_pos.mpr hB.pos)⟩
```

establishes

$$
\operatorname{Real.toNNReal}\!\left(\frac1\beta\right)
=
\left\langle \frac1\beta,\; 0\le \frac1\beta\right\rangle
$$

as elements of $\mathbb{R}_{\ge 0}$.

Next, the target conclusion is

$$
\text{`LipschitzWith ⟨1 / beta, ...⟩ B`}.
$$

The command `rw [← heq]` rewrites the expression $\langle 1/\beta,\ldots\rangle$ in the goal to `Real.toNNReal (1 / beta)`, using the equality `heq` from right to left. The goal becomes

$$
\text{`LipschitzWith (Real.toNNReal (1 / beta)) B`}.
$$

This is precisely the conclusion of the cited theorem `cocoercive_implies_lipschitz`, which states that for any $A:H\to H$ and real $\beta$, if $A$ is cocoercive on all of $H$ with constant $\beta$, then $A$ is Lipschitz with constant `Real.toNNReal (1 / β)`. Specializing that theorem to $A=B$ and $\beta=\beta$, and supplying the hypothesis `hB`, the final command

```lean
exact cocoercive_implies_lipschitz B beta hB
```

closes the goal. Thus the theorem is proved by converting the explicit bundled Lipschitz constant $1/\beta$ into the equivalent `Real.toNNReal` form used by the general cocoercivity-to-Lipschitz theorem, then applying that general theorem.

