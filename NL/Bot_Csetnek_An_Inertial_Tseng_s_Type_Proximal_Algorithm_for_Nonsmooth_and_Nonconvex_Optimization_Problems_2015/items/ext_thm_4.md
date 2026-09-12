## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_thm_4.lean`

## Lean statement
```lean
theorem semialgebraic_objective_yields_KL_H {m : Nat}
    (g : EuclideanSpace m -> EReal) (M2 : Real)
    (_hg : IsSemiAlgebraicEReal g)
    (hbridge : SemialgebraicToProductKL g M2)
    : ProductKLFunction
      (fun z : EuclideanSpace m × EuclideanSpace m =>
        erealAddReal (g z.1) (M2 * ‖z.1 - z.2‖ ^ 2))
```

## Statement explanation
Let $m$ be a natural number, let $E = \text{EuclideanSpace } m$, and let $g : E \to \overline{\mathbb{R}}$ be an extended-real-valued function. Let $M_2$ be a real number. The declaration has two hypotheses. The first, `_hg`, is the assertion `IsSemiAlgebraicEReal g`, meaning that $g$ is semialgebraic in the extended-real-valued sense used locally. The second, `hbridge`, has type `SemialgebraicToProductKL g M2`. The source does not expand the definitions of these local predicates, so we do not attribute any further content to them. The proof shows that `hbridge` is used as an implication-like bridge: it can be applied to the semialgebraicity evidence `_hg`.

The conclusion is that the function

$$
F(x,y) = \operatorname{erealAddReal}\bigl(g(x),\, M_2 \|x-y\|^2\bigr)
$$

on $E \times E$, taking values in $\overline{\mathbb{R}}$, is a `ProductKLFunction`. Here $x$ and $y$ are the two components of a pair $z : E \times E$, and $\|x-y\|^2$ is the squared Euclidean distance between $x$ and $y$. The term $M_2 \|x-y\|^2$ is real, and `erealAddReal` adds it to the extended-real value $g(x)$, producing an extended-real value. Thus the theorem says, in ordinary language: if $g$ is semialgebraic and if the local bridge statement `SemialgebraicToProductKL g M2` is available, then the product function $F(x,y)=g(x)+M_2\|x-y\|^2$ has the product KL property. No other assumptions are made and no other conclusion is asserted.

## Lean proof
```lean
by
  exact hbridge _hg
```

## Proof explanation
The proof is the single term `by exact hbridge _hg`. The theorem binders for $m$, $g$, $M_2$, `_hg`, and `hbridge` are already in the local context, so no `intro` is needed. The goal is exactly the `ProductKLFunction` assertion for $F$. The hypothesis `hbridge` is a proof of the local bridge statement `SemialgebraicToProductKL g M2`; in this application it behaves as a function from a proof of `IsSemiAlgebraicEReal g` to the desired `ProductKLFunction` conclusion. Applying it to `_hg`, which is precisely a proof of `IsSemiAlgebraicEReal g`, therefore produces a term of the goal type. The tactic `exact` closes the goal by verifying that `hbridge _hg` has exactly that type. Mathematically this is modus ponens: the bridge hypothesis supplies the implication from semialgebraicity of $g$ to the KL property of $F$, and `_hg` supplies its premise. There are no rewrites (`rw`), simplifications (`simp`), arithmetic calls (`linarith`), or additional named lemmas. The source contains no cited theorem statements for this proof, and the proof indeed uses only the local hypothesis `hbridge` together with its argument `_hg`.

