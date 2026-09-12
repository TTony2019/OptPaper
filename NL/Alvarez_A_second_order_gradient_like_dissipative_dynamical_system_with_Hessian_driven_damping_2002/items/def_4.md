## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/def_4.lean`

## Lean statement
```lean
def StronglyMonotoneOnBoundedSubsets (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → H) : Prop := ∀ R : ℝ, 0 < R → ∃ c : ℝ, 0 < c ∧ ∀ x y : H,
  max ‖x‖ ‖y‖ < R → c * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫
```

## Statement explanation
The declaration defines a predicate named `StronglyMonotoneOnBoundedSubsets`. Its context consists of a type \(H\), an additive commutative group structure with a norm on \(H\) given by `NormedAddCommGroup H`, and a real inner product space structure on \(H\) given by `InnerProductSpace ℝ H`. Thus \(H\) is equipped with a real inner product \(\langle \cdot,\cdot\rangle\) and an associated norm \(\|\cdot\|\). The statement does not assume completeness of \(H\). The argument \(G\) is an arbitrary map \(G:H\to H\); it is not assumed to be linear, continuous, differentiable, or monotone in any other sense.

The predicate is the proposition

\[
\forall R:\mathbb{R},\; 0<R \to \exists c:\mathbb{R},\; 0<c \wedge \forall x,y:H,\;
\max(\|x\|,\|y\|)<R \to c\,\|x-y\|^2 \le \langle Gx-Gy,x-y\rangle .
\]

In words: for every positive real radius \(R\), there exists a positive real constant \(c\), possibly depending on \(R\), such that for all \(x,y\in H\) satisfying \(\|x\|<R\) and \(\|y\|<R\), equivalently \(\max(\|x\|,\|y\|)<R\), the map \(G\) satisfies the strong monotonicity inequality

\[
\langle Gx-Gy,x-y\rangle \ge c\,\|x-y\|^2 .
\]

Thus \(G\) is strongly monotone with a positive modulus \(c\) on each open ball of radius \(R\) centered at the origin. The constant \(c\) is uniform over all pairs \(x,y\) inside that ball, but it may depend on the ball radius \(R\). Equivalently, the definition requires uniform strong monotonicity on every bounded subset, encoded here by the condition that both \(x\) and \(y\) lie in the open ball of radius \(R\). Since \(c>0\), the inequality says that the inner product \(\langle Gx-Gy,x-y\rangle\) dominates a positive multiple of the squared distance \(\|x-y\|^2\) throughout that bounded region.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration kind is `def`, so the text after `:=` is the defining body of the predicate `StronglyMonotoneOnBoundedSubsets`, not a proof of a theorem. Lean only checks that this body has type `Prop` and then binds the name `StronglyMonotoneOnBoundedSubsets` to that proposition.

No tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` appears, and no named theorem or local lemma is invoked. Accordingly, there are no proof steps to analyze and no cited mathematical result whose content must be specialized to the current variables. The entire mathematical content is the quantified strong-monotonicity condition described in the first section.

