## Source file
`Nesterov_Accelerated_gradient_1983/items/def_1.lean`

## Lean statement
```lean
structure ExtremalProblem (m : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Q : Set E
  Q_convex : Convex ℝ Q
  Q_closed : IsClosed Q
  F : EuclideanSpace ℝ (Fin m) → ℝ
  F_convex : ConvexOn ℝ Set.univ F
  F_homogeneous : PositivelyHomogeneous F
  f : Fin m → E → ℝ
  f_convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  f_continuouslyDifferentiable : ∀ i, ContDiff ℝ 1 (f i)
  solutionSet : Set E
  solutions_nonempty : solutionSet.Nonempty
  solution_iff : ∀ x, x ∈ solutionSet ↔ x ∈ Q ∧
    ∀ z ∈ Q, F (WithLp.toLp 2 (fun i => f i x)) ≤ F (WithLp.toLp 2 (fun i => f i z))
  negative_multiplier_linear : ∀ l ∈ subdifferential (fun y => (F y : EReal)) 0, ∀ i,
    l i < 0 → ∃ g : E →ₗ[ℝ] ℝ, ∀ x, f i x = g x
```

## Statement explanation
The declaration introduces a bundled record type `ExtremalProblem` depending on a natural number \(m\) and on a type \(E\) equipped with `[NormedAddCommGroup E]` and `[InnerProductSpace ℝ E]`. Thus \(E\) is a real inner product space with its induced norm; no completeness of \(E\) is assumed by this declaration. The number \(m\) indexes a finite family of component functions.

The fields record the following data and properties.

- \(Q\subseteq E\) is the feasible set. The field `Q_convex` states that \(Q\) is convex over \(\mathbb R\): for all \(x,y\in Q\) and all \(t\in[0,1]\), one has \(t x+(1-t)y\in Q\). The field `Q_closed` states that \(Q\) is closed in the norm topology on \(E\).

- \(F:\mathbb R^m\to\mathbb R\), written in Lean as `EuclideanSpace ℝ (Fin m) → ℝ`, is the objective function on the space of values of the component functions. The field `F_convex` says that \(F\) is convex on all of \(\mathbb R^m\):
  \[
  F(t y+(1-t)z)\le tF(y)+(1-t)F(z)
  \]
  for all \(y,z\in\mathbb R^m\) and \(t\in[0,1]\). The field `F_homogeneous` says that \(F\) is positively homogeneous, i.e. scaling the argument by a nonnegative real scalar scales the value by the same scalar.

- \(f_i:E\to\mathbb R\) for \(i\in\operatorname{Fin} m\) is a finite family of real-valued functions on \(E\). Each `f i` is convex on all of \(E\), and each `f i` is of differentiability class \(C^1\), recorded by `ContDiff ℝ 1`.

- `solutionSet` is a subset \(S\subseteq E\). The field `solutions_nonempty` asserts that \(S\) is nonempty.

- The field `solution_iff` gives the exact characterization of the solution set: for every \(x\in E\),
  \[
  x\in S
  \iff
  x\in Q
  \ \text{and}\ 
  \forall z\in Q,\quad
  F\bigl((f_i(x))_{i\in\operatorname{Fin} m}\bigr)
  \le
  F\bigl((f_i(z))_{i\in\operatorname{Fin} m}\bigr).
  \]
  Here `WithLp.toLp 2 (fun i => f i x)` is the Euclidean vector in \(\mathbb R^m\) whose \(i\)-th coordinate is \(f_i(x)\). Thus \(S\) is exactly the set of feasible points \(x\in Q\) that globally minimize the composite objective
  \[
  x\mapsto F\bigl((f_i(x))_{i\in\operatorname{Fin} m}\bigr)
  \]
  over \(Q\).

- The field `negative_multiplier_linear` concerns the subdifferential at the origin of the extended-real-valued function
  \[
  y\mapsto (F(y):\overline{\mathbb R}),
  \]
  where \(\overline{\mathbb R}\) is `EReal`, the extended real line. In the inner-product setting, membership
  \[
  l\in \partial\bigl(y\mapsto (F(y):\overline{\mathbb R})\bigr)(0)
  \]
  means that \(l\in\mathbb R^m\) is a subgradient at the origin, i.e. it satisfies the subgradient inequality
  \[
  (F(0):\overline{\mathbb R})+\langle l,y\rangle
  \le
  (F(y):\overline{\mathbb R})
  \]
  for all \(y\in\mathbb R^m\), interpreted in the extended-real order. The field says that for every such subgradient \(l\), for every index \(i\), if the \(i\)-th coordinate satisfies \(l_i<0\), then the corresponding function \(f_i\) is linear:
  \[
  \exists\, g:E\to\mathbb R\ \text{\(\mathbb R\)-linear such that}\ \forall x\in E,\ f_i(x)=g(x).
  \]
  In other words, a negative multiplier coordinate forces the associated component function to be a linear functional on \(E\). The field itself records only the existence of an algebraic real-linear map \(g\); it does not separately state continuity of \(g\).

Overall, the structure packages an optimization problem with a convex closed feasible set, a convex positively homogeneous objective on the vector of component values, a finite family of convex \(C^1\) functions, a nonempty solution set that is exactly the set of feasible minimizers of the composite objective, and a negative-multiplier linearity condition for subgradients of \(F\) at the origin.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure` declaration, so Lean introduces a record type together with its fields rather than proving a theorem. The fields of proposition type, such as `Q_convex`, `Q_closed`, `F_convex`, `F_homogeneous`, `f_convex`, `f_continuouslyDifferentiable`, `solutions_nonempty`, `solution_iff`, and `negative_multiplier_linear`, are proof obligations that any future inhabitant of `ExtremalProblem m E` must supply. None of them is proved here. Consequently, there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named lemmas or theorems are invoked in the source. The mathematical content is entirely the specification of the fields described in the first section.

