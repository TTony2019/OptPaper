## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/rem_1.lean`

## Lean statement
```lean
theorem remark_3_1 {n : ℕ}
    (f fstar : EuclideanSpace ℝ (Fin n) → EReal) (x y : EuclideanSpace ℝ (Fin n))
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (hproper : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f) (hconjugate : fstar = ERealFunction.conjugate f) :
    (y ∈ ERealFunction.subdifferential f x ↔ f x + fstar y = (inner ℝ y x : EReal)) ∧
      (f x + fstar y = (inner ℝ y x : EReal) ↔
        x ∈ ERealFunction.subdifferential fstar y)
```

## Statement explanation
The declaration is a theorem about two functionals \(f\) and \(f^\ast\) on a finite-dimensional real Euclidean space, with values in the extended real numbers. Here \(n:\mathbb{N}\) is the dimension, and the underlying space is \(\mathbb{R}^n\), represented as `EuclideanSpace ℝ (Fin n)`. The variables \(x\) and \(y\) are points in this Euclidean space. The functions \(f\) and `fstar` are arbitrary extended-real-valued functions on this space. The hypotheses are:

- `hconvex`: the epigraph of \(f\) is convex, so \(f\) is a convex function.
- `hproper`: \(f\) is a proper extended-real-valued function, meaning it does not take the value \(-\infty\) and is not identically \(+\infty\).
- `hlsc`: \(f\) is lower semicontinuous.
- `hconjugate`: `fstar` equals the Fenchel conjugate of \(f\). In symbols, 
  \[
  f^\ast(y)=\sup_z \bigl(\langle y,z\rangle-f(z)\bigr),
  \]
  with values in the extended real numbers.

The conclusion is a conjunction of two equivalences. The first equivalence says that \(y\) is a subgradient of \(f\) at \(x\), written \(y\in \partial f(x)\), if and only if the Fenchel equality
\[
f(x)+f^\ast(y)=\langle y,x\rangle
\]
holds, where the inner product is viewed as an extended real number. The second equivalence says that exactly the same Fenchel equality holds if and only if \(x\) is a subgradient of the conjugate function \(f^\ast\) at \(y\), written \(x\in \partial f^\ast(y)\).

## Lean proof
```lean
by
  constructor
  · exact fenchel_equality_iff_subgradient f fstar x y hproper hconjugate
  · constructor
    · exact fenchel_equality_imp_dual_subgradient f fstar x y hproper hconjugate
    · intro hsub
      exact fenchel_dual_subgradient_imp_equality f fstar x y hconvex hproper hlsc hconjugate hsub
```

## Proof explanation
The proof is a short composition of previously established lemmas. It begins with `constructor`, which splits the top-level conjunction into its two stated equivalences.

For the first conjunct, the goal is
\[
y\in \partial f(x)\iff f(x)+f^\ast(y)=\langle y,x\rangle.
\]
The proof applies `exact fenchel_equality_iff_subgradient f fstar x y hproper hconjugate`. This means the goal is precisely the statement of that lemma, using the hypotheses that \(f\) is proper and that `fstar` is its conjugate.

For the second conjunct, the goal is
\[
f(x)+f^\ast(y)=\langle y,x\rangle \iff x\in \partial f^\ast(y).
\]
The proof again uses `constructor`, splitting this equivalence into its forward implication and its reverse implication.

The forward implication is handled by
`exact fenchel_equality_imp_dual_subgradient f fstar x y hproper hconjugate`. This lemma says that if the Fenchel equality holds, then \(x\) is a subgradient of the conjugate function at \(y\), i.e. \(x\in\partial f^\ast(y)\).

For the reverse implication, the proof uses `intro hsub`, introducing the hypothesis `hsub : x ∈ ERealFunction.subdifferential fstar y`. Under this assumption, the goal becomes the Fenchel equality
\[
f(x)+f^\ast(y)=\langle y,x\rangle.
\]
The proof closes this goal with
`exact fenchel_dual_subgradient_imp_equality f fstar x y hconvex hproper hlsc hconjugate hsub`.
This lemma states that, under the additional assumptions that \(f\) is convex and lower semicontinuous, if \(x\in\partial f^\ast(y)\) then the Fenchel equality holds.

Thus every subgoal is solved by applying an existing lemma. The commands used are `constructor` to disassemble conjunctions and equivalences, `exact` to provide a theorem that matches the current goal, and `intro` to name the hypothesis of an implication. The commands `rw`, `simp`, and `linarith` are not used in this proof.

