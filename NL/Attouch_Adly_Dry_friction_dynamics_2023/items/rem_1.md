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
The declaration states a Fenchel-duality equivalence for an extended-real-valued function on finite-dimensional Euclidean space. Let $n\in\mathbb N$, let

$$
f,\ f^* : \mathbb R^n \to \overline{\mathbb R}
$$

be extended-real-valued functions, and let $x,y\in \mathbb R^n$. Here $\mathbb R^n$ is the Lean type `EuclideanSpace ℝ (Fin n)`, and $\overline{\mathbb R}$ is `EReal`. The inner product $\langle y,x\rangle$ is the real inner product on $\mathbb R^n$, coerced into the extended reals.

The hypotheses are:

- `hconvex`: the epigraph of $f$ is convex over $\mathbb R$, i.e. $f$ is convex in the extended-real sense.
- `hproper`: $f$ is proper in the extended-real sense: it is not identically $+\infty$ and takes no value $-\infty$.
- `hlsc`: $f$ is lower semicontinuous as an extended-real-valued function.
- `hconjugate`: $f^*$ is the Fenchel conjugate of $f$, so for every $u\in\mathbb R^n$,

$$
f^*(u)=\sup_{z\in\mathbb R^n}\bigl(\langle u,z\rangle-f(z)\bigr).
$$

The conclusion is the conjunction of two biconditionals. First,

$$
y\in \partial f(x)
\quad\Longleftrightarrow\quad
f(x)+f^*(y)=\langle y,x\rangle,
$$

where $\partial f(x)$ denotes the subdifferential of $f$ at $x$. Second,

$$
f(x)+f^*(y)=\langle y,x\rangle
\quad\Longleftrightarrow\quad
x\in \partial f^*(y),
$$

where $\partial f^*(y)$ denotes the subdifferential of the conjugate $f^*$ at $y$. Thus the theorem says that, under the stated convexity, properness, lower semicontinuity, and conjugacy assumptions, the following three statements are equivalent:

$$
y\in \partial f(x),
\qquad
f(x)+f^*(y)=\langle y,x\rangle,
\qquad
x\in \partial f^*(y).
$$

The middle statement is equality in the Fenchel-Young inequality $f(x)+f^*(y)\ge \langle y,x\rangle$.

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
The proof begins with `constructor`, which splits the conjunctive goal into two subgoals: first the biconditional involving $y\in\partial f(x)$, and second the biconditional involving $x\in\partial f^*(y)$.

For the first subgoal,

$$
y\in \partial f(x)\ \Longleftrightarrow\ f(x)+f^*(y)=\langle y,x\rangle,
$$

the proof uses `exact fenchel_equality_iff_subgradient f fstar x y hproper hconjugate`. The cited lemma is stated for any real inner-product space $H$. It assumes that $f$ is proper and that $f^*$ is the Fenchel conjugate of $f$. Under those assumptions, it gives exactly the biconditional

$$
y\in \partial f(x)\ \Longleftrightarrow\ f(x)+f^*(y)=\langle y,x\rangle.
$$

Mathematically, this is the standard characterization of a subgradient by equality in the Fenchel-Young inequality: $y$ is a supporting slope of $f$ at $x$ precisely when the inequality

$$
f(x)+f^*(y)\ge \langle y,x\rangle
$$

is tight. This lemma does not require the convexity or lower semicontinuity hypotheses, so `hconvex` and `hlsc` are not passed to it. The `exact` command closes the first subgoal by supplying a term whose type is precisely that biconditional.

For the second subgoal,

$$
f(x)+f^*(y)=\langle y,x\rangle
\ \Longleftrightarrow\
x\in \partial f^*(y),
$$

the proof again uses `constructor`, splitting it into the forward implication and the backward implication.

In the forward direction, the goal is

$$
f(x)+f^*(y)=\langle y,x\rangle \ \Longrightarrow\ x\in \partial f^*(y).
$$

The proof uses
`exact fenchel_equality_imp_dual_subgradient f fstar x y hproper hconjugate`.
The cited lemma says that in any real inner-product space, if $f$ is proper and $f^*$ is its Fenchel conjugate, then the Fenchel equality

$$
f(x)+f^*(y)=\langle y,x\rangle
$$

implies that $x$ belongs to the subdifferential of $f^*$ at $y$:

$$
x\in \partial f^*(y).
$$

Here the unsupplied equality proof is exactly the premise of the implication, so `exact` produces the required function from the equality to the dual-subgradient membership. This proves the forward implication of the second biconditional.

In the backward direction, the proof first executes `intro hsub`, introducing the assumption

$$
hsub:\ x\in \partial f^*(y)
$$

and changing the goal to

$$
f(x)+f^*(y)=\langle y,x\rangle.
$$

It then uses
`exact fenchel_dual_subgradient_imp_equality f fstar x y hconvex hproper hlsc hconjugate hsub`.
The cited lemma assumes that the epigraph of $f$ is convex, that $f$ is proper, that $f$ is lower semicontinuous, that $f^*$ is the Fenchel conjugate of $f$, and that $x\in\partial f^*(y)$. Its conclusion is exactly

$$
f(x)+f^*(y)=\langle y,x\rangle.
$$

This is the nontrivial Fenchel-Moreau direction: convexity and lower semicontinuity make $f$ a closed convex proper function, so its double conjugate recovers $f$, and a subgradient of the conjugate yields equality in the Fenchel-Young relation. This proves the backward implication of the second biconditional. Together with the forward implication, it yields the second equivalence; together with the first equivalence, it proves the full conjunction.

No rewriting with `rw`, simplification with `simp`, or arithmetic reasoning with `linarith` occurs in this proof. The proof is a direct logical assembly of the three cited Fenchel-duality lemmas using `constructor`, `exact`, and `intro`.

