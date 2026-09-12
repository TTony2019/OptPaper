## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/def_3.lean`

## Lean statement
```lean
def lassoObjective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (g : (n → ℝ) → EReal)
    (_hmn : Fintype.card m ≤ Fintype.card n)
    (_hconvex : ∀ (x y : n → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      g (a • x + b • y) ≤ (a : EReal) * g x + (b : EReal) * g y)
    (_hlsc : LowerSemicontinuous g) (_hproper : ERealFunction.IsProper g) : (n → ℝ) → EReal :=
  fun x ↦ ((1 / 2 : ℝ) * ‖A.mulVec x - b‖ ^ 2 : ℝ) + g x
```

## Statement explanation
The declaration `lassoObjective` defines a lasso-type objective function. Its parameters are: finite types $m$ and $n$; a real matrix $A : m \times n \to \mathbb{R}$, represented in Lean as `Matrix m n ℝ`; a vector $b : m \to \mathbb{R}$; and a regularizer $g : (n \to \mathbb{R}) \to \overline{\mathbb{R}}$, where $\overline{\mathbb{R}}$ is the extended real line. The unused hypotheses record the intended setting: $|m| \le |n|$, convexity of $g$, lower semicontinuity of $g$, and properness of $g$. Concretely, convexity says that for all $x,y \in \mathbb{R}^n$ and all $a,b \in \mathbb{R}$ with $a,b \ge 0$ and $a+b=1$,

$$
g(a x + b y) \le a g(x) + b g(y),
$$

where the scalars $a,b$ and the operations are interpreted in $\overline{\mathbb{R}}$. The conclusion is a function

$$
F : \mathbb{R}^n \to \overline{\mathbb{R}}
$$

defined by

$$
F(x) = \frac{1}{2}\|A x - b\|^2 + g(x),
$$

where $A x$ is the matrix-vector product `A.mulVec x`, $\|A x - b\|$ is the norm of the residual in $m \to \mathbb{R}$, the squared real least-squares term is embedded into $\overline{\mathbb{R}}$, and the final addition is addition in $\overline{\mathbb{R}}$. Thus the declaration packages the usual objective consisting of a half-squared data-fidelity term plus a general extended-real regularizer $g$. The hypotheses are present to describe the admissible regularizer, but they are not used to compute the value of $F$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof, because the declaration is a definition. Its body is the expression

$$
\text{fun } x \mapsto \left(\frac{1}{2}\|A.\mathrm{mulVec}(x)-b\|^{2} : \mathbb{R}\right) + g(x).
$$

The `fun x ↦` binder introduces an arbitrary vector $x \in \mathbb{R}^n$. The subexpression `A.mulVec x` computes the matrix-vector product $A x \in \mathbb{R}^m$. Then `A.mulVec x - b` forms the residual $A x - b \in \mathbb{R}^m$. The norm $\|A x - b\|$ is taken in the finite-dimensional space $m \to \mathbb{R}$, and the following `^ 2` squares this norm. The factor `(1 / 2 : ℝ)` multiplies the squared norm, and the type annotation `: ℝ` ensures that this entire first term is treated as a real number before it is coerced into $\overline{\mathbb{R}}$. Finally, `g x` is the extended-real regularizer value, and the `+` is the addition operation in $\overline{\mathbb{R}}$. No named theorem, lemma, or local result is invoked, and no tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` appears. The hypotheses `_hmn`, `_hconvex`, `_hlsc`, and `_hproper` are marked with underscores and do not occur in the definition body; they only constrain the intended mathematical setting.

