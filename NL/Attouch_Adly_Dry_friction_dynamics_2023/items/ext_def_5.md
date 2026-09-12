## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_def_5.lean`

## Lean statement
```lean
def bregmanDistance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → ℝ) (gradF : H → H) (a b : H) : ℝ := F b - F a - inner ℝ (gradF a) (b - a)
```

## Statement explanation
The declaration `bregmanDistance` defines a real-valued function associated with a real inner product space. The ambient type \(H\) is assumed to be a normed additive commutative group and an inner product space over \(\mathbb R\), so it supports subtraction, addition, real scalar multiplication, and a real inner product. The arguments are:

- a function \(F:H\to\mathbb R\);
- a map \(gradF:H\to H\);
- two points \(a,b\in H\).

The value returned is the real number

\[
\operatorname{bregmanDistance}(F,gradF,a,b)
= F(b)-F(a)-\langle gradF(a),\, b-a\rangle,
\]

where \(\langle\cdot,\cdot\rangle\) is the real inner product on \(H\). In words, it takes the change \(F(b)-F(a)\) in the values of \(F\) and subtracts the linear quantity obtained by pairing \(gradF(a)\) with the displacement \(b-a\). Equivalently, it is

\[
F(b)-\bigl(F(a)+\langle gradF(a),b-a\rangle\bigr),
\]

so it measures the difference between the actual value \(F(b)\) and the value obtained from a linear correction based at \(a\). The declaration does not assume that \(gradF\) is actually the gradient or derivative of \(F\), nor does it assume convexity, differentiability, nonnegativity, symmetry, or any other property of this expression. It simply introduces the formula as a definition.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, so Lean only needs to verify that the right-hand side is a well-typed real expression under the stated typeclass assumptions. The proof block contains only a comment saying that there is no proof part. No named theorem, lemma, local declaration, or tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` is used.

The mathematical content is therefore exactly the defining formula. Concretely, \(F(a)\) and \(F(b)\) are real numbers, \(b-a\) is a vector in \(H\), \(gradF(a)\) is a vector in \(H\), and the inner product \(\langle gradF(a),b-a\rangle\) is again a real number. Thus the expression

\[
F(b)-F(a)-\langle gradF(a),b-a\rangle
\]

is a real number, and Lean binds the name `bregmanDistance` to this operation on \(F\), \(gradF\), \(a\), and \(b\).

