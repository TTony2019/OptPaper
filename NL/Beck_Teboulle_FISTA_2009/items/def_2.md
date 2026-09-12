## Source file
`Beck_Teboulle_FISTA_2009/items/def_2.lean`

## Lean statement
```lean
noncomputable def shrinkageOperator {n : ℕ} (α : ℝ) (x : Vec n) : Vec n :=
  WithLp.toLp 2 (fun i : Fin n =>
    positivePart (|x i| - α) * Real.sign (x i))
```

## Statement explanation
The declaration defines the shrinkage operator as a componentwise map on real $n$-dimensional vectors. It takes an implicit natural number $n$, a real scalar $\alpha$, and a vector $x$ of type `Vec n`, and returns a vector of the same type. The body uses `WithLp.toLp 2` to package a coordinate function $i \mapsto \cdots$ as an element of the $L^2$-type underlying `Vec n`; the number $2$ specifies the $L^2$/Euclidean packaging, not a coordinate index. For each index $i \in \mathrm{Fin}(n)$, the $i$-th coordinate of the result is

$$
(S_\alpha x)_i
=
\mathrm{positivePart}(|x_i|-\alpha)\mathrm{sign}(x_i),
$$

where $\mathrm{positivePart}(t)=\max(t,0)$. Thus the coordinate is zero unless $|x_i|-\alpha$ is positive and $x_i\neq 0$; otherwise it is $(|x_i|-\alpha)\mathrm{sign}(x_i)$. The factor $\mathrm{sign}(x_i)$ is $1$ when $x_i>0$, $-1$ when $x_i<0$, and $0$ when $x_i=0$. Consequently the formula shrinks the magnitude of each coordinate toward zero by $\alpha$, while preserving its sign. When $\alpha\ge 0$, this is the usual soft-thresholding formula:

$$
(S_\alpha x)_i =
\begin{cases}
x_i-\alpha, & x_i>\alpha,\\
0, & |x_i|\le \alpha,\\
x_i+\alpha, & x_i<-\alpha.
\end{cases}
$$

The definition itself does not assume $\alpha\ge 0$; for other real values of $\alpha$ the coordinate formula still makes sense, though the standard threshold interpretation is the case $\alpha\ge 0$. The marker `noncomputable` indicates that Lean treats the definition as non-executable, but it adds no mathematical hypothesis and does not change the formula.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, so the expression after `:=` is the defining expression rather than a proof term. No theorem, lemma, named local result, or proof tactic such as `intro`, `rw`, `simp`, `exact`, or `linarith` is used. The mathematical content is entirely in the construction of the operator: `WithLp.toLp 2` turns the coordinate function $i \mapsto \mathrm{positivePart}(|x_i|-\alpha)\mathrm{sign}(x_i)$ into a vector in the $L^2$-type `Vec n`; the lambda `fun i : Fin n => ...` specifies that this coordinate formula is applied independently at every index $i$. The function `positivePart` supplies the nonnegative part $\max(|x_i|-\alpha,0)$, so it clips the amount by which $|x_i|$ exceeds $\alpha$ to be nonnegative, and `Real.sign` supplies the sign of the original coordinate. The multiplication of these two factors gives a coordinate of magnitude $|x_i|-\alpha$ when $|x_i|-\alpha>0$, with the original sign of $x_i$, and gives $0$ when either the nonnegative part is zero or the sign is zero. Thus the definition encodes componentwise shrinkage toward zero with threshold $\alpha$.

