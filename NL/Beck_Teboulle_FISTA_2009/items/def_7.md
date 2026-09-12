## Source file
`Beck_Teboulle_FISTA_2009/items/def_7.lean`

## Lean statement
```lean
def IsProxPoint {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsMinOn (fun x => quadraticApprox f g L x y) univ z
```

## Statement explanation
The declaration defines a predicate named `IsProxPoint`. It takes an implicit natural number \(n\), two real-valued functions
\[
f,g:\mathbb{R}^n\to\mathbb{R},
\]
a real number \(L\), and two points \(y,z\in\mathbb{R}^n\). The type \(\mathbb{R}^n\) is written in Lean as `EuclideanSpace ℝ (Fin n)`. The predicate is defined so that `IsProxPoint f g L y z` holds exactly when
\[
\texttt{IsMinOn}\left(x\mapsto \operatorname{quadraticApprox}(f,g,L,x,y)\right)\ \mathrm{univ}\ z.
\]
Thus, after fixing \(f,g,L,y\), one forms the real-valued function
\[
F(x)=\operatorname{quadraticApprox}(f,g,L,x,y)
\]
on \(\mathbb{R}^n\). The proposition says that \(z\) is a minimum point of \(F\) over the whole space \(\mathbb{R}^n\). In Mathlib, `IsMinOn F s z` means that \(z\in s\) and \(F(z)\le F(x)\) for every \(x\in s\); here \(s=\mathrm{univ}\), so the membership condition is automatic and the substantive content is that
\[
F(z)\le F(x)\qquad\text{for every }x\in\mathbb{R}^n.
\]
Therefore `IsProxPoint f g L y z` is the statement that \(z\) globally minimizes the quadratic approximation built from \(f,g,L\) at the point \(y\). The definition imposes no extra hypotheses on \(f,g,L,y,z\): no convexity, differentiability, positivity of \(L\), existence, or uniqueness is asserted. The formula for `quadraticApprox` is not included in this declaration, so the definition says only that `IsProxPoint` is the global-minimizer property for that already-named function.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. This declaration is a definition, not a theorem. Lean accepts it by checking that the right-hand side
\[
\texttt{IsMinOn}\left(x\mapsto \operatorname{quadraticApprox}(f,g,L,x,y)\right)\ \mathrm{univ}\ z
\]
is a well-typed term of type `Prop`. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, because no mathematical reasoning is being performed.

If one later unfolds `IsProxPoint`, the expression `IsProxPoint f g L y z` is replaced by its defining right-hand side. Then, using the meaning of `IsMinOn` specialized to the universal set `univ`, one obtains exactly that \(z\) is a global minimum of the function
\[
F(x)=\operatorname{quadraticApprox}(f,g,L,x,y),
\]
that is,
\[
F(z)\le F(x)\qquad\text{for all }x\in\mathbb{R}^n.
\]
This is the exact consequence supplied by the definition. The definition itself does not assert that such a point \(z\) exists, nor that it is unique, nor any further optimality condition beyond this global inequality.

