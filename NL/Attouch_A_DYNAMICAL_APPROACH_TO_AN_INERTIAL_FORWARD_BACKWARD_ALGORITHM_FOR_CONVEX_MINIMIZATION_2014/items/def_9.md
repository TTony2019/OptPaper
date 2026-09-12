## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_9.lean`

## Lean statement
```lean
noncomputable def auxiliaryA {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  (a + b) / (2 * lam) * ‖u k - q‖ ^ 2 -
    (1 / lam + b) * auxiliaryG u y a b lam q (k + 1) (by omega)
```

## Statement explanation
The declaration introduces a noncomputable real-valued auxiliary function `auxiliaryA`. The type \(H\) is assumed to be a normed additive commutative group and also a real inner-product space, so it carries an inner product over \(\mathbb{R}\) and the associated norm \(\|\cdot\|\). The arguments \(u\) and \(y\) are sequences \(\mathbb{N}\to H\). The parameters \(a\), \(b\), and `lam` are real numbers; write \(\lambda\) for the Lean parameter `lam`. The point \(q\) lies in \(H\). The index \(k\) is a natural number, and \(hk\) is a proof of the hypothesis \(1\le k\). The function returns a real number.

For such data, `auxiliaryA` is defined by
\[
\operatorname{auxiliaryA}(u,y,a,b,\lambda,q,k,hk)
=
\frac{a+b}{2\lambda}\,\|u_k-q\|^2
-
\left(\frac{1}{\lambda}+b\right)\,
\operatorname{auxiliaryG}(u,y,a,b,\lambda,q,k+1,\text{proof}).
\]
Here \(u_k\) denotes the \(k\)-th term of the sequence \(u\), and \(\|u_k-q\|^2\) is the squared distance, in \(H\), from that term to \(q\). The second summand uses the previously defined auxiliary quantity `auxiliaryG`, evaluated with the same sequences and parameters but at the next index \(k+1\). The final argument `(by omega)` is a proof term needed because `auxiliaryG` requires an arithmetic side condition for the index at which it is evaluated. The exact proposition required by `auxiliaryG` is not shown in the provided source, but the visible role of `omega` is to discharge that arithmetic requirement for the index \(k+1\). There is no assumption in the declaration that \(\lambda\neq 0\); Lean’s real division is total, so the displayed expression is still formally defined even when \(\lambda=0\).

Mathematically, the definition constructs a real correction or auxiliary expression: it takes a weighted squared distance of \(u_k\) from \(q\), subtracts a scalar multiple of another auxiliary term evaluated at the next index \(k+1\), and packages this as a function of the sequences, the scalar parameters, the point \(q\), and the index \(k\) with its positivity hypothesis.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a definition, not a theorem, so Lean does not prove a proposition here; it only checks that the right-hand side is a well-typed term of type \(\mathbb{R}\). The keyword `noncomputable` marks it as a noncomputable definition, which is appropriate because the definition is built from abstract normed and inner-product-space structure and from the auxiliary quantity `auxiliaryG`.

There are no uses of tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`. The only proof-producing expression in the definition is `by omega`, which occurs as the final argument to `auxiliaryG`. The `omega` tactic solves goals in linear integer arithmetic. Its role here is to supply the arithmetic proof required by `auxiliaryG` when that auxiliary quantity is evaluated at the index \(k+1\). The surrounding context contains the hypothesis \(hk:1\le k\), and the call is made at the next natural-number index \(k+1\). The exact condition expected by `auxiliaryG` is not displayed in the provided source, so one cannot expand it further from the given material; what is visible is that `omega` discharges the necessary arithmetic side condition so that the call to `auxiliaryG` is well-typed.

After that proof argument is supplied, the value of `auxiliaryA` is exactly the real number formed by the two terms displayed above: the weighted squared distance \(\|u_k-q\|^2\) minus the scalar times `auxiliaryG` at index \(k+1\). No named theorem or lemma is invoked in the definition.

