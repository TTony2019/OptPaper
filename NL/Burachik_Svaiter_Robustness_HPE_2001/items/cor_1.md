## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/cor_1.lean`

## Lean statement
```lean
theorem hpe_distance_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) {xStar : H}
    (hxStar : (0 : H) ∈ T xStar) (k : ℕ) :
    ‖A.x (k + 1) - xStar‖ ≤ A.α k + Real.sqrt (‖A.x k - xStar‖ ^ 2 + A.δ k)
```

## Statement explanation
The declaration `hpe_distance_bound` states a one-step distance estimate for an HPE iteration. It is stated for a real inner product space \(H\), a set-valued operator \(T:H \to H\), an HPE-iteration object \(A\) associated with \(T\), a point \(x^\star\in H\), and an index \(k\in\mathbb N\). The hypothesis \(hxStar : (0:H)\in T xStar\) says that the zero vector belongs to the set \(T(x^\star)\), so \(x^\star\) is a zero or solution of the inclusion \(0\in T(x)\).

The object \(A\) packages the iteration data. The conclusion uses the main iterate \(A.x_k\), the next iterate \(A.x_{k+1}\), and the real parameters \(A.\alpha_k\) and \(A.\delta_k\). The proof also uses the auxiliary fields \(A.y_k\), \(A.c_k\), \(A.v_k\), and \(A.\sigma_k\). The cited definition of `extragradientStep` says that the extragradient point is

\[
\operatorname{extragradientStep}(A,k)=A.x_k-A.c_k\cdot A.v_k,
\]

where \(\cdot\) is scalar multiplication. The cited theorem `hpe_descent` says that if \(0\in T(x^\star)\), then

\[
\|x^\star-A.x_k\|^2-\|x^\star-\operatorname{extragradientStep}(A,k)\|^2
\ge
(1-(A.\sigma_k)^2)\|A.y_k-A.x_k\|^2-A.\delta_k.
\]

Thus the squared distance to \(x^\star\) decreases by at least a penalty term involving \(\|A.y_k-A.x_k\|^2\), minus the error \(A.\delta_k\), provided the coefficient \(1-(A.\sigma_k)^2\) is nonnegative.

The theorem concludes the ordinary-language bound

\[
\|A.x_{k+1}-x^\star\|
\le
A.\alpha_k+
\sqrt{\|A.x_k-x^\star\|^2+A.\delta_k}.
\]

So the next iterate is no farther from \(x^\star\) than the sum of the step error \(A.\alpha_k\) and the square root of the previous squared distance plus the error \(A.\delta_k\). This is a robustness or stability estimate: it controls the distance from the next iterate to the solution in terms of the previous distance and the method’s error parameters.

## Lean proof
```lean
by
  let z := extragradientStep A k
  have hupdate : ‖A.x (k + 1) - z‖ ≤ A.α k := by
    simpa [z] using A.update_error k
  let σbar := A.sigma_bound.choose
  have hσbar_lt_one : σbar < 1 := A.sigma_bound.choose_spec.2.1
  have hσ_nonneg : 0 ≤ A.σ k := A.σ_nonneg k
  have hσ_le : A.σ k ≤ σbar := (A.sigma_bound.choose_spec.2.2 k).2
  have hσsq : (A.σ k) ^ 2 ≤ 1 := by
    nlinarith [hσ_nonneg, hσ_le, hσbar_lt_one]
  have hcoeff : 0 ≤ 1 - (A.σ k) ^ 2 := sub_nonneg.mpr hσsq
  have hpenalty : 0 ≤ (1 - (A.σ k) ^ 2) * ‖A.y k - A.x k‖ ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg _)
  have hdescent := hpe_descent A hxStar k
  have hsq : ‖xStar - z‖ ^ 2 ≤ ‖xStar - A.x k‖ ^ 2 + A.δ k := by
    simp only [z]
    nlinarith [hdescent, hpenalty]
  have hz_sqrt : ‖z - xStar‖ ≤ Real.sqrt (‖A.x k - xStar‖ ^ 2 + A.δ k) := by
    have hroot : ‖xStar - z‖ ≤ Real.sqrt (‖xStar - A.x k‖ ^ 2 + A.δ k) := by
      calc
        ‖xStar - z‖ = Real.sqrt (‖xStar - z‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖xStar - A.x k‖ ^ 2 + A.δ k) := Real.sqrt_le_sqrt hsq
    simpa only [norm_sub_rev] using hroot
  calc
    ‖A.x (k + 1) - xStar‖ = ‖(A.x (k + 1) - z) + (z - xStar)‖ := by
      rw [show A.x (k + 1) - xStar = (A.x (k + 1) - z) + (z - xStar) by abel]
    _ ≤ ‖A.x (k + 1) - z‖ + ‖z - xStar‖ := norm_add_le _ _
    _ ≤ A.α k + Real.sqrt (‖A.x k - xStar‖ ^ 2 + A.δ k) :=
      add_le_add hupdate hz_sqrt
```

## Proof explanation
The proof starts by defining the local abbreviation \(z\) as the extragradient step:

\[
z := \operatorname{extragradientStep}(A,k).
\]

This lets the rest of the proof refer to that intermediate point concisely. The first auxiliary claim is

\[
hupdate : \|A.x_{k+1}-z\|\le A.\alpha_k.
\]

It is obtained by `simpa [z] using A.update_error k`. The exact consequence visible here is that the update-error property of the HPE iterates, after unfolding \(z\) as the extragradient step, gives that the next iterate \(A.x_{k+1}\) is within \(A.\alpha_k\) of \(z\). This is the part of the estimate that contributes the additive term \(A.\alpha_k\).

Next the proof chooses a uniform bound for the parameters \(A.\sigma_k\). It writes

\[
\bar\sigma := A.\sigma_{\text{bound}}.\mathrm{choose}.
\]

The field \(A.\sigma_{\text{bound}}\) is an existential statement, and `choose` selects a witness \(\bar\sigma\). Applying `choose_spec.2.1` gives

\[
\bar\sigma < 1.
\]

Applying `choose_spec.2.2 k` and taking its second component gives

\[
A.\sigma_k \le \bar\sigma.
\]

The proof also uses the field \(A.\sigma_{\text{nonneg}} k\) to obtain

\[
0 \le A.\sigma_k.
\]

Combining \(0\le A.\sigma_k\), \(A.\sigma_k\le \bar\sigma\), and \(\bar\sigma<1\) by `nlinarith` yields

\[
(A.\sigma_k)^2 \le 1.
\]

Here `nlinarith` is doing nonlinear arithmetic over the ordered field \(\mathbb R\): from the nonnegativity and upper bound on \(A.\sigma_k\), it derives the squared bound. This matters because the descent inequality from `hpe_descent` contains the coefficient \(1-(A.\sigma_k)^2\).

From \((A.\sigma_k)^2\le 1\), the proof obtains

\[
0 \le 1-(A.\sigma_k)^2
\]

using `sub_nonneg.mpr`. This is just the equivalence \(0\le a-b\) iff \(b\le a\). Then it proves

\[
0 \le (1-(A.\sigma_k)^2)\|A.y_k-A.x_k\|^2
\]

using `mul_nonneg hcoeff (sq_nonneg _)`. The reason is that \(1-(A.\sigma_k)^2\) is nonnegative and every squared norm is nonnegative. This nonnegativity of the penalty term is essential for turning the descent inequality into an upper bound on the squared distance to \(z\).

The proof then applies the cited descent theorem:

\[
hdescent := \texttt{hpe\_descent } A\ hxStar\ k.
\]

In concrete terms, this gives

\[
\|x^\star-A.x_k\|^2-\|x^\star-z\|^2
\ge
(1-(A.\sigma_k)^2)\|A.y_k-A.x_k\|^2-A.\delta_k,
\]

because \(z\) is the extragradient step. Let

\[
D=\|x^\star-A.x_k\|^2,\qquad
E=\|x^\star-z\|^2,\qquad
P=(1-(A.\sigma_k)^2)\|A.y_k-A.x_k\|^2.
\]

The descent inequality says \(D-E\ge P-A.\delta_k\), and the preceding nonnegativity result says \(P\ge 0\). Hence \(D-E\ge -A.\delta_k\), which rearranges to

\[
E\le D+A.\delta_k.
\]

This is exactly the auxiliary claim

\[
hsq : \|x^\star-z\|^2\le \|x^\star-A.x_k\|^2+A.\delta_k.
\]

The proof obtains it by unfolding \(z\) with `simp only [z]` and then using `nlinarith` with the hypotheses `hdescent` and `hpenalty`.

Next the proof converts the squared inequality into an inequality for norms. It wants

\[
hz\_sqrt : \|z-x^\star\|
\le
\sqrt{\|A.x_k-x^\star\|^2+A.\delta_k}.
\]

First it proves the version with \(\|x^\star-z\|\) on the left:

\[
hroot : \|x^\star-z\|
\le
\sqrt{\|x^\star-A.x_k\|^2+A.\delta_k}.
\]

The proof uses the calculation

\[
\|x^\star-z\|=\sqrt{\|x^\star-z\|^2}.
\]

This equality follows from `Real.sqrt_sq (norm_nonneg _)`: for a nonnegative real number \(r\), one has \(\sqrt{r^2}=r\), and the norm \(\|x^\star-z\|\) is nonnegative. Then it applies monotonicity of the square root via `Real.sqrt_le_sqrt hsq`, using the previously established inequality \(hsq\), to get

\[
\sqrt{\|x^\star-z\|^2}
\le
\sqrt{\|x^\star-A.x_k\|^2+A.\delta_k}.
\]

Combining these gives \(hroot\). Finally, `simpa only [norm_sub_rev] using hroot` rewrites \(\|x^\star-z\|\) as \(\|z-x^\star\|\) and rewrites \(\|x^\star-A.x_k\|\) as \(\|A.x_k-x^\star\|\), since \(\|a-b\|=\|b-a\|\). This yields \(hz\_sqrt\).

The final part of the proof is a `calc` chain:

\[
\|A.x_{k+1}-x^\star\|
=
\|(A.x_{k+1}-z)+(z-x^\star)\|.
\]

The equality is obtained by `rw [show A.x (k + 1) - xStar = (A.x (k + 1) - z) + (z - xStar) by abel]`, where `abel` proves the algebraic identity in the additive abelian group. Then the triangle inequality, invoked through `norm_add_le`, gives

\[
\|(A.x_{k+1}-z)+(z-x^\star)\|
\le
\|A.x_{k+1}-z\|+\|z-x^\star\|.
\]

Finally, `add_le_add hupdate hz_sqrt` adds the two estimates

\[
\|A.x_{k+1}-z\|\le A.\alpha_k
\]

and

\[
\|z-x^\star\|
\le
\sqrt{\|A.x_k-x^\star\|^2+A.\delta_k}
\]

to obtain

\[
\|A.x_{k+1}-x^\star\|
\le
A.\alpha_k+
\sqrt{\|A.x_k-x^\star\|^2+A.\delta_k}.
\]

That is exactly the claimed distance bound. There is no separate `intro` or terminal `exact` in this proof; the theorem’s parameters are already in context, and the result is produced by the local `have` statements and the final `calc` block.

