## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_2.lean`

## Lean statement
```lean
theorem gamma_pos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis phi theta psi gradPsi a b lam Lpsi) : 0 < gamma a b lam
```

## Statement explanation
The theorem `gamma_pos` concerns a real inner product space $H$, functions $\phi,\theta:H\to\overline{\mathbb R}$, $\psi:H\to\mathbb R$, a map $\mathrm{gradPsi}:H\to H$, real parameters $a,b,\lambda,L_{\psi}$, and a hypothesis

$$
hH : \texttt{IFBHypothesis}(\phi,\theta,\psi,\mathrm{gradPsi},a,b,\lambda,L_{\psi}).
$$

The only numerical object defined locally is

$$
\gamma(a,b,\lambda)=\frac{1-a\lambda}{2b\lambda^{2}}.
$$

The conclusion of the theorem is

$$
0<\gamma(a,b,\lambda).
$$

Mathematically, the theorem says that under the hypotheses packaged in `IFBHypothesis`, the quantity $\gamma(a,b,\lambda)$ is strictly positive. The proof uses only a few consequences of `hH`: it uses positivity of $a$, positivity of $b$, positivity of $\lambda$, and a step-size inequality implying

$$
\lambda<\frac1a.
$$

From $\lambda<1/a$ and $a>0$, it follows that $a\lambda<1$, hence the numerator $1-a\lambda$ is positive. Also $2b>0$ and $\lambda^{2}>0$, so the denominator $2b\lambda^{2}$ is positive. Therefore the quotient $(1-a\lambda)/(2b\lambda^{2})$ is positive. The other ingredients of `IFBHypothesis`, such as $\phi,\theta,\psi,\mathrm{gradPsi},L_{\psi}$, do not enter the proof except as part of the hypothesis `hH`.

## Lean proof
```lean
by
  have hlam_lt_one_div_a : lam < 1 / a :=
    lt_of_lt_of_le hH.step_lt (min_le_left _ _)
  have hlam_mul_a_lt_one : lam * a < 1 :=
    (lt_div_iff₀ hH.a_pos).mp hlam_lt_one_div_a
  have hprod_lt_one : a * lam < 1 := by
    simpa [mul_comm] using hlam_mul_a_lt_one
  have hnum_pos : 0 < 1 - a * lam := sub_pos.mpr hprod_lt_one
  have htwo_b_pos : 0 < 2 * b :=
    mul_pos (by norm_num) hH.b_pos
  have hlam_sq_pos : 0 < lam ^ 2 := pow_pos hH.step_pos 2
  have hden_pos : 0 < 2 * b * lam ^ 2 :=
    mul_pos htwo_b_pos hlam_sq_pos
  unfold gamma
  exact div_pos hnum_pos hden_pos
```

## Proof explanation
The proof proceeds by establishing positivity of the numerator and denominator separately, then applying positivity of division.

First, the proof asserts

$$
\lambda<\frac1a.
$$

It obtains this by applying `lt_of_lt_of_le` to `hH.step_lt` and `min_le_left _ _`. The lemma `min_le_left` says that for any $u,v$,

$$
\min(u,v)\le u.
$$

The field `hH.step_lt` is a strict inequality whose right-hand side is a minimum with first component $1/a$, so together they yield $\lambda<1/a$. This is the step-size condition needed for the numerator estimate.

Next, from $\lambda<1/a$ and the positivity of $a$, supplied by `hH.a_pos`, the proof uses `lt_div_iff₀ hH.a_pos`. This lemma says that for a positive divisor $a$,

$$
\lambda<\frac1a \quad\Longleftrightarrow\quad \lambda a<1.
$$

Thus the proof obtains

$$
\lambda a<1.
$$

Then `simpa [mul_comm]` rewrites using commutativity of multiplication to get

$$
a\lambda<1.
$$

This is the crucial upper bound on $a\lambda$.

Now the proof shows the numerator is positive. Using `sub_pos.mpr`, which says that $x<y$ implies $0<y-x$, the inequality $a\lambda<1$ gives

$$
0<1-a\lambda.
$$

So the numerator $1-a\lambda$ of $\gamma(a,b,\lambda)$ is strictly positive.

Next, the proof shows the denominator is positive. First it proves

$$
0<2b.
$$

It applies `mul_pos` to the facts $0<2$, proved by `norm_num`, and $0<b$, supplied by `hH.b_pos`. Hence the factor $2b$ is positive.

Then it proves

$$
0<\lambda^{2}.
$$

It applies `pow_pos` to `hH.step_pos`, which supplies $0<\lambda$, and exponent $2$, obtaining positivity of the square.

Combining these, the proof uses `mul_pos` again to get

$$
0<2b\cdot \lambda^{2}.
$$

This is exactly the denominator of $\gamma(a,b,\lambda)$ written as $(2b)\lambda^{2}$.

Finally, the proof executes `unfold gamma`, replacing $\gamma(a,b,\lambda)$ by its defining formula

$$
\frac{1-a\lambda}{2b\lambda^{2}}.
$$

It then applies `div_pos` to the already established facts

$$
0<1-a\lambda
$$

and

$$
0<2b\lambda^{2}.
$$

Since a quotient of two positive real numbers is positive, this gives

$$
0<\frac{1-a\lambda}{2b\lambda^{2}},
$$

which, after unfolding the definition of $\gamma$, is precisely the desired conclusion

$$
0<\gamma(a,b,\lambda).
$$

