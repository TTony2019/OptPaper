## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/lem_1.lean`

## Lean statement
```lean
theorem hpe_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) {xStar : H}
    (hxStar : (0 : H) ∈ T xStar) (k : ℕ) :
    ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 ≥
      (1 - (A.σ k) ^ 2) * ‖A.y k - A.x k‖ ^ 2 - A.δ k
```

## Statement explanation
The declaration `hpe_descent` states a one-step descent inequality for an HPE-type iteration associated with a set-valued operator $T$. The ambient space $H$ is a real inner product space, so it carries a norm $\|\cdot\|$ and a real inner product $\langle\cdot,\cdot\rangle$. The operator $T$ is a set-valued operator on $H$, and $A$ is an `HPEIterates H T`, i.e. a record of iterates and parameters attached to $T$. For each natural number $k$, write

$$
x_k = A.x\,k,\qquad y_k = A.y\,k,\qquad v_k = A.v\,k,
$$

and for the real parameters

$$
c_k = A.c\,k,\qquad \varepsilon_k = A.\varepsilon\,k,\qquad
\delta_k = A.\delta\,k,\qquad \sigma_k = A.\sigma\,k.
$$

The extragradient step is defined by

$$
z_k = \operatorname{extragradientStep} A k = x_k - c_k v_k.
$$

The point $x^\star$ is assumed to be a zero of $T$ in the precise sense that $0 \in T x^\star$. The conclusion is

$$
\|x^\star-x_k\|^2-\|x^\star-z_k\|^2
\ge
(1-\sigma_k^2)\|y_k-x_k\|^2-\delta_k.
$$

Thus the squared distance from $x^\star$ to the current iterate $x_k$, minus the squared distance from $x^\star$ to the extragradient point $z_k$, is bounded below by a residual term $(1-\sigma_k^2)\|y_k-x_k\|^2$ minus the parameter $\delta_k$. In ordinary language, this says that the extragradient step $z_k$ makes at least the prescribed amount of progress toward the zero $x^\star$, up to the correction term $\delta_k$.

The proof uses several properties packaged inside the HPE iteration $A$. First, $c_k>0$, hence $c_k\ge0$, which is needed to multiply an inequality by $c_k$ without changing its direction. Second, $v_k$ belongs to the $\varepsilon_k$-enlargement of $T$ at $y_k$: by definition of `epsilonEnlargement`, this means that for every $z$ and every $w$,

$$
w\in Tz \quad\Longrightarrow\quad
\langle w-v_k,\,z-y_k\rangle \ge -\varepsilon_k.
$$

Third, the residual bound for the HPE iteration says, in the form used after rewriting, that

$$
\|y_k-z_k\|^2+2c_k\varepsilon_k
\le
\delta_k+\sigma_k^2\|y_k-x_k\|^2.
$$

These are not extra hypotheses written explicitly in the theorem statement; they are the facts about `A` that the proof invokes.

## Lean proof
```lean
by
  have hm := A.enlargement_mem k
  have hmem : -A.ε k ≤ inner ℝ ((0 : H) - A.v k) (xStar - A.y k) := by
    simpa [epsilonEnlargement] using hm xStar (0 : H) hxStar
  have hc0 : 0 ≤ A.c k := le_of_lt (A.c_pos k)
  have hinner : -A.c k * A.ε k ≤
      inner ℝ (extragradientStep A k - A.x k) (xStar - A.y k) := by
    have hscaled := mul_le_mul_of_nonneg_left hmem hc0
    rw [show extragradientStep A k - A.x k = -(A.c k • A.v k) by
      simp [extragradientStep], inner_neg_left, real_inner_smul_left]
    simpa [mul_neg, neg_mul] using hscaled
  have hnorm := hpe_norm_difference_identity xStar (A.y k) (A.x k)
    (extragradientStep A k)
  have hfirst : ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 ≥
      ‖A.y k - A.x k‖ ^ 2 - ‖A.y k - extragradientStep A k‖ ^ 2 -
        2 * A.c k * A.ε k := by
    nlinarith [hnorm, hinner]
  have hyz : A.y k - extragradientStep A k = A.c k • A.v k + A.y k - A.x k := by
    simp [extragradientStep]
    abel
  have hres : ‖A.y k - extragradientStep A k‖ ^ 2 + 2 * A.c k * A.ε k ≤
      A.δ k + (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2 := by
    rw [hyz]
    exact A.residual_bound k
  nlinarith [hfirst, hres]
```

## Proof explanation
The proof begins with `have hm := A.enlargement_mem k`. This extracts the membership fact that $v_k$ lies in the $\varepsilon_k$-enlargement of $T$ at $y_k$. By the definition of `epsilonEnlargement`, such a membership is a universal statement: for every $z$ and every $w$, if $w\in Tz$, then

$$
\langle w-v_k,\,z-y_k\rangle \ge -\varepsilon_k.
$$

Next, the proof forms

$$
\texttt{hmem}:\quad -\varepsilon_k \le \langle 0-v_k,\,x^\star-y_k\rangle.
$$

It does this by applying `hm` to $z=x^\star$ and $w=0$, using the hypothesis `hxStar : (0 : H) ∈ T xStar`. The command `simpa [epsilonEnlargement]` unfolds the definition of `epsilonEnlargement` and simplifies the resulting inequality to the displayed form. Since $0-v_k=-v_k$, this inequality says

$$
-\varepsilon_k \le \langle -v_k,\,x^\star-y_k\rangle.
$$

So the known zero $x^\star$ is used as the test point for the enlargement condition.

The proof then records `hc0 : 0 ≤ A.c k` from `A.c_pos k` via `le_of_lt`. In words, the step size $c_k$ is positive, therefore nonnegative.

The next step is

$$
\texttt{hinner}:\quad -c_k\varepsilon_k
\le
\langle \operatorname{extragradientStep} A k - x_k,\,
x^\star-y_k\rangle.
$$

It is obtained by multiplying the previous inequality by $c_k\ge0$. The command `mul_le_mul_of_nonneg_left hmem hc0` gives

$$
-c_k\varepsilon_k
\le
c_k\langle -v_k,\,x^\star-y_k\rangle.
$$

Then the proof rewrites

$$
\operatorname{extragradientStep} A k - x_k
=
(x_k-c_kv_k)-x_k
=
-c_kv_k.
$$

Using linearity of the inner product in its first argument, this becomes

$$
\langle -c_kv_k,\,x^\star-y_k\rangle
=
c_k\langle -v_k,\,x^\star-y_k\rangle.
$$

The `rw` with `extragradientStep`, `inner_neg_left`, and `real_inner_smul_left` performs these rewrites, and `simpa [mul_neg, neg_mul]` normalizes the signs.

The proof now applies the three-point norm identity `hpe_norm_difference_identity`. Specialized to

$$
x^\star=x^\star,\qquad y=y_k,\qquad x=x_k,\qquad z=z_k,
$$

it gives

$$
\|x^\star-x_k\|^2-\|x^\star-z_k\|^2
=
2\langle z_k-x_k,\,x^\star-y_k\rangle
+\|y_k-x_k\|^2-\|y_k-z_k\|^2.
$$

This is an exact algebraic identity for the real inner product space. Combining it with `hinner`, which says

$$
-c_k\varepsilon_k
\le
\langle z_k-x_k,\,x^\star-y_k\rangle,
$$

yields

$$
2\langle z_k-x_k,\,x^\star-y_k\rangle
\ge
-2c_k\varepsilon_k.
$$

Hence

$$
\|x^\star-x_k\|^2-\|x^\star-z_k\|^2
\ge
\|y_k-x_k\|^2-\|y_k-z_k\|^2-2c_k\varepsilon_k.
$$

This is the intermediate inequality called `hfirst`. The tactic `nlinarith [hnorm, hinner]` verifies this real arithmetic combination.

Next, the proof establishes

$$
y_k-z_k=c_kv_k+y_k-x_k.
$$

Indeed,

$$
z_k=x_k-c_kv_k,
$$

so

$$
y_k-z_k
=
y_k-(x_k-c_kv_k)
=
c_kv_k+y_k-x_k.
$$

The command `simp [extragradientStep]` unfolds the definition of the extragradient step, and `abel` normalizes the additive expression in the abelian group $H$.

The proof then invokes the residual bound of the HPE iteration. After rewriting $y_k-z_k$ as above, the statement

$$
\texttt{hres}:
\|y_k-z_k\|^2+2c_k\varepsilon_k
\le
\delta_k+\sigma_k^2\|y_k-x_k\|^2
$$

is exactly the consequence supplied by `A.residual_bound k`. The `rw [hyz]` rewrites the left-hand squared norm into

$$
\|c_kv_k+y_k-x_k\|^2,
$$

and then `exact A.residual_bound k` closes the goal. This residual bound controls the size of the HPE residual $c_kv_k+y_k-x_k$ together with the enlargement term $2c_k\varepsilon_k$.

Finally, the proof combines `hfirst` and `hres` using `nlinarith [hfirst, hres]`. From `hfirst`,

$$
\|x^\star-x_k\|^2-\|x^\star-z_k\|^2
\ge
\|y_k-x_k\|^2-\|y_k-z_k\|^2-2c_k\varepsilon_k.
$$

From `hres`,

$$
\|y_k-z_k\|^2+2c_k\varepsilon_k
\le
\delta_k+\sigma_k^2\|y_k-x_k\|^2.
$$

Therefore

$$
\|y_k-x_k\|^2-\|y_k-z_k\|^2-2c_k\varepsilon_k
=
\|y_k-x_k\|^2-\bigl(\|y_k-z_k\|^2+2c_k\varepsilon_k\bigr)
\ge
\|y_k-x_k\|^2-\bigl(\delta_k+\sigma_k^2\|y_k-x_k\|^2\bigr)
=
(1-\sigma_k^2)\|y_k-x_k\|^2-\delta_k.
$$

Combining this with the previous lower bound gives

$$
\|x^\star-x_k\|^2-\|x^\star-z_k\|^2
\ge
(1-\sigma_k^2)\|y_k-x_k\|^2-\delta_k,
$$

which is precisely the claimed descent inequality.

