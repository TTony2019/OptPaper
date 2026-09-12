## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_def_3.lean`

## Lean statement
```lean
lemma beta_div_delta_nonincreasing (β μ : ℕ → ℝ) (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_pos : ∀ n, β n > 0) (hμ_pos : ∀ n, μ n > 0)
    (hβ_prop : β_behavior.toProp (β := β)) (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∀ n, β (n+1) / deltaSeq β μ β_behavior μ_behavior (n+1) ≤
         β n / deltaSeq β μ β_behavior μ_behavior n
```

## Statement explanation
The declaration concerns two strictly positive real sequences $\beta,\mu:\mathbb N\to\mathbb R$ and two monotonicity tags `β_behavior` and `μ_behavior`, each of which is either `.nonincreasing` or `.nondecreasing`. The auxiliary sequence $\delta$ is defined by cases according to those two tags:

```math
\delta_n=
\begin{cases}
1, & \text{if } \beta \text{ is nonincreasing and } \mu \text{ is nonincreasing},\\
\mu_n, & \text{if } \beta \text{ is nonincreasing and } \mu \text{ is nondecreasing},\\
\beta_n, & \text{if } \beta \text{ is nondecreasing and } \mu \text{ is nonincreasing},\\
\beta_n\mu_n, & \text{if } \beta \text{ is nondecreasing and } \mu \text{ is nondecreasing}.
\end{cases}
```

The hypotheses are:

- $hβ_pos:\forall n,\ \beta_n\gt 0$, so every term of $\beta$ is strictly positive.
- $hμ_pos:\forall n,\ \mu_n\gt 0$, so every term of $\mu$ is strictly positive.
- $`hβ_prop:\beta\_behavior.toProp(\beta:=\beta)`$, meaning$\beta$ has the monotonicity behavior indicated by `β_behavior`. In the proof this is used as the pointwise consequence: if `β_behavior` is `.nonincreasing`, then $\beta_{n+1}\le \beta_n$; if it is `.nondecreasing`, then $\beta_n\le \beta_{n+1}$.
- $`hμ_prop:\mu\_behavior.toProp(\beta:=\mu)`$, the analogous monotonicity property for$\mu$.

The conclusion is

$$
\forall n,\quad
\frac{\beta_{n+1}}{\delta_{n+1}}
\le
\frac{\beta_n}{\delta_n}.
$$

Equivalently, the sequence $n\mapsto \beta_n/\delta_n$ is nonincreasing. The lemma is thus a case-by-case verification that the chosen denominator sequence $\delta$ makes the quotient of $\beta$ by $\delta$ weakly decreasing, under the stated positivity and monotonicity hypotheses.

## Lean proof
```lean
by
  intro n
  unfold deltaSeq
  have hβpos_n : 0 < β n := hβ_pos n
  have hβpos_n1 : 0 < β (n+1) := hβ_pos (n+1)
  have hμpos_n : 0 < μ n := hμ_pos n
  have hμpos_n1 : 0 < μ (n+1) := hμ_pos (n+1)
  match β_behavior, μ_behavior with
  | .nonincreasing, .nonincreasing =>
    -- δ = 1, so the claim reduces to β(n+1) ≤ β(n)
    simp [hβ_prop n]
  | .nonincreasing, .nondecreasing =>
    -- δ = μ. β is nonincreasing, μ is nondecreasing, both positive.
    -- Multiply both sides by μ(n+1)·μ(n) > 0, then use calc chain.
    have hprod : β (n+1) * μ n ≤ β n * μ (n+1) := by
      calc
        β (n+1) * μ n ≤ β n * μ n := mul_le_mul_of_nonneg_right (hβ_prop n) (by positivity)
        _ ≤ β n * μ (n+1) := mul_le_mul_of_nonneg_left (hμ_prop n) (by positivity)
    field_simp [hμpos_n.ne.symm, hμpos_n1.ne.symm]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  | .nondecreasing, .nonincreasing =>
    -- δ = β, so both sides equal 1
    field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm]
    exact le_refl 1
  | .nondecreasing, .nondecreasing =>
    -- δ = β·μ. Both fractions simplify to reciprocals of μ:
    -- β(n+1)/(β(n+1)·μ(n+1)) = 1/μ(n+1), β(n)/(β(n)·μ(n)) = 1/μ(n)
    -- So the claim reduces to μ(n) ≤ μ(n+1)
    field_simp [hβpos_n.ne.symm, hβpos_n1.ne.symm, hμpos_n.ne.symm, hμpos_n1.ne.symm]
    exact hμ_prop n
```

## Proof explanation
The proof begins with `intro n`, which fixes an arbitrary natural number $n$, reducing the goal from a universal statement to the single inequality

$$
\frac{\beta_{n+1}}{\delta_{n+1}}
\le
\frac{\beta_n}{\delta_n}.
$$

Then `unfold deltaSeq` replaces $\delta$ by the explicit case definition of `deltaSeq`. The four `have` statements record the local positivity facts

$$
0<\beta_n,\qquad 0<\beta_{n+1},\qquad 0<\mu_n,\qquad 0<\mu_{n+1}.
$$

These are obtained by applying the global hypotheses $hβ_pos$ and $hμ_pos$ at $n$ and $n+1$. They are used later to justify cancellations and multiplication by positive factors.

The `match` command splits the proof into the four possible combinations of the two monotonicity behaviors.

- Case `.nonincreasing, .nonincreasing`: here $\delta_m=1$ for every $m$. The goal becomes

$$
\frac{\beta_{n+1}}{1}\le \frac{\beta_n}{1},
$$

  that is, $\beta_{n+1}\le \beta_n$. The `simp` call simplifies the divisions by $1$ and uses the hypothesis $hβ_prop\ n$, which, because `β_behavior` is `.nonincreasing`, is exactly the inequality $\beta_{n+1}\le \beta_n$. Hence the goal is closed.

- Case `.nonincreasing, .nondecreasing`: here $\delta_m=\mu_m$. The goal is

$$
\frac{\beta_{n+1}}{\mu_{n+1}}\le \frac{\beta_n}{\mu_n}.
$$

  The proof first establishes

$$
\beta_{n+1}\mu_n\le \beta_n\mu_{n+1}.
$$

  This is done with a `calc` chain. The first inequality is

$$
\beta_{n+1}\mu_n\le \beta_n\mu_n.
$$

  It uses the theorem `mul_le_mul_of_nonneg_right`: if $a\le b$ and $0\le c$, then $ac\le bc$. Here $a=\beta_{n+1}$, $b=\beta_n$, and $c=\mu_n$. The inequality $\beta_{n+1}\le \beta_n$ is $hβ_prop\ n$, and the side condition $0\le \mu_n$ is supplied by `positivity` using $\mu_n\gt 0$. The second inequality is

$$
\beta_n\mu_n\le \beta_n\mu_{n+1}.
$$

  It uses `mul_le_mul_of_nonneg_left`: if $a\le b$ and $0\le c$, then $ca\le cb$. Here $a=\mu_n$, $b=\mu_{n+1}$, and $c=\beta_n$. The inequality $\mu_n\le \mu_{n+1}$ is $hμ_prop\ n$, and $0\le \beta_n$ is supplied by `positivity`. The `calc` chain combines these two inequalities by transitivity to obtain the displayed product inequality. Then `field_simp` clears the denominators $\mu_{n+1}$ and $\mu_n$, using the nonzero facts $\mu_{n+1}\ne0$ and $\mu_n\ne0$. Since these denominators are in fact positive, clearing them is equivalent to multiplying the original inequality by the positive factor $\mu_n\mu_{n+1}$, giving exactly the product inequality already proved. Finally, `simpa` with commutativity and associativity rewrites the product inequality into the required normal form and applies the previously established fact.

- Case `.nondecreasing, .nonincreasing`: here $\delta_m=\beta_m$. The goal is

$$
\frac{\beta_{n+1}}{\beta_{n+1}}\le \frac{\beta_n}{\beta_n}.
$$

  Since $\beta_{n+1}\ne0$ and $\beta_n\ne0$, `field_simp` cancels these factors and reduces the goal to $1\le1$. The command `exact le_refl 1` then proves this by reflexivity of the order on the real numbers. In this case no monotonicity inequality is needed beyond the fact that the shape of $\delta$ is determined by the two behavior tags.

- Case `.nondecreasing, .nondecreasing`: here $\delta_m=\beta_m\mu_m$. The goal is

$$
\frac{\beta_{n+1}}{\beta_{n+1}\mu_{n+1}}
\le
\frac{\beta_n}{\beta_n\mu_n}.
$$

  Because $\beta_{n+1}$ and $\beta_n$ are nonzero, the $\beta$-factors cancel, leaving

$$
\frac{1}{\mu_{n+1}}\le \frac{1}{\mu_n}.
$$

  Since $\mu_{n+1}$ and $\mu_n$ are positive, multiplying by the positive product $\mu_n\mu_{n+1}$ preserves the inequality and gives

$$
\mu_n\le \mu_{n+1}.
$$

  The `field_simp` call performs these cancellations and cross-multiplications, using the nonzero facts for $\beta_n,\beta_{n+1},\mu_n,\mu_{n+1}$. Then `exact hμ_prop n` applies the $n$-th instance of the nondecreasing property of $\mu$, which is precisely $\mu_n\le \mu_{n+1}$. This closes the final case.

The proof does not use `rw` or `linarith`; the arithmetic and case reductions are handled by `unfold`, `have`, `match`, `simp`, `positivity`, `calc`, `field_simp`, `simpa`, and `exact`.

