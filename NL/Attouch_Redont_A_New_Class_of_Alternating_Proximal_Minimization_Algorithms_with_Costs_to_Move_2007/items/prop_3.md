## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/prop_3.lean`

## Lean statement
```lean
theorem proposition_4_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (x_seq y_seq : ℕ → H) (x y : H)
    (hα_nonneg : ∀ n, α n ≥ 0) (hν_nonneg : ∀ n, ν n ≥ 0)
    (hβ_pos : β > 0) (hμ_pos : μ > 0)
    (h_bound_a : ∀ n, ‖x_seq (n+1) - x‖ ^ 2 ≤
      (1 / (α n + β)) * (α n * ‖x_seq n - x‖ ^ 2 + β * ‖y_seq n - y‖ ^ 2))
    (h_bound_b : ∀ n, ‖y_seq (n+1) - y‖ ^ 2 ≤
      (1 / ((μ + ν n) * (α n + β))) * (μ * α n * ‖x_seq n - x‖ ^ 2 +
        (μ * β + ν n * (α n + β)) * ‖y_seq n - y‖ ^ 2)) :
    ∃ M : ℝ, ∀ n : ℕ, ‖x_seq n‖ ≤ M ∧ ‖y_seq n‖ ≤ M
```

## Statement explanation
The declaration `proposition_4_4` is a boundedness result for two sequences in a real inner product space. The space $H$ carries the norm $`\|\cdot\|`$, and the theorem has two unused function parameters$f,g:H\to\mathbb R$, which do not occur in the assumptions or the conclusion. The actual data are two sequences$x_n,y_n\in H$, two reference points$x,y\in H$, real parameters$\beta,\mu$, and real sequences$\alpha_n,\nu_n$.

The assumptions are:

- $\alpha_n\ge 0$ for every $n\in\mathbb N$;
- $\nu_n\ge 0$ for every $n\in\mathbb N$;
- $\beta\gt 0$;
- $\mu\gt 0$.

Writing

```math
A_n=\|x_n-x\|^2,\qquad B_n=\|y_n-y\|^2,
```

the first recursive bound says

$$
A_{n+1}\le \frac{1}{\alpha_n+\beta}\bigl(\alpha_n A_n+\beta B_n\bigr)
= \frac{\alpha_n A_n+\beta B_n}{\alpha_n+\beta}.
$$

The second recursive bound says

$$
B_{n+1}\le
\frac{1}{(\mu+\nu_n)(\alpha_n+\beta)}
\left(\mu\alpha_n A_n+\bigl(\mu\beta+\nu_n(\alpha_n+\beta)\bigr)B_n\right).
$$

Because $\alpha_n\ge 0$, $\nu_n\ge 0$, $\beta\gt 0$, and $\mu\gt 0$, the denominators are positive. Moreover, in the first bound the numerator coefficients $\alpha_n$ and $\beta$ have sum $\alpha_n+\beta$, and in the second bound the numerator coefficients have sum

$$
\mu\alpha_n+\mu\beta+\nu_n(\alpha_n+\beta)
=(\mu+\nu_n)(\alpha_n+\beta).
$$

Thus each right-hand side is a convex or weighted average of $A_n$ and $B_n$, hence is at most their maximum.

The conclusion is that there exists a real number $M$ such that for every $n\in\mathbb N$,

```math
\|x_n\|\le M
\quad\text{and}\quad
\|y_n\|\le M.
```

So the theorem asserts that both sequences are bounded in norm by one common constant.

## Lean proof
```lean
by
  -- Squared norms are nonnegative
  have h_sq_nonneg (z w : H) : ‖z - w‖ ^ 2 ≥ 0 := by positivity
  have h_norm_nonneg (z w : H) : ‖z - w‖ ≥ 0 := norm_nonneg _
  -- Step 1: each ‖x_{n+1} - x‖² ≤ max(‖x_n - x‖², ‖y_n - y‖²)
  have h_step_a : ∀ n, ‖x_seq (n+1) - x‖ ^ 2 ≤ max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
    intro n
    have hbound := h_bound_a n
    have hsum_pos : α n + β > 0 := by nlinarith [hα_nonneg n, hβ_pos]
    have h_num : α n * ‖x_seq n - x‖ ^ 2 + β * ‖y_seq n - y‖ ^ 2 ≤
        (α n + β) * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
      have h1 : α n * ‖x_seq n - x‖ ^ 2 ≤ α n * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (hα_nonneg n)
      have h2 : β * ‖y_seq n - y‖ ^ 2 ≤ β * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
      nlinarith
    have h_one_div_nonneg : 0 ≤ 1 / (α n + β) :=
      div_nonneg (by norm_num) (by linarith)
    have h_rhs : (1 / (α n + β)) * (α n * ‖x_seq n - x‖ ^ 2 + β * ‖y_seq n - y‖ ^ 2) ≤
        max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
      calc
        (1 / (α n + β)) * (α n * ‖x_seq n - x‖ ^ 2 + β * ‖y_seq n - y‖ ^ 2) ≤
            (1 / (α n + β)) * ((α n + β) * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h_num h_one_div_nonneg
        _ = ((α n + β) * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2)) / (α n + β) := by ring
        _ = max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) * ((α n + β) / (α n + β)) := by ring
        _ = max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) * 1 := by rw [div_self hsum_pos.ne.symm]
        _ = max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by ring
    exact le_trans hbound h_rhs
  -- Step 2: each ‖y_{n+1} - y‖² ≤ max(‖x_n - x‖², ‖y_n - y‖²)
  have h_step_b : ∀ n, ‖y_seq (n+1) - y‖ ^ 2 ≤ max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
    intro n
    have hbound := h_bound_b n
    have hden_pos : (μ + ν n) * (α n + β) > 0 := by
      have hμν_pos : μ + ν n > 0 := by nlinarith [hμ_pos, hν_nonneg n]
      have hαβ_pos : α n + β > 0 := by nlinarith [hα_nonneg n, hβ_pos]
      nlinarith
    have h_num : μ * α n * ‖x_seq n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖y_seq n - y‖ ^ 2 ≤
        (μ + ν n) * (α n + β) * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
      have h_μα_nonneg : μ * α n ≥ 0 := mul_nonneg (by linarith) (hα_nonneg n)
      have h_mix_nonneg : μ * β + ν n * (α n + β) ≥ 0 := by
        have hμβ_nonneg : μ * β ≥ 0 := mul_nonneg (by linarith) (by linarith)
        have hναβ_nonneg : ν n * (α n + β) ≥ 0 :=
          mul_nonneg (hν_nonneg n) (by nlinarith [hα_nonneg n, hβ_pos])
        nlinarith
      have h1 : μ * α n * ‖x_seq n - x‖ ^ 2 ≤ μ * α n * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) h_μα_nonneg
      have h2 : (μ * β + ν n * (α n + β)) * ‖y_seq n - y‖ ^ 2 ≤
          (μ * β + ν n * (α n + β)) * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) h_mix_nonneg
      nlinarith
    have h_one_div_nonneg : 0 ≤ 1 / ((μ + ν n) * (α n + β)) :=
      div_nonneg (by norm_num) (by nlinarith)
    have h_rhs : (1 / ((μ + ν n) * (α n + β))) *
        (μ * α n * ‖x_seq n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖y_seq n - y‖ ^ 2) ≤
        max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
      calc
        (1 / ((μ + ν n) * (α n + β))) *
            (μ * α n * ‖x_seq n - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖y_seq n - y‖ ^ 2) ≤
            (1 / ((μ + ν n) * (α n + β))) * ((μ + ν n) * (α n + β) *
              max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h_num h_one_div_nonneg
        _ = ((μ + ν n) * (α n + β) * max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2)) /
            ((μ + ν n) * (α n + β)) := by ring
        _ = max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) * (((μ + ν n) * (α n + β)) /
            ((μ + ν n) * (α n + β))) := by ring
        _ = max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) * 1 := by rw [div_self hden_pos.ne.symm]
        _ = max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by ring
    exact le_trans hbound h_rhs
  -- Step 3: max(‖x_{n+1} - x‖², ‖y_{n+1} - y‖²) ≤ max(‖x_n - x‖², ‖y_n - y‖²)
  have h_max_step : ∀ n, max (‖x_seq (n+1) - x‖ ^ 2) (‖y_seq (n+1) - y‖ ^ 2) ≤
      max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) := by
    intro n
    exact max_le (h_step_a n) (h_step_b n)
  -- Step 4: by induction, bounded by initial max
  set K := max (‖x_seq 0 - x‖ ^ 2) (‖y_seq 0 - y‖ ^ 2) with hK_def
  have hK_nonneg : K ≥ 0 := by
    rw [hK_def]
    have h0 : ‖x_seq 0 - x‖ ^ 2 ≥ 0 := h_sq_nonneg (x_seq 0) x
    exact le_max_of_le_left h0
  have h_max_bounded : ∀ n, max (‖x_seq n - x‖ ^ 2) (‖y_seq n - y‖ ^ 2) ≤ K := by
    intro n
    induction n with
    | zero => exact le_refl K
    | succ k ih => exact le_trans (h_max_step k) ih
  have hx_sq_bound : ∀ n, ‖x_seq n - x‖ ^ 2 ≤ K := by
    intro n
    have h := h_max_bounded n
    exact le_trans (le_max_left _ _) h
  have hy_sq_bound : ∀ n, ‖y_seq n - y‖ ^ 2 ≤ K := by
    intro n
    have h := h_max_bounded n
    exact le_trans (le_max_right _ _) h
  -- Step 5: from squared norm bound to norm bound, using ‖z‖ ≤ ‖z - w‖ + ‖w‖
  have h_norm_bound_sq_to_norm (r : ℝ) (hr : r ≥ 0) (hrsq : r ^ 2 ≤ K) : r ≤ K + 1 := by
    by_cases hle1 : r ≤ 1
    · nlinarith
    · have : r < r ^ 2 := by
        nlinarith
      nlinarith
  have hx_norm_bound : ∀ n, ‖x_seq n - x‖ ≤ K + 1 := by
    intro n
    apply h_norm_bound_sq_to_norm (‖x_seq n - x‖) (h_norm_nonneg (x_seq n) x) (hx_sq_bound n)
  have hy_norm_bound : ∀ n, ‖y_seq n - y‖ ≤ K + 1 := by
    intro n
    apply h_norm_bound_sq_to_norm (‖y_seq n - y‖) (h_norm_nonneg (y_seq n) y) (hy_sq_bound n)
  -- Step 6: construct M from the bounds
  set M := K + 1 + max ‖x‖ ‖y‖ with hM_def
  refine ⟨M, ?_⟩
  intro n
  have hx : ‖x_seq n‖ ≤ K + 1 + ‖x‖ := by
    calc
      ‖x_seq n‖ = ‖(x_seq n - x) + x‖ := by simp
      _ ≤ ‖x_seq n - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ (K + 1) + ‖x‖ := by nlinarith [hx_norm_bound n]
  have hy : ‖y_seq n‖ ≤ K + 1 + ‖y‖ := by
    calc
      ‖y_seq n‖ = ‖(y_seq n - y) + y‖ := by simp
      _ ≤ ‖y_seq n - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ (K + 1) + ‖y‖ := by nlinarith [hy_norm_bound n]
  have hxM : ‖x_seq n‖ ≤ M := by
    have hx' : ‖x‖ ≤ max ‖x‖ ‖y‖ := le_max_left _ _
    nlinarith
  have hyM : ‖y_seq n‖ ≤ M := by
    have hy' : ‖y‖ ≤ max ‖x‖ ‖y‖ := le_max_right _ _
    nlinarith
  exact And.intro hxM hyM
```

## Proof explanation
The proof first records two elementary facts. The auxiliary fact `h_sq_nonneg` says that for all $z,w\in H$,

```math
\|z-w\|^2\ge 0,
```

which is proved by `positivity` from the nonnegativity of the norm. The auxiliary fact `h_norm_nonneg` says that

```math
\|z-w\|\ge 0,
```

which is the standard nonnegativity of the norm.

The first main step proves, for every $n$,

```math
\|x_{n+1}-x\|^2\le \max\bigl(\|x_n-x\|^2,\|y_n-y\|^2\bigr).
```

After fixing $n$, the proof uses the hypothesis `h_bound_a n`, namely

$$
A_{n+1}\le \frac{\alpha_n A_n+\beta B_n}{\alpha_n+\beta}.
$$

Since $\alpha_n\ge 0$ and $\beta\gt 0$, the proof obtains $\alpha_n+\beta\gt 0$ by `nlinarith`. It then shows

$$
\alpha_n A_n+\beta B_n\le (\alpha_n+\beta)\max(A_n,B_n).
$$

Indeed, $A_n\le \max(A_n,B_n)$ and $B_n\le \max(A_n,B_n)$. Multiplying the first inequality by the nonnegative number $\alpha_n$, and the second by the nonnegative number $\beta$, is justified by `mul_le_mul_of_nonneg_left`, whose content is: if $u\le v$ and $c\ge 0$, then $cu\le cv$. Adding the two resulting inequalities gives the displayed inequality. Since $1/(\alpha_n+\beta)\ge 0$, multiplying by this nonnegative factor preserves the inequality:

$$
\frac{\alpha_n A_n+\beta B_n}{\alpha_n+\beta}
\le
\frac{(\alpha_n+\beta)\max(A_n,B_n)}{\alpha_n+\beta}.
$$

The proof uses `ring` to rearrange the algebraic expressions and `div_self` to replace

$$
\frac{\alpha_n+\beta}{\alpha_n+\beta}
$$

by $1$, because $\alpha_n+\beta\ne 0$. Hence the right-hand side is exactly $\max(A_n,B_n)$. Combining this with the hypothesis `h_bound_a n` by transitivity of $\le$, called `le_trans`, gives the first main bound.

The second main step is analogous and proves

```math
\|y_{n+1}-y\|^2\le \max\bigl(\|x_n-x\|^2,\|y_n-y\|^2\bigr).
```

The proof again fixes $n$ and uses `h_bound_b n`. The denominator

$$
(\mu+\nu_n)(\alpha_n+\beta)
$$

is positive: $\mu+\nu_n\gt 0$ because $\mu\gt 0$ and $\nu_n\ge 0$, while $\alpha_n+\beta\gt 0$ because $\alpha_n\ge 0$ and $\beta\gt 0$. The coefficient $\mu\alpha_n$ is nonnegative, and the coefficient

$$
\mu\beta+\nu_n(\alpha_n+\beta)
$$

is also nonnegative because $\mu\beta\ge 0$ and $\nu_n(\alpha_n+\beta)\ge 0$. Therefore the same multiplication-by-nonnegative-scalars argument gives

$$
\mu\alpha_n A_n+\bigl(\mu\beta+\nu_n(\alpha_n+\beta)\bigr)B_n
\le
(\mu+\nu_n)(\alpha_n+\beta)\max(A_n,B_n).
$$

Multiplying by

$$
\frac{1}{(\mu+\nu_n)(\alpha_n+\beta)}\ge 0
$$

preserves the inequality, and `ring` plus `div_self` cancel the positive denominator. Thus

$$
B_{n+1}\le \max(A_n,B_n).
$$

The third step observes that since both $A_{n+1}$ and $B_{n+1}$ are bounded above by $\max(A_n,B_n)$, their maximum is also bounded above by that same quantity:

$$
\max(A_{n+1},B_{n+1})\le \max(A_n,B_n).
$$

This uses `max_le`, whose content is: if $u\le c$ and $v\le c$, then $\max(u,v)\le c$.

The fourth step defines

```math
K=\max\bigl(\|x_0-x\|^2,\|y_0-y\|^2\bigr).
```

Since $`\|x_0-x\|^2\ge 0`$, the maximum$K$is nonnegative. The proof then uses induction on$n$ to show

$$
\max(A_n,B_n)\le K
$$

for every $n$. The base case $n=0$ is equality by definition of $K$. The induction step uses the third step to get

$$
\max(A_{k+1},B_{k+1})\le \max(A_k,B_k),
$$

and then the induction hypothesis gives $\max(A_k,B_k)\le K$. Transitivity yields the desired inequality for $k+1$. From

$$
\max(A_n,B_n)\le K
$$

the proof obtains separately

$$
A_n\le K,\qquad B_n\le K
$$

using the facts that $A_n\le \max(A_n,B_n)$ and $B_n\le \max(A_n,B_n)$.

The fifth step converts squared-norm bounds into ordinary norm bounds. The proof establishes that if $r\ge 0$ and $r^2\le K$, then

$$
r\le K+1.
$$

Indeed, if $r\le 1$, then $r\le K+1$ because $K\ge 0$. If $r\gt 1$, then $r\lt r^2$, and since $r^2\le K$, one has $r\le K+1$. Applying this with $`r=\|x_n-x\|`$and$`r=\|y_n-y\|`$ gives

```math
\|x_n-x\|\le K+1,\qquad
\|y_n-y\|\le K+1
```

for every $n$.

Finally, the proof sets

```math
M=K+1+\max(\|x\|,\|y\|).
```

For each $n$, the triangle inequality `norm_add_le`, applied to $x_n-x$ and $x$, gives

```math
\|x_n\|
=\|(x_n-x)+x\|
\le \|x_n-x\|+\|x\|
\le (K+1)+\|x\|.
```

Since $`\|x\|\le \max(\|x\|,\|y\|)`$, it follows that

```math
\|x_n\|\le K+1+\max(\|x\|,\|y\|)=M.
```

The same argument with $y_n-y$ and $y$ gives

```math
\|y_n\|\le M.
```

Thus the existential goal

```math
\exists M:\mathbb R,\ \forall n:\mathbb N,\ \|x_n\|\le M\land \|y_n\|\le M
```

is closed by providing the witness $M$ and proving both inequalities for an arbitrary $n$.

