## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/lem_3.lean`

## Lean statement
```lean
theorem lemma_4_3_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hyp : H41toH46 H f g β μ) (x y : H)
    (hα_nonneg : ∀ n : ℕ, α n ≥ 0) (hν_nonneg : ∀ n : ℕ, ν n ≥ 0)
    (alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
            (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν)
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
             (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 x y) (n : ℕ) :
    α n * μ * ‖alg.x (n+1) - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y (n+1) - y‖ ^ 2 ≤
    α n * μ * ‖alg.x n - x‖ ^ 2 + β * (μ + ν n) * ‖alg.y n - y‖ ^ 2 -
    α n * μ * ‖alg.x (n+1) - alg.x n‖ ^ 2 -
    β * ν n * ‖alg.y (n+1) - alg.y n‖ ^ 2 -
    β * μ * ‖alg.y n - alg.x (n+1) - y + x‖ ^ 2 -
    β * μ * ‖alg.y (n+1) - alg.x (n+1) - y + x‖ ^ 2
```

## Statement explanation
The declaration `lemma_4_3_c` is a theorem about two sequences in a real inner product space $H$. The ambient assumptions on $H$ are that it is a normed additive commutative group and a real inner product space, so expressions such as $`\|u-v\|^2`$are squared distances in$H$. The data are functions$f,g:H\to\mathbb R$, real parameters$\beta,\mu$, sequences$\alpha,\nu:\mathbb N\to\mathbb R$, a bundled hypothesis `hyp : H41toH46 H f g β μ`, reference points $x,y\in H$, global nonnegativity assumptions $hα_nonneg:\forall n,\ \alpha_n\ge0$ and $hν_nonneg:\forall n,\ \nu_n\ge0$, an algorithm/iteration object `alg : CA2 ...`, and an additional bundled condition `hine : IsINE ...`. The object `alg` supplies the two iterate sequences; write

$$
x_n:=\mathrm{alg.x}(n),\qquad y_n:=\mathrm{alg.y}(n).
$$

The three functions $`(\xi,\eta)\mapsto \|\xi-\eta\|^2/2`$ supplied to `CA2` and to `IsINE` are the quadratic move-cost functions used in the hypotheses; the definitions of `H41toH46`, `CA2`, and `IsINE` are not expanded here. From `hyp` the proof uses the positivity fields `hyp.beta_pos` and `hyp.mu_pos`, so the bundled hypothesis supplies $\beta\gt 0$ and $\mu\gt 0$.

For every natural number $n$, the theorem concludes

```math
\begin{aligned}
&\alpha_n \mu \|x_{n+1}-x\|^2+\beta(\mu+\nu_n)\|y_{n+1}-y\|^2 \\
&\le
\alpha_n \mu \|x_n-x\|^2+\beta(\mu+\nu_n)\|y_n-y\|^2 \\
&\quad -\alpha_n \mu \|x_{n+1}-x_n\|^2
-\beta \nu_n \|y_{n+1}-y_n\|^2 \\
&\quad -\beta \mu \|y_n-x_{n+1}-y+x\|^2
-\beta \mu \|y_{n+1}-x_{n+1}-y+x\|^2.
\end{aligned}
```

Mathematically, this is a one-step weighted descent estimate. The left side is a weighted sum of squared distances of the next iterates $x_{n+1},y_{n+1}$ from the reference points $x,y$. The right side is the corresponding weighted sum for the current iterates $x_n,y_n$, minus nonnegative penalty terms: $`\alpha_n\mu\|x_{n+1}-x_n\|^2`$penalizes movement of the$x$-sequence,$`\beta\nu_n\|y_{n+1}-y_n\|^2`$penalizes movement of the$y$-sequence, and the last two terms penalize the discrepancies$`\|(y_n-y)-(x_{n+1}-x)\|^2`$and$`\|(y_{n+1}-y)-(x_{n+1}-x)\|^2`$. The weights in the subtracted terms are nonnegative because$\alpha_n,\nu_n\ge0$and$\beta,\mu>0$.

## Lean proof
```lean
by
  set xn1 := alg.x (n+1)
  set xn := alg.x n
  set yn1 := alg.y (n+1)
  set yn := alg.y n
  have hβpos : β > 0 := hyp.beta_pos
  have hμpos : μ > 0 := hyp.mu_pos
  have hα_nonneg_n : α n ≥ 0 := hα_nonneg n
  have hν_nonneg_n : ν n ≥ 0 := hν_nonneg n
  have h_adenom_pos : α n + β > 0 := by linarith
  have ha := lemma_4_3_a hyp x y hα_nonneg hν_nonneg alg hine n
  have hb := lemma_4_3_b hyp x y hα_nonneg hν_nonneg alg hine n
  -- Clear denominators: multiply ha by (α_n+β), multiply hb by (μ+ν_n)(α_n+β)
  have ha_mul : (α n + β) * ‖xn1 - x‖ ^ 2 ≤
      α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2 := by
    calc
      (α n + β) * ‖xn1 - x‖ ^ 2 ≤ (α n + β) * ((1 / (α n + β)) *
        (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left ha (by linarith)
      _ = α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2 := by
        field_simp [h_adenom_pos.ne']
  have hb_mul : (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2 ≤
      μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
      μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
      μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2 := by
    have hbden_pos : (μ + ν n) * (α n + β) > 0 := by positivity
    calc
      (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2 ≤
          (μ + ν n) * (α n + β) * ((1 / ((μ + ν n) * (α n + β))) *
            (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
             μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
             μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
          μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
          μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2 := by
        field_simp [hbden_pos.ne']
  -- Now multiply ha_mul by α_n·μ, and hb_mul by β
  have h1 : α n * μ * (α n + β) * ‖xn1 - x‖ ^ 2 ≤
      α n * μ * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2) := by
    have h_nonneg : 0 ≤ α n * μ := by nlinarith
    have htemp := mul_le_mul_of_nonneg_left ha_mul h_nonneg
    simpa [mul_assoc] using htemp
  have h2 : β * ((μ + ν n) * (α n + β)) * ‖yn1 - y‖ ^ 2 ≤
      β * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2) := by
    have h_nonneg : 0 ≤ β := by linarith
    have htemp := mul_le_mul_of_nonneg_left hb_mul h_nonneg
    simpa [mul_assoc] using htemp
  -- Add h1 and h2
  have h_add : (α n * μ * (α n + β) * ‖xn1 - x‖ ^ 2) + (β * (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2) ≤
      (α n * μ * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) +
      (β * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2)) := by
    nlinarith
  -- Factor (α_n+β) from both sides using ring
  have h_lhs_expand : (α n * μ * (α n + β) * ‖xn1 - x‖ ^ 2) + (β * (μ + ν n) * (α n + β) * ‖yn1 - y‖ ^ 2) =
      (α n + β) * (α n * μ * ‖xn1 - x‖ ^ 2 + β * (μ + ν n) * ‖yn1 - y‖ ^ 2) := by ring
  have h_rhs_expand : (α n * μ * (α n * ‖xn - x‖ ^ 2 + β * ‖yn - y‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - y + x‖ ^ 2)) +
      (β * (μ * α n * ‖xn - x‖ ^ 2 + (μ * β + ν n * (α n + β)) * ‖yn - y‖ ^ 2 -
        μ * α n * ‖xn1 - xn‖ ^ 2 - ν n * (α n + β) * ‖yn1 - yn‖ ^ 2 -
        μ * β * ‖yn - xn1 - y + x‖ ^ 2 - μ * (α n + β) * ‖yn1 - xn1 - y + x‖ ^ 2)) =
      (α n + β) * (α n * μ * ‖xn - x‖ ^ 2 + β * (μ + ν n) * ‖yn - y‖ ^ 2 -
        α n * μ * ‖xn1 - xn‖ ^ 2 - β * ν n * ‖yn1 - yn‖ ^ 2 -
        β * μ * ‖yn - xn1 - y + x‖ ^ 2 - β * μ * ‖yn1 - xn1 - y + x‖ ^ 2) := by ring
  rw [h_lhs_expand, h_rhs_expand] at h_add
  -- Cancel (α_n+β) > 0: h_add has form c * LHS' ≤ c * RHS' with c = α_n+β > 0
  -- Use le_of_mul_le_mul_left: 0 < c → c*a ≤ c*b → a ≤ b
  exact le_of_mul_le_mul_left h_add h_adenom_pos
```

## Proof explanation
The proof begins by introducing local abbreviations:

$$
x_{n+1}:=\mathrm{alg.x}(n+1),\quad
x_n:=\mathrm{alg.x}(n),\quad
y_{n+1}:=\mathrm{alg.y}(n+1),\quad
y_n:=\mathrm{alg.y}(n).
$$

The `set` commands only create notation and do not change the mathematical content. Next, `hyp.beta_pos` and `hyp.mu_pos` give $\beta\gt 0$ and $\mu\gt 0$. Specializing the global nonnegativity hypotheses gives $\alpha_n\ge0$ and $\nu_n\ge0$. From $\alpha_n\ge0$ and $\beta\gt 0$, `linarith` proves

$$
\alpha_n+\beta>0.
$$

Later `positivity` proves

$$
(\mu+\nu_n)(\alpha_n+\beta)>0,
$$

using $\mu\gt 0$, $\nu_n\ge0$, and $\alpha_n+\beta\gt 0$.

The proof then invokes the two previous estimates. The first, `lemma_4_3_a`, with the same hypotheses `hyp`, reference points $x,y$, global nonnegativity of $\alpha,\nu$, the same `alg` and `hine`, and the current index $n$, gives

```math
\|x_{n+1}-x\|^2
\le \frac{1}{\alpha_n+\beta}
\Bigl(
\alpha_n\|x_n-x\|^2+\beta\|y_n-y\|^2
-\alpha_n\|x_{n+1}-x_n\|^2
-\beta\|y_n-x_{n+1}-y+x\|^2
\Bigr).
```

This is an upper bound for the squared distance of the new $x$-iterate from $x$, with a denominator $\alpha_n+\beta$. The second, `lemma_4_3_b`, with the same data and index $n$, gives

```math
\begin{aligned}
\|y_{n+1}-y\|^2
&\le \frac{1}{(\mu+\nu_n)(\alpha_n+\beta)}
\Bigl(
\mu\alpha_n\|x_n-x\|^2
+(\mu\beta+\nu_n(\alpha_n+\beta))\|y_n-y\|^2 \\
&\qquad
-\mu\alpha_n\|x_{n+1}-x_n\|^2
-\nu_n(\alpha_n+\beta)\|y_{n+1}-y_n\|^2 \\
&\qquad
-\mu\beta\|y_n-x_{n+1}-y+x\|^2
-\mu(\alpha_n+\beta)\|y_{n+1}-x_{n+1}-y+x\|^2
\Bigr).
\end{aligned}
```

This is the corresponding upper bound for the squared distance of the new $y$-iterate from $y$.

The next step clears denominators. The proof multiplies the first estimate by the positive scalar $\alpha_n+\beta$. The tactic `mul_le_mul_of_nonneg_left` is the elementary fact that if $a\le b$ and $0\le c$, then $ca\le cb$; here $c=\alpha_n+\beta$. Then `field_simp` cancels the nonzero denominator $1/(\alpha_n+\beta)$. The resulting inequality is

```math
\begin{aligned}
&(\alpha_n+\beta)\|x_{n+1}-x\|^2 \\
&\le \alpha_n\|x_n-x\|^2+\beta\|y_n-y\|^2
-\alpha_n\|x_{n+1}-x_n\|^2
-\beta\|y_n-x_{n+1}-y+x\|^2.
\end{aligned}
```

Similarly, the proof multiplies the second estimate by the positive scalar

$$
D:=(\mu+\nu_n)(\alpha_n+\beta).
$$

Again `mul_le_mul_of_nonneg_left` preserves the inequality, and `field_simp` cancels the denominator. This yields

```math
\begin{aligned}
&D\|y_{n+1}-y\|^2 \\
&\le \mu\alpha_n\|x_n-x\|^2
+(\mu\beta+\nu_n(\alpha_n+\beta))\|y_n-y\|^2 \\
&\qquad
-\mu\alpha_n\|x_{n+1}-x_n\|^2
-\nu_n(\alpha_n+\beta)\|y_{n+1}-y_n\|^2 \\
&\qquad
-\mu\beta\|y_n-x_{n+1}-y+x\|^2
-\mu(\alpha_n+\beta)\|y_{n+1}-x_{n+1}-y+x\|^2.
\end{aligned}
```

Now the proof weights the two cleared estimates so that the final factor $\alpha_n+\beta$ can be canceled. It multiplies the first cleared inequality by $\alpha_n\mu$. The fact $0\le \alpha_n\mu$ follows from $\alpha_n\ge0$ and $\mu\gt 0$ by `nlinarith`; then `mul_le_mul_of_nonneg_left` multiplies the inequality, and `simpa [mul_assoc]` only reassociates products. The resulting inequality has left side

```math
\alpha_n\mu(\alpha_n+\beta)\|x_{n+1}-x\|^2
```

and right side equal to $\alpha_n\mu$ times the bracketed right-hand side of the first cleared inequality. Similarly, the proof multiplies the second cleared inequality by $\beta$. Since $\beta\gt 0$, $\beta$ is nonnegative; `mul_le_mul_of_nonneg_left` preserves the inequality, and `simpa [mul_assoc]` reassociates products, giving a left side

```math
\beta(\mu+\nu_n)(\alpha_n+\beta)\|y_{n+1}-y\|^2.
```

Adding these two weighted inequalities by `nlinarith` gives `h_add`: the sum of the two weighted left sides is bounded above by the sum of the two weighted right sides.

The remaining task is to factor $\alpha_n+\beta$ from both sides. The proof uses `ring` to verify two polynomial identities, treating each norm-squared expression as an atom. The left side factors as

```math
(\alpha_n+\beta)\Bigl(
\alpha_n\mu\|x_{n+1}-x\|^2
+\beta(\mu+\nu_n)\|y_{n+1}-y\|^2
\Bigr).
```

The right side factors as

```math
\begin{aligned}
&(\alpha_n+\beta)\Bigl(
\alpha_n\mu\|x_n-x\|^2
+\beta(\mu+\nu_n)\|y_n-y\|^2 \\
&\qquad
-\alpha_n\mu\|x_{n+1}-x_n\|^2
-\beta\nu_n\|y_{n+1}-y_n\|^2 \\
&\qquad
-\beta\mu\|y_n-x_{n+1}-y+x\|^2
-\beta\mu\|y_{n+1}-x_{n+1}-y+x\|^2
\Bigr).
\end{aligned}
```

The `rw` command rewrites the two sides of `h_add` using these identities. Thus `h_add` becomes an inequality of the form

$$
(\alpha_n+\beta)L\le(\alpha_n+\beta)R,
$$

where $L$ is the left side of the target inequality and $R$ is its right side. Since $\alpha_n+\beta\gt 0$, the final command `exact le_of_mul_le_mul_left h_add h_adenom_pos` applies the cancellation rule: for a positive scalar $c$, $ca\le cb$ implies $a\le b$. Therefore $L\le R$, which is exactly the stated conclusion of `lemma_4_3_c`.

