## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/cor_1.lean`

## Lean statement
```lean
theorem cor_2_1 (f : H → ℝ) (α : ℝ) (hα : α ≥ 1) (A : SetValuedOperator H H)
    (hA : ∀ x, A x = {v | ∀ y, (fun (z : H) => ‖z‖^α) y ≥ (fun (z : H) => ‖z‖^α) x + inner ℝ v (y - x)})
    (B : SetValuedOperator H H) (hB : ∀ x, B x = {v | ∀ y, f y ≥ f x + inner ℝ v (y - x)})
    (hf_conv : ConvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    (hdom : (SetValuedOperator.dom B).Nonempty)
    (hinf : ∃ m, ∀ x, f x ≥ m) (lam : ℕ → ℝ) (hlam_pos : ∀ n, lam n > 0)
    (hlam_nondec : ∀ n, lam n ≤ lam (n+1)) (x : ℕ → H) (halg : AlgorithmA A B x lam) :
    ∃ (C : ℝ), Tendsto (fun (N : ℕ) => (Finset.range (N+1)).sum (fun n =>
      ‖(lam n)⁻¹ • (x (n+2) - x (n+1))‖^α)) atTop (𝓝 C)
```

## Statement explanation
The declaration concerns a real inner product space $H$, a real-valued function $f:H\to\mathbb R$, a real number $\alpha$, two set-valued operators $A,B$ from $H$ to $H$, a sequence of positive nondecreasing parameters $\lambda:\mathbb N\to\mathbb R$, and a sequence $x:\mathbb N\to H$.

The hypotheses say the following. First, $\alpha\ge 1$. Second, for every $u\in H$, the set $A u$ is exactly the subdifferential of the function $`z\mapsto \|z\|^\alpha`$at$u$:

```math
A u=\left\{v\in H:\ \forall y\in H,\ \|y\|^\alpha\ge \|u\|^\alpha+\langle v,y-u\rangle\right\}.
```

Third, for every $u\in H$, the set $B u$ is exactly the subdifferential of $f$ at $u$:

```math
B u=\left\{v\in H:\ \forall y\in H,\ f(y)\ge f(u)+\langle v,y-u\rangle\right\}.
```

Fourth, $f$ is convex on all of $H$, lower semicontinuous, its domain-like operator $B$ has nonempty domain, and $f$ is bounded below by some real number $m$. Fifth, every $\lambda_n\gt 0$ and the sequence $\lambda$ is nondecreasing: $\lambda_n\le \lambda_{n+1}$. Finally, $x$ satisfies the algorithmic relation `AlgorithmA A B x lam`. The proof shows that the only part of that relation used is the step relation

```math
0\in \left\{\lambda_n^{-2}\bigl(x_{n+2}-2x_{n+1}+x_n\bigr)\right\}
+A\!\left(\lambda_n^{-1}(x_{n+2}-x_{n+1})\right)
+B(x_{n+2})
```

for every $n$.

The conclusion is that there exists a real number $C$ such that

```math
\sum_{n=0}^{N}\left\|\lambda_n^{-1}\bigl(x_{n+2}-x_{n+1}\bigr)\right\|^\alpha
\longrightarrow C
\qquad (N\to\infty).
```

Thus the partial sums of the residuals

```math
\left\|\lambda_n^{-1}\bigl(x_{n+2}-x_{n+1}\bigr)\right\|^\alpha
```

converge; equivalently, the series of these nonnegative residuals is summable. The proof actually exhibits $C$ as the infinite sum of those terms. The assumptions that $f$ is convex, lower semicontinuous, and that $B$ has nonempty domain are present in the statement, but the displayed proof does not use them.

## Lean proof
```lean
by
  classical
  let vel : ℕ → H := fun n => (lam n)⁻¹ • (x (n+2) - x (n+1))
  let term : ℕ → ℝ := fun n => ‖vel n‖^α
  let weighted : ℕ → ℝ := fun n => lam n * term n
  let energy : ℕ → ℝ := fun n =>
    ((2 * (lam n)^2)⁻¹) * ‖x (n+1) - x n‖^2 + f (x (n+1))
  have hterm_nonneg : ∀ n, 0 ≤ term n := by
    intro n
    exact Real.rpow_nonneg (norm_nonneg _) α
  have henergy_drop : ∀ n, energy (n+1) - energy n ≤ -weighted n := by
    intro n
    let d₁ : H := x (n+1) - x n
    let d₂ : H := x (n+2) - x (n+1)
    let v : H := (lam n)⁻¹ • d₂
    let acc : H := ((lam n)^2)⁻¹ • (x (n+2) - 2 • x (n+1) + x n)
    have hstep : (0 : H) ∈ ({acc} : Set H) + A v + B (x (n+2)) := by
      simpa [AlgorithmA, acc, v, d₂] using halg.step n
    rw [Set.mem_add] at hstep
    rcases hstep with ⟨p, hp, b, hb, hpbeq⟩
    rw [Set.mem_add] at hp
    rcases hp with ⟨a, ha, y, hyA, hp_eq⟩
    rw [Set.mem_singleton_iff] at ha
    subst a
    have hsum_zero : acc + y + b = 0 := by
      simpa [hp_eq] using hpbeq
    have hbsub : ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ b (t - x (n+2)) := by
      have hb' : b ∈ {v | ∀ t : H, f t ≥ f (x (n+2)) + inner ℝ v (t - x (n+2))} := by
        simpa [hB] using hb
      simpa using hb'
    have hf_diff : f (x (n+2)) - f (x (n+1)) ≤ inner ℝ b d₂ := by
      have h := hbsub (x (n+1))
      have hinner : inner ℝ b (x (n+1) - x (n+2)) = - inner ℝ b d₂ := by
        rw [show x (n+1) - x (n+2) = -(x (n+2) - x (n+1)) by abel]
        rw [inner_neg_right]
      linarith
    have hcoeff :
        (2 * (lam (n+1))^2)⁻¹ * ‖d₂‖^2 ≤
          (2 * (lam n)^2)⁻¹ * ‖d₂‖^2 := by
      have hln : 0 < lam n := hlam_pos n
      have hln1 : 0 < lam (n+1) := lt_of_lt_of_le hln (hlam_nondec n)
      have habs : |lam n| ≤ |lam (n+1)| := by
        simpa [abs_of_pos hln, abs_of_pos hln1] using hlam_nondec n
      have hden : 2 * (lam n)^2 ≤ 2 * (lam (n+1))^2 := by
        nlinarith [sq_le_sq.mpr habs]
      have hdenpos : 0 < 2 * (lam n)^2 := by positivity
      have hinv : (2 * (lam (n+1))^2)⁻¹ ≤ (2 * (lam n)^2)⁻¹ := by
        exact inv_anti₀ hdenpos hden
      exact mul_le_mul_of_nonneg_right hinv (sq_nonneg _)
    have henergy_le :
        energy (n+1) - energy n ≤
          (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := by
      dsimp [energy, d₁, d₂]
      linarith
    have hnorm :
        ‖d₂‖^2 - ‖d₁‖^2 ≤ 2 * inner ℝ (d₂ - d₁) d₂ := by
      have hnon : 0 ≤ ‖d₂ - d₁‖^2 := sq_nonneg _
      rw [norm_sub_sq_real] at hnon
      rw [real_inner_comm d₁ d₂] at hnon
      rw [inner_sub_left]
      rw [real_inner_self_eq_norm_sq]
      nlinarith [hnon]
    have hnorm_scaled :
        (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) ≤
          ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
      have hscale_nonneg : 0 ≤ (2 * (lam n)^2)⁻¹ := by positivity
      have hmul := mul_le_mul_of_nonneg_left hnorm hscale_nonneg
      have hscale_eq :
          (2 * (lam n)^2)⁻¹ * (2 * inner ℝ (d₂ - d₁) d₂) =
            ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
        field_simp [ne_of_gt (hlam_pos n)]
      calc
        (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2)
            ≤ (2 * (lam n)^2)⁻¹ * (2 * inner ℝ (d₂ - d₁) d₂) := hmul
        _ = ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := hscale_eq
    have hacc_eq : acc = ((lam n)^2)⁻¹ • (d₂ - d₁) := by
      dsimp [acc, d₁, d₂]
      congr 1
      abel
    have hacc_inner :
        inner ℝ acc d₂ = ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ := by
      rw [hacc_eq, inner_smul_left]
      rfl
    have henergy_acc :
        energy (n+1) - energy n ≤ inner ℝ (acc + b) d₂ := by
      calc
        energy (n+1) - energy n
            ≤ (2 * (lam n)^2)⁻¹ * (‖d₂‖^2 - ‖d₁‖^2) + inner ℝ b d₂ := henergy_le
        _ ≤ ((lam n)^2)⁻¹ * inner ℝ (d₂ - d₁) d₂ + inner ℝ b d₂ := by
          linarith
        _ = inner ℝ (acc + b) d₂ := by
          rw [← hacc_inner, inner_add_left]
    have haccb : acc + b = -y := by
      calc
        acc + b = (acc + y + b) - y := by abel
        _ = 0 - y := by rw [hsum_zero]
        _ = -y := by simp
    have henergy_y : energy (n+1) - energy n ≤ - inner ℝ y d₂ := by
      calc
        energy (n+1) - energy n ≤ inner ℝ (acc + b) d₂ := henergy_acc
        _ = inner ℝ (-y) d₂ := by rw [haccb]
        _ = - inner ℝ y d₂ := by rw [inner_neg_left]
    have hd₂_eq : d₂ = (lam n) • v := by
      dsimp [v]
      rw [smul_smul]
      field_simp [ne_of_gt (hlam_pos n)]
      simp
    have hinner_d₂ : inner ℝ y d₂ = (lam n) * inner ℝ y v := by
      rw [hd₂_eq, inner_smul_right]
    have hsubA : ∀ t : H, ‖t‖^α ≥ ‖v‖^α + inner ℝ y (t - v) := by
      have hy' : y ∈ {u | ∀ t : H, ‖t‖^α ≥ ‖v‖^α + inner ℝ u (t - v)} := by
        simpa [hA] using hyA
      simpa using hy'
    have hinner_ge : ‖v‖^α ≤ inner ℝ y v := by
      have h := hsubA 0
      have hα_pos : 0 < α := lt_of_lt_of_le zero_lt_one hα
      have hzero : ‖(0 : H)‖^α = 0 := by
        simp [Real.zero_rpow, ne_of_gt hα_pos]
      rw [hzero] at h
      rw [zero_sub, inner_neg_right] at h
      linarith
    have hfinal : -(lam n) * inner ℝ y v ≤ -(lam n) * ‖v‖^α := by
      nlinarith [hlam_pos n, hinner_ge]
    calc
      energy (n+1) - energy n ≤ - inner ℝ y d₂ := henergy_y
      _ = -(lam n) * inner ℝ y v := by
        rw [hinner_d₂]
        ring
      _ ≤ -(lam n) * ‖v‖^α := hfinal
      _ = -weighted n := by
        simp [weighted, term, vel, v, d₂]
  rcases hinf with ⟨m, hm⟩
  have hweighted_le_energy : ∀ n, weighted n ≤ energy n - energy (n+1) := by
    intro n
    have h := henergy_drop n
    linarith
  have henergy_lower : ∀ N, m ≤ energy N := by
    intro N
    have hf_lower : m ≤ f (x (N+1)) := hm (x (N+1))
    have hcoeff_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ := by positivity
    have hnorm_nonneg : 0 ≤ ‖x (N+1) - x N‖^2 := sq_nonneg _
    have hprod_nonneg : 0 ≤ (2 * (lam N)^2)⁻¹ * ‖x (N+1) - x N‖^2 :=
      mul_nonneg hcoeff_nonneg hnorm_nonneg
    dsimp [energy]
    nlinarith
  have hweighted_sum_bound :
      ∀ N, (Finset.range N).sum weighted ≤ energy 0 - m := by
    intro N
    have hsum_le_energy :
        (Finset.range N).sum weighted ≤
          (Finset.range N).sum (fun n => energy n - energy (n+1)) := by
      exact Finset.sum_le_sum (fun n _ => hweighted_le_energy n)
    have htel :
        (Finset.range N).sum (fun n => energy n - energy (n+1)) =
          energy 0 - energy N := by
      exact Finset.sum_range_sub' energy N
    calc
      (Finset.range N).sum weighted
          ≤ (Finset.range N).sum (fun n => energy n - energy (n+1)) := hsum_le_energy
      _ = energy 0 - energy N := htel
      _ ≤ energy 0 - m := by
        linarith [henergy_lower N]
  have hlam0_le : ∀ n, lam 0 ≤ lam n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact le_trans ih (hlam_nondec n)
  have hterm_le_scaled : ∀ n, term n ≤ (lam 0)⁻¹ * weighted n := by
    intro n
    have h0pos : 0 < lam 0 := hlam_pos 0
    have hscale_nonneg : 0 ≤ (lam 0)⁻¹ := inv_nonneg.mpr (le_of_lt h0pos)
    have hmul := mul_le_mul_of_nonneg_right (hlam0_le n) (hterm_nonneg n)
    calc
      term n = (lam 0)⁻¹ * (lam 0 * term n) := by
        field_simp [ne_of_gt h0pos]
      _ ≤ (lam 0)⁻¹ * (lam n * term n) := by
        exact mul_le_mul_of_nonneg_left hmul hscale_nonneg
      _ = (lam 0)⁻¹ * weighted n := by
        rfl
  have hsum_bound :
      ∀ N, (Finset.range N).sum term ≤ (lam 0)⁻¹ * (energy 0 - m) := by
    intro N
    have hsum_scaled :
        (Finset.range N).sum term ≤
          (Finset.range N).sum (fun n => (lam 0)⁻¹ * weighted n) := by
      exact Finset.sum_le_sum (fun n _ => hterm_le_scaled n)
    have hscale_nonneg : 0 ≤ (lam 0)⁻¹ := inv_nonneg.mpr (le_of_lt (hlam_pos 0))
    calc
      (Finset.range N).sum term
          ≤ (Finset.range N).sum (fun n => (lam 0)⁻¹ * weighted n) := hsum_scaled
      _ = (lam 0)⁻¹ * (Finset.range N).sum weighted := by
        simp [Finset.mul_sum]
      _ ≤ (lam 0)⁻¹ * (energy 0 - m) := by
        exact mul_le_mul_of_nonneg_left (hweighted_sum_bound N) hscale_nonneg
  have hsummable : Summable term := summable_of_sum_range_le hterm_nonneg hsum_bound
  refine ⟨∑' n, term n, ?_⟩
  have ht := hsummable.hasSum.tendsto_sum_nat
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id
  simpa [term, vel] using ht.comp hshift
```

## Proof explanation
The proof begins with `classical`, which only permits classical logic and does not affect the mathematics. It then introduces four auxiliary sequences:

```math
v_n:=\lambda_n^{-1}\bigl(x_{n+2}-x_{n+1}\bigr),
\qquad
t_n:=\|v_n\|^\alpha,
```

```math
w_n:=\lambda_n t_n,
\qquad
E_n:=\frac{1}{2\lambda_n^2}\|x_{n+1}-x_n\|^2+f(x_{n+1}).
```

Here $E_n$ is an energy or Lyapunov quantity. The main goal is to prove that the $t_n$ are summable.

First, the proof shows $t_n\ge 0$ for every $n$. Since a norm is nonnegative, this follows from the fact that a real power of a nonnegative number is nonnegative. In Lean this is the lemma `Real.rpow_nonneg`.

Next comes the central estimate:

$$
E_{n+1}-E_n\le -w_n.
$$

This is proved for an arbitrary $n$. Let

$$
d_1:=x_{n+1}-x_n,\qquad d_2:=x_{n+2}-x_{n+1},
$$

and

$$
v:=\lambda_n^{-1}d_2,\qquad
\mathrm{acc}:=\lambda_n^{-2}\bigl(x_{n+2}-2x_{n+1}+x_n\bigr).
$$

The algorithmic step for this $n$ gives

```math
0\in \{\mathrm{acc}\}+A v+B(x_{n+2}).
```

The proof rewrites membership in a Minkowski sum using `Set.mem_add`. This membership says that a point belongs to $S+T$ exactly when it is the sum of one point of $S$ and one point of $T$. Applying this twice decomposes the algorithmic inclusion into the existence of

```math
p\in \{\mathrm{acc}\}+A v,\qquad b\in B(x_{n+2}),\qquad p+b=0,
```

and then into the existence of

$$
y\in A v,\qquad \mathrm{acc}+y=p.
$$

Because $`p\in\{\mathrm{acc}\}+A v`$, the singleton-membership lemma `Set.mem_singleton_iff` gives the first summand as $\mathrm{acc}$, after which `subst` replaces it. Hence

$$
\mathrm{acc}+y+b=0.
$$

From $b\in B(x_{n+2})$ and the definition of $B$, the proof obtains the subgradient inequality

$$
\forall z\in H,\qquad f(z)\ge f(x_{n+2})+\langle b,z-x_{n+2}\rangle.
$$

Taking $z=x_{n+1}$ and rewriting

$$
x_{n+1}-x_{n+2}=-(x_{n+2}-x_{n+1})=-d_2
$$

using the inner-product identity $\langle b,-d_2\rangle=-\langle b,d_2\rangle$, it follows that

$$
f(x_{n+2})-f(x_{n+1})\le \langle b,d_2\rangle.
$$

The proof also compares the kinetic coefficients. Since $\lambda_n\gt 0$ and $\lambda_n\le \lambda_{n+1}$, we have

$$
0<2\lambda_n^2\le 2\lambda_{n+1}^2,
$$

so

$$
\frac{1}{2\lambda_{n+1}^2}\le \frac{1}{2\lambda_n^2}.
$$

Multiplying by the nonnegative quantity $`\|d_2\|^2`$ gives

```math
\frac{1}{2\lambda_{n+1}^2}\|d_2\|^2
\le
\frac{1}{2\lambda_n^2}\|d_2\|^2.
```

Combining this with the previous subgradient estimate yields

```math
E_{n+1}-E_n
\le
\frac{1}{2\lambda_n^2}\bigl(\|d_2\|^2-\|d_1\|^2\bigr)
+\langle b,d_2\rangle.
```

This is the step where the proof uses `linarith` to combine the two inequalities after unfolding the definition of $E$.

Next the proof estimates the difference of squared norms. From the nonnegativity of $`\|d_2-d_1\|^2`$, expanding the square and rewriting the real inner product by symmetry gives

```math
\|d_2\|^2-\|d_1\|^2
\le
2\langle d_2-d_1,d_2\rangle.
```

The Lean proof uses `norm_sub_sq_real`, `real_inner_comm`, `inner_sub_left`, and `real_inner_self_eq_norm_sq`, then finishes with `nlinarith`. Multiplying by the nonnegative factor $\frac{1}{2\lambda_n^2}$ gives

```math
\frac{1}{2\lambda_n^2}\bigl(\|d_2\|^2-\|d_1\|^2\bigr)
\le
\frac{1}{\lambda_n^2}\langle d_2-d_1,d_2\rangle.
```

But

$$
d_2-d_1=(x_{n+2}-x_{n+1})-(x_{n+1}-x_n)
=x_{n+2}-2x_{n+1}+x_n,
$$

so

$$
\mathrm{acc}=\lambda_n^{-2}(d_2-d_1).
$$

Therefore

$$
\frac{1}{\lambda_n^2}\langle d_2-d_1,d_2\rangle
=\langle \mathrm{acc},d_2\rangle.
$$

Thus

$$
E_{n+1}-E_n\le \langle \mathrm{acc}+b,d_2\rangle.
$$

Since $\mathrm{acc}+y+b=0$, we have $\mathrm{acc}+b=-y$. Hence

$$
E_{n+1}-E_n\le -\langle y,d_2\rangle.
$$

Using $d_2=\lambda_n v$, which follows from $v=\lambda_n^{-1}d_2$, the inner product rewrites as

$$
\langle y,d_2\rangle=\lambda_n\langle y,v\rangle.
$$

So

$$
E_{n+1}-E_n\le -\lambda_n\langle y,v\rangle.
$$

It remains to bound $\langle y,v\rangle$ from below. Since $y\in A v$, the definition of $A$ gives

```math
\forall z\in H,\qquad
\|z\|^\alpha\ge \|v\|^\alpha+\langle y,z-v\rangle.
```

Taking $z=0$, and using $\alpha\gt 0$ from $\alpha\ge1$, we have $0^\alpha=0$. Therefore

```math
0\ge \|v\|^\alpha-\langle y,v\rangle,
```

so

```math
\langle y,v\rangle\ge \|v\|^\alpha.
```

Multiplying by the negative number $-\lambda_n$ reverses the inequality:

```math
-\lambda_n\langle y,v\rangle
\le
-\lambda_n\|v\|^\alpha.
```

Since $v=\lambda_n^{-1}(x_{n+2}-x_{n+1})$, the right-hand side is exactly $-w_n$. Combining all inequalities gives

$$
E_{n+1}-E_n\le -w_n.
$$

From this energy drop, the proof obtains

$$
w_n\le E_n-E_{n+1}.
$$

Since $f\ge m$, and the kinetic term is nonnegative,

```math
E_N=\frac{1}{2\lambda_N^2}\|x_{N+1}-x_N\|^2+f(x_{N+1})\ge m.
```

Summing the inequality $w_n\le E_n-E_{n+1}$ over $n=0,\dots,N-1$ and using telescoping, the proof gets

$$
\sum_{n=0}^{N-1}w_n
\le
\sum_{n=0}^{N-1}(E_n-E_{n+1})
=E_0-E_N
\le
E_0-m.
$$

Here `Finset.sum_range_sub'` is the telescoping-sum identity.

Next the proof compares $t_n$ with $w_n$. Since $\lambda$ is nondecreasing and $\lambda_0\gt 0$, induction gives $\lambda_0\le \lambda_n$ for every $n$. Because $t_n\ge0$,

$$
\lambda_0 t_n\le \lambda_n t_n=w_n.
$$

Multiplying by $\lambda_0^{-1}\gt 0$ gives

$$
t_n\le \lambda_0^{-1}w_n.
$$

Summing over $n=0,\dots,N-1$,

$$
\sum_{n=0}^{N-1}t_n
\le
\lambda_0^{-1}\sum_{n=0}^{N-1}w_n
\le
\lambda_0^{-1}(E_0-m).
$$

Thus the partial sums of the nonnegative sequence $t_n$ are uniformly bounded.

The proof then invokes `summable_of_sum_range_le`. Its concrete role here is: because every $t_n\ge0$ and all partial sums $\sum_{n=0}^{N-1}t_n$ are bounded above by the fixed number $\lambda_0^{-1}(E_0-m)$, the series $\sum_n t_n$ is summable. Let

$$
C:=\sum_{n=0}^{\infty} t_n.
$$

The theorem `HasSum.tendsto_sum_nat` gives that the partial sums

$$
N\mapsto \sum_{n=0}^{N-1}t_n
$$

tend to $C$ as $N\to\infty$. The proof also notes that $N\mapsto N+1$ tends to infinity. Composing the two limits shows

$$
\sum_{n=0}^{N}t_n \longrightarrow C.
$$

Finally, unfolding the definitions of $t_n$ and $v_n$ turns this into exactly the desired convergence:

```math
\sum_{n=0}^{N}
\left\|
\lambda_n^{-1}\bigl(x_{n+2}-x_{n+1}\bigr)
\right\|^\alpha
\longrightarrow C.
```

This is the conclusion of the theorem.

