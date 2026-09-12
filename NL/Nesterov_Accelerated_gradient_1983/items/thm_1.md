## Source file
`Nesterov_Accelerated_gradient_1983/items/thm_1.lean`

## Lean statement
```lean
theorem accelerated_gradient_rate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (L : ℝ)
    (hC11 : IsC11 f L) (hconv : ConvexOn ℝ Set.univ f)
    (M : AcceleratedGradientMethod f) (xstar : E)
    (hy0 : M.y 0 = M.y0)
    (hmin : ∀ x, f xstar ≤ f x) :
    (∀ k, f (M.x k) - f xstar ≤ (4 * L * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2) ∧
    ∀ ε : ℝ, 0 < ε →
      let NG
```

## Statement explanation
The declaration `accelerated_gradient_rate` states a convergence rate and an iteration/evaluation complexity bound for Nesterov’s accelerated gradient method.

The ambient type $E$ is a real Hilbert space: it is a normed additive commutative group, an inner product space over $\mathbb R$, and complete. The function $f:E\to\mathbb R$ is the objective. The real number $L$ is the parameter of the hypothesis `hC11 : IsC11 f L`, a $C^{1,1}$-type regularity assumption for $f$. In the proof this hypothesis is used through the visible consequences that $f$ has gradient `gradient f u` at every point $u$, and that the method’s data imply $0<L$ with $1/L\le M.initialStep$. The hypothesis `hconv : ConvexOn ℝ Set.univ f` says that $f$ is convex on all of $E$. The term $M$ is an accelerated gradient method for $f$; the proof uses its sequences $M.x_k$, $M.y_k$, its initial auxiliary point $M.y_0$, its previous point $M.x_{-1}$, its step sizes $M.step_k$, its weights $M.weight_k$, its initial step $M.initialStep$, and its line-search trial counts $M.searchIndex_k$. The point $x^*$ is a global minimizer of $f$, because `hmin : ∀ x, f xstar ≤ f x`. The hypothesis `hy0 : M.y 0 = M.y0` identifies the first auxiliary iterate of the method with the initial point $M.y_0$ used in the estimates.

The first conclusion is the accelerated rate:

$$
\forall k\in\mathbb N,\qquad
f(M.x_k)-f(x^*)
\le
\frac{4L\,\lVert M.y_0-x^*\rVert^2}{(k+2)^2}.
$$

Thus the objective gap at the $k$-th iterate is bounded by a constant multiple of $(k+2)^{-2}$.

The second conclusion is a complexity statement. For every $\varepsilon>0$, define

$$
NG=\sqrt{\frac{4L\,\lVert M.y_0-x^*\rVert^2}{\varepsilon}},
\qquad
NF=2NG+\log_2(2L\,M.initialStep)+1.
$$

Then there exist natural numbers `iterations`, `gradientEvaluations`, and `functionEvaluations` such that

$$
\text{gradientEvaluations}
=\text{acceleratedGradientEvaluationCount}(f,M,\text{iterations}),
$$

$$
\text{functionEvaluations}
=\text{acceleratedFunctionEvaluationCount}(f,M,\text{iterations}),
$$

and

$$
\text{gradientEvaluations}\le \lceil NG\rceil_{\mathbb N},
\qquad
\text{functionEvaluations}\le \lceil NF\rceil_{\mathbb N},
\qquad
f(M.x_{\text{iterations}})-f(x^*)\le \varepsilon .
$$

Here $\lceil r\rceil_{\mathbb N}$ denotes `(Int.ceil r).toNat`, the natural-number ceiling, valid because the proof establishes that the arguments are nonnegative. The cited definitions give

$$
\text{acceleratedGradientEvaluationCount}(f,M,n)=n,
$$

so the gradient-evaluation count is just the number of iterations, and

$$
\text{acceleratedFunctionEvaluationCount}(f,M,n)
=2n+\sum_{i<n} M.searchIndex_i.
$$

Thus the function-evaluation count is $2n$ plus the total number of rejected line-search trials.

## Lean proof
```lean
Real.sqrt (4 * L * ‖M.y0 - xstar‖ ^ 2 / ε)
      let NF := 2 * NG + Real.logb 2 (2 * L * M.initialStep) + 1
      ∃ iterations gradientEvaluations functionEvaluations : ℕ,
        gradientEvaluations = acceleratedGradientEvaluationCount f M iterations ∧
        functionEvaluations = acceleratedFunctionEvaluationCount f M iterations ∧
        gradientEvaluations ≤ (Int.ceil NG).toNat ∧
        functionEvaluations ≤ (Int.ceil NF).toNat ∧
        f (M.x iterations) - f xstar ≤ ε := by
  let p : ℕ → E := fun n => (M.weight n - 1) •
    ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n)
  have hp : ∀ n, p n = (M.weight n - 1) •
      ((if n = 0 then M.x_neg_one else M.x (n - 1)) - M.x n) := fun _ => rfl
  have hL : 0 < L := (initialStep_ge_inv_L f L hC11 M).1
  have henergy : ∀ k, 2 * M.step k * M.weight k ^ 2 *
      (f (M.x k) - f xstar) + ‖p k - M.x k + xstar‖ ^ 2 ≤
        ‖M.y0 - xstar‖ ^ 2 := by
    intro k
    induction k with
    | zero =>
        exact accelerated_energy_zero_le f M xstar hy0 hconv
          (fun u => hC11.hasGradientAt u) p hp
    | succ k ih => exact (accelerated_energy_succ_le f L hC11 hconv M xstar hmin p hp k).trans ih
  have hrate : ∀ k, f (M.x k) - f xstar ≤
      (4 * L * ‖M.y0 - xstar‖ ^ 2) / (k + 2 : ℝ) ^ 2 := by
    intro k
    have hgap : 0 ≤ f (M.x k) - f xstar := by linarith [hmin (M.x k)]
    have hstep : 1 / (2 * L) ≤ M.step k := method_step_lower f L hC11 M k
    have hweight : 1 + (k : ℝ) / 2 ≤ M.weight k := weight_lower f M k
    have hlower : 0 ≤ 1 + (k : ℝ) / 2 := by positivity
    have hweightSq : (1 + (k : ℝ) / 2) ^ 2 ≤ M.weight k ^ 2 := by nlinarith
    have henergy' : 2 * M.step k * M.weight k ^ 2 *
        (f (M.x k) - f xstar) ≤ ‖M.y0 - xstar‖ ^ 2 := by
      nlinarith [henergy k, sq_nonneg ‖p k - M.x k + xstar‖]
    have hscaledStep := mul_le_mul_of_nonneg_right hstep
      (mul_nonneg (sq_nonneg (M.weight k)) hgap)
    have hscaledWeight := mul_le_mul_of_nonneg_right hweightSq
      (mul_nonneg (le_of_lt (by positivity : 0 < 1 / (2 * L))) hgap)
    have hscaledWeight' : (1 + (k : ℝ) / 2) ^ 2 *
        (1 / (2 * L) * (f (M.x k) - f xstar)) ≤ M.weight k ^ 2 *
        (1 / (2 * L) * (f (M.x k) - f xstar)) := by
      convert hscaledWeight using 1 <;> field_simp <;> ring
    have hcoef : ((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar) ≤
        ‖M.y0 - xstar‖ ^ 2 := by
      have hbase : (1 + (k : ℝ) / 2) ^ 2 *
          (1 / (2 * L) * (f (M.x k) - f xstar)) ≤
          1 / (2 * L) * (M.weight k ^ 2 * (f (M.x k) - f xstar)) := by
        convert hscaledWeight' using 1 <;> ring
      have heq : ((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar) =
          2 * ((1 + (k : ℝ) / 2) ^ 2 *
            (1 / (2 * L) * (f (M.x k) - f xstar))) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring
      calc
        ((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar) =
            2 * ((1 + (k : ℝ) / 2) ^ 2 *
              (1 / (2 * L) * (f (M.x k) - f xstar))) := heq
        _ ≤ 2 * (1 / (2 * L) * (M.weight k ^ 2 * (f (M.x k) - f xstar))) := by
          gcongr
        _ ≤ 2 * (M.step k * (M.weight k ^ 2 * (f (M.x k) - f xstar))) := by
          gcongr
        _ ≤ ‖M.y0 - xstar‖ ^ 2 := by nlinarith [henergy']
    have hden : 0 < (k + 2 : ℝ) ^ 2 := by positivity
    apply (le_div_iff₀ hden).2
    calc
      (f (M.x k) - f xstar) * (k + 2 : ℝ) ^ 2 =
          (4 * L) * (((k + 2 : ℝ) ^ 2 / (4 * L)) * (f (M.x k) - f xstar)) := by
            field_simp
      _ ≤ (4 * L) * ‖M.y0 - xstar‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = 4 * L * ‖M.y0 - xstar‖ ^ 2 := by ring
  constructor
  · exact hrate
  · intro ε hε
    dsimp
    let NG := Real.sqrt (4 * L * ‖M.y0 - xstar‖ ^ 2 / ε)
    let D := Real.logb 2 (2 * L * M.initialStep)
    have hC0 : 0 ≤ 4 * L * ‖M.y0 - xstar‖ ^ 2 := by positivity
    have hNG0 : 0 ≤ NG := Real.sqrt_nonneg _
    have hN0 : 0 ≤ Int.ceil NG := Int.ceil_nonneg hNG0
    let iterations := (Int.ceil NG).toNat
    have hNGle : NG ≤ (iterations : ℝ) := by
      rw [show (iterations : ℝ) = (Int.ceil NG : ℤ) by
        exact_mod_cast (Int.toNat_of_nonneg hN0)]
      exact Int.le_ceil NG
    have hsqNG : NG ^ 2 = 4 * L * ‖M.y0 - xstar‖ ^ 2 / ε := by
      dsimp [NG]
      exact Real.sq_sqrt (div_nonneg hC0 (le_of_lt hε))
    have haccuracy : f (M.x iterations) - f xstar ≤ ε := by
      have hden : 0 < (iterations + 2 : ℝ) ^ 2 := by positivity
      calc
        f (M.x iterations) - f xstar ≤
            (4 * L * ‖M.y0 - xstar‖ ^ 2) / (iterations + 2 : ℝ) ^ 2 :=
          hrate iterations
        _ ≤ ε := by
          apply (div_le_iff₀ hden).2
          have hsquares : NG ^ 2 ≤ (iterations : ℝ) ^ 2 :=
            (sq_le_sq₀ hNG0 (by positivity)).2 hNGle
          rw [hsqNG] at hsquares
          have hCiterations : 4 * L * ‖M.y0 - xstar‖ ^ 2 ≤
              ε * (iterations : ℝ) ^ 2 := by
            nlinarith [(div_le_iff₀ hε).mp hsquares]
          have hinc : (iterations : ℝ) ^ 2 ≤ (iterations + 2 : ℝ) ^ 2 := by
            nlinarith [show (0 : ℝ) ≤ iterations by positivity]
          exact hCiterations.trans (mul_le_mul_of_nonneg_left hinc (le_of_lt hε))
    have hD0 : 0 ≤ D := by
      have hsum := search_sum_le_logb f L hC11 M 0
      have hnonneg : (0 : ℝ) ≤
          (((Finset.range (0 + 1)).sum M.searchIndex : ℕ) : ℝ) := by positivity
      linarith [show (((Finset.range (0 + 1)).sum M.searchIndex : ℕ) : ℝ) ≤ D by
        simpa [D] using hsum]
    have hsubset : Finset.range iterations ⊆ Finset.range (iterations + 1) :=
      Finset.range_subset_range.2 (Nat.le_succ _)
    have hsumle : (Finset.range iterations).sum M.searchIndex ≤
        (Finset.range (iterations + 1)).sum M.searchIndex :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    have hsumR : (((Finset.range iterations).sum M.searchIndex : ℕ) : ℝ) ≤ D := by
      have hcast : (((Finset.range iterations).sum M.searchIndex : ℕ) : ℝ) ≤
          (((Finset.range (iterations + 1)).sum M.searchIndex : ℕ) : ℝ) := by
        exact_mod_cast hsumle
      exact hcast.trans (by simpa [D] using search_sum_le_logb f L hC11 M iterations)
    have hsumD : (Finset.range iterations).sum M.searchIndex ≤ (Int.ceil D).toNat := by
      have hceil : (((Finset.range iterations).sum M.searchIndex : ℕ) : ℤ) ≤ Int.ceil D := by
        exact_mod_cast hsumR.trans (Int.le_ceil D)
      exact (Int.le_toNat (Int.ceil_nonneg hD0)).2 hceil
    refine ⟨iterations, acceleratedGradientEvaluationCount f M iterations,
      acceleratedFunctionEvaluationCount f M iterations, rfl, rfl, ?_, ?_, haccuracy⟩
    · rfl
    · change 2 * iterations + (Finset.range iterations).sum M.searchIndex ≤
        (Int.ceil (2 * NG + D + 1)).toNat
      have harg : 0 ≤ 2 * NG + D + 1 := by positivity
      have hY : 0 ≤ Int.ceil (2 * NG + D + 1) := Int.ceil_nonneg harg
      refine (Int.le_toNat hY).2 ?_
      have hiter : (iterations : ℤ) = Int.ceil NG := Int.toNat_of_nonneg hN0
      have hiterR : (iterations : ℝ) = ((Int.ceil NG : ℤ) : ℝ) := by
        exact_mod_cast hiter
      have hltR :
          (((2 * iterations + (Finset.range iterations).sum M.searchIndex : ℕ) : ℤ) : ℝ) <
            ((Int.ceil (2 * NG + D + 1) : ℤ) : ℝ) + 1 := by
        have hceilR : ((Int.ceil NG : ℤ) : ℝ) < NG + 1 := Int.ceil_lt_add_one NG
        have hYle : 2 * NG + D + 1 ≤ ((Int.ceil (2 * NG + D + 1) : ℤ) : ℝ) := Int.le_ceil _
        have hsumR' : (∑ x ∈ Finset.range iterations, (M.searchIndex x : ℝ)) ≤ D := by
          simpa only [Nat.cast_sum] using hsumR
        push_cast
        linarith
      exact Int.lt_add_one_iff.1 (by exact_mod_cast hltR)
```

## Proof explanation
The proof first defines the auxiliary sequence

$$
p_n
=(M.weight_n-1)\cdot
\left(
\left(\text{if }n=0\text{ then }M.x_{-1}\text{ else }M.x_{n-1}\right)-M.x_n
\right).
$$

This is the momentum-like extrapolated point used in the energy estimates. The fact `hp` is proved by `rfl`, because it is exactly the definition just introduced.

Next, the proof obtains $0<L$ from `initialStep_ge_inv_L`. That theorem states

$$
0<L
\qquad\text{and}\qquad
\frac1L\le M.initialStep.
$$

The proof only extracts the first conjunct, $0<L$, and uses it later for positivity and division arguments.

The central estimate is the energy bound

$$
2 M.step_k M.weight_k^2\bigl(f(M.x_k)-f(x^*)\bigr)
+\lVert p_k-M.x_k+x^*\rVert^2
\le
\lVert M.y_0-x^*\rVert^2 .
$$

The proof proves this for all $k$ by induction. The base case $k=0$ is exactly the conclusion of `accelerated_energy_zero_le`, which, using `hy0`, convexity of $f$, the gradient hypothesis, and the definition of $p$, gives

$$
2 M.step_0 M.weight_0^2\bigl(f(M.x_0)-f(x^*)\bigr)
+\lVert p_0-M.x_0+x^*\rVert^2
\le
\lVert M.y_0-x^*\rVert^2 .
$$

The gradient hypothesis supplied to that lemma is `fun u => hC11.hasGradientAt u`: for every point $u$, the gradient of $f$ at $u$ is `gradient f u`.

For the induction step, `accelerated_energy_succ_le` states

$$
2 M.step_{k+1} M.weight_{k+1}^2
\bigl(f(M.x_{k+1})-f(x^*)\bigr)
+\lVert p_{k+1}-M.x_{k+1}+x^*\rVert^2
\le
2 M.step_k M.weight_k^2
\bigl(f(M.x_k)-f(x^*)\bigr)
+\lVert p_k-M.x_k+x^*\rVert^2 .
$$

So the energy at step $k+1$ is at most the energy at step $k$. Composing this with the induction hypothesis gives the desired global bound. This is the mathematical content of the `.trans ih` step.

From this energy bound, the proof derives the rate

$$
f(M.x_k)-f(x^*)
\le
\frac{4L\,\lVert M.y_0-x^*\rVert^2}{(k+2)^2}.
$$

For fixed $k$, the gap is nonnegative because $x^*$ is a global minimizer:

$$
0\le f(M.x_k)-f(x^*),
$$

proved by `linarith [hmin (M.x k)]`.

Two lower bounds are then invoked. The theorem `method_step_lower` gives

$$
\frac{1}{2L}\le M.step_k,
$$

and the theorem `weight_lower` gives

$$
1+\frac{k}{2}\le M.weight_k.
$$

Since $1+k/2\ge0$, squaring the weight inequality yields

$$
\left(1+\frac{k}{2}\right)^2\le M.weight_k^2.
$$

The energy bound also implies, after dropping the nonnegative squared-norm term,

$$
2 M.step_k M.weight_k^2\bigl(f(M.x_k)-f(x^*)\bigr)
\le
\lVert M.y_0-x^*\rVert^2 .
$$

The proof multiplies the lower bounds for $M.step_k$ and $M.weight_k^2$ by the nonnegative gap $f(M.x_k)-f(x^*)$. Together with

$$
\left(1+\frac{k}{2}\right)^2=\frac{(k+2)^2}{4},
$$

this gives

$$
\frac{(k+2)^2}{4L}\bigl(f(M.x_k)-f(x^*)\bigr)
\le
\lVert M.y_0-x^*\rVert^2 .
$$

The tactics `positivity`, `nlinarith`, `gcongr`, `field_simp`, and `ring` are used here for nonnegativity, algebraic rearrangement, and monotonicity of multiplication by nonnegative factors. Multiplying by $4L$, using $L>0$, and dividing by the positive denominator $(k+2)^2$ yields the stated rate.

The proof then proves the complexity part. Given $\varepsilon>0$, it defines

$$
NG=\sqrt{\frac{4L\lVert M.y_0-x^*\rVert^2}{\varepsilon}}
$$

and

$$
D=\log_2(2L\,M.initialStep),
$$

so that the theorem’s $NF$ is $2NG+D+1$. It checks that

$$
0\le 4L\lVert M.y_0-x^*\rVert^2,
\qquad
0\le NG,
\qquad
0\le \lceil NG\rceil,
$$

and defines

$$
\text{iterations}=(\lceil NG\rceil)_{\mathbb N}.
$$

The inequality $NG\le \text{iterations}$ follows from $NG\le \lceil NG\rceil$ and the fact that `iterations` is the natural-number version of that ceiling. Also,

$$
NG^2=\frac{4L\lVert M.y_0-x^*\rVert^2}{\varepsilon},
$$

using `Real.sq_sqrt` and the nonnegativity of the radicand.

The accuracy estimate $f(M.x_{\text{iterations}})-f(x^*)\le\varepsilon$ follows from the rate. Since $NG\le \text{iterations}$, squaring gives

$$
NG^2\le \text{iterations}^2.
$$

Substituting the formula for $NG^2$ yields

$$
\frac{4L\lVert M.y_0-x^*\rVert^2}{\varepsilon}
\le
\text{iterations}^2.
$$

Multiplying by $\varepsilon>0$ gives

$$
4L\lVert M.y_0-x^*\rVert^2
\le
\varepsilon\,\text{iterations}^2.
$$

Since $\text{iterations}^2\le(\text{iterations}+2)^2$, the rate at $k=\text{iterations}$ is at most $\varepsilon$.

Next the proof bounds the line-search sum. Let

$$
S=\sum_{i<\text{iterations}} M.searchIndex_i.
$$

First, `D` is nonnegative. Indeed, applying `search_sum_le_logb` with $n=0$ gives

$$
\sum_{i=0}^{0} M.searchIndex_i
\le
\log_2(2L\,M.initialStep)=D,
$$

and the left-hand side is a natural number cast to $\mathbb R$, hence nonnegative.

For the chosen number of iterations, the proof uses that the range of indices below `iterations` is contained in the range of indices below `iterations+1`, and that all terms $M.searchIndex_i$ are natural numbers, hence nonnegative. Therefore

$$
\sum_{i<\text{iterations}} M.searchIndex_i
\le
\sum_{i<\text{iterations}+1} M.searchIndex_i.
$$

Applying `search_sum_le_logb` with $n=\text{iterations}$ bounds the right-hand sum by $D$:

$$
\sum_{i<\text{iterations}+1} M.searchIndex_i
\le D.
$$

Thus $S\le D$, and since $D\ge0$, also

$$
S\le \lceil D\rceil_{\mathbb N}.
$$

The proof now chooses witnesses

$$
\text{iterations}=(\lceil NG\rceil)_{\mathbb N},
$$

$$
\text{gradientEvaluations}
=\text{acceleratedGradientEvaluationCount}(f,M,\text{iterations}),
$$

$$
\text{functionEvaluations}
=\text{acceleratedFunctionEvaluationCount}(f,M,\text{iterations}).
$$

The two defining equalities are closed by `rfl`. The gradient-evaluation bound is also immediate, because

$$
\text{acceleratedGradientEvaluationCount}(f,M,\text{iterations})
=\text{iterations}
=(\lceil NG\rceil)_{\mathbb N},
$$

so the inequality against `(Int.ceil NG).toNat` is reflexive.

For the function-evaluation bound, the goal becomes

$$
2\,\text{iterations}+S
\le
\left\lceil 2NG+D+1\right\rceil_{\mathbb N}.
$$

The proof first shows the corresponding integer inequality. It uses

$$
\text{iterations}=\lceil NG\rceil<\ NG+1,
$$

from `Int.ceil_lt_add_one`, and $S\le D$, together with

$$
2NG+D+1\le \lceil 2NG+D+1\rceil.
$$

Combining these gives the real inequality

$$
2\,\text{iterations}+S
<
\lceil 2NG+D+1\rceil+1.
$$

Since the left-hand side is an integer and the right-hand side is an integer plus one, `Int.lt_add_one_iff` converts this into the integer inequality

$$
2\,\text{iterations}+S
\le
\lceil 2NG+D+1\rceil.
$$

Finally, because the right-hand integer is nonnegative, `Int.le_toNat` converts this into the desired natural-number inequality

$$
2\,\text{iterations}+S
\le
\left\lceil 2NG+D+1\right\rceil_{\mathbb N}.
$$

Together with the already established $\varepsilon$-accuracy, this supplies all clauses of the existential complexity statement.

