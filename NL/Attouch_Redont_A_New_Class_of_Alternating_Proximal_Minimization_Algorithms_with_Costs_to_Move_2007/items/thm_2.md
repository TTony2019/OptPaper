## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/thm_2.lean`

## Lean statement
```lean
theorem theorem_2_5 {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β μ ν)
    (hyp : H21toH24 X Y f g h k c α β μ ν)
    (β_behavior μ_behavior : MonotonicityBehavior)
    (hβ_prop : β_behavior.toProp (β := β))
    (hμ_prop : μ_behavior.toProp (β := μ)) :
    ∃ inf_f inf_g L : ℝ,
      (∀ x, f x ≥ inf_f) ∧
      (∀ y, g y ≥ inf_g) ∧
      Antitone (weightedEnergy f g c (fun n => β n) (fun n => μ n)
        (deltaSeq β μ β_behavior μ_behavior) inf_f inf_g alg.x alg.y) ∧
      Tendsto (weightedEnergy f g c β μ (deltaSeq β μ β_behavior μ_behavior)
        inf_f inf_g alg.x alg.y) atTop (𝓝 L) ∧
      Summable (weightedCost h k α β μ ν (deltaSeq β μ β_behavior μ_behavior)
        alg.x alg.y)
```

## Statement explanation
The declaration states a convergence and finite-cost theorem for a two-block alternating proximal minimization algorithm. Let $X$ and $Y$ be types, and let

$$
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,\qquad
h:X\to X\to\mathbb R,\qquad k:Y\to Y\to\mathbb R,\qquad c:X\to Y\to\mathbb R
$$

be real-valued functions. Also let $\alpha,\beta,\mu,\nu:\mathbb N\to\mathbb R$ be real sequences.

The hypothesis `alg : CA2 X Y f g h k c α β μ ν` supplies the algorithm object; in particular it supplies the two sequences

$$
x_n = alg.x(n)\in X,\qquad y_n = alg.y(n)\in Y.
$$

The hypothesis `hyp : H21toH24 X Y f g h k c α β μ ν` is a bundle of assumptions. The proof uses the following parts of it:
- $f$ is bounded below: there is $inf_f\in\mathbb R$ with $f(x)\ge inf_f$ for every $x\in X$.
- $g$ is bounded below: there is $inf_g\in\mathbb R$ with $g(y)\ge inf_g$ for every $y\in Y$.
- $\beta_n>0$ and $\mu_n>0$ for every $n$.
- $\alpha_n\ge0$ and $\nu_n\ge0$ for every $n$.
- $c(x,y)\ge0$ for all $x,y$.
- $h(x,x')\ge0$ for all $x,x'$.
- $k(y,y')\ge0$ for all $y,y'$.

The parameters `β_behavior` and `μ_behavior` are monotonicity choices for $\beta$ and $\mu$. The hypotheses `hβ_prop` and `hμ_prop` assert that $\beta$ and $\mu$ have those chosen behaviors. The sequence $\delta_n = \operatorname{deltaSeq}(\beta,\mu,\beta_{\rm behavior},\mu_{\rm behavior})$ is defined by four cases:

$$
\delta_n=
\begin{cases}
1, & \beta \text{ nonincreasing and } \mu \text{ nonincreasing},\\
\mu_n, & \beta \text{ nonincreasing and } \mu \text{ nondecreasing},\\
\beta_n, & \beta \text{ nondecreasing and } \mu \text{ nonincreasing},\\
\beta_n\mu_n, & \beta \text{ nondecreasing and } \mu \text{ nondecreasing}.
\end{cases}
$$

The theorem uses the weighted energy

$$
E_n=
\frac{\mu_n}{\delta_n}\bigl(f(x_n)-inf_f\bigr)
+\frac{\beta_n}{\delta_n}\bigl(g(y_n)-inf_g\bigr)
+\frac{\beta_n\mu_n}{\delta_n}c(x_n,y_n),
$$

and the weighted move cost

$$
W_n=
\frac{\mu_n}{\delta_n}\alpha_n h(x_n,x_{n+1})
+\frac{\beta_n}{\delta_n}\nu_n k(y_n,y_{n+1}).
$$

In the Lean statement, the antitone conjunct writes `(fun n => β n)` and `(fun n => μ n)` in place of $\beta$ and $\mu$; these are the same functions.

The conclusion is that there exist real numbers $inf_f$, $inf_g$, and $L$ such that:
1. $f(x)\ge inf_f$ for every $x\in X$.
2. $g(y)\ge inf_g$ for every $y\in Y$.
3. The sequence $n\mapsto E_n$ is antitone, i.e. nonincreasing.
4. $E_n\to L$ as $n\to\infty$.
5. The sequence $n\mapsto W_n$ is summable, so the total weighted move cost $\sum_{n=0}^\infty W_n$ is finite.

## Lean proof
```lean
by
  rcases hyp.f_bdd_below with ⟨inf_f, hf⟩
  rcases hyp.g_bdd_below with ⟨inf_g, hg⟩
  let delta := deltaSeq β μ β_behavior μ_behavior
  have hdelta_pos : ∀ n, 0 < delta n := by
    intro n
    dsimp [delta]
    unfold deltaSeq
    match β_behavior, μ_behavior with
    | .nonincreasing, .nonincreasing => norm_num
    | .nonincreasing, .nondecreasing => exact hyp.mu_pos n
    | .nondecreasing, .nonincreasing => exact hyp.beta_pos n
    | .nondecreasing, .nondecreasing => exact mul_pos (hyp.beta_pos n) (hyp.mu_pos n)
  have hμd : ∀ n, μ (n+1) / delta (n+1) ≤ μ n / delta n := by
    simpa [delta] using
      mu_div_delta_nonincreasing β μ β_behavior μ_behavior hyp.beta_pos hyp.mu_pos
        hβ_prop hμ_prop
  have hβd : ∀ n, β (n+1) / delta (n+1) ≤ β n / delta n := by
    simpa [delta] using
      beta_div_delta_nonincreasing β μ β_behavior μ_behavior hyp.beta_pos hyp.mu_pos
        hβ_prop hμ_prop
  have hβμd : ∀ n, (β (n+1) * μ (n+1)) / delta (n+1) ≤
      (β n * μ n) / delta n := by
    simpa [delta] using
      betamu_div_delta_nonincreasing β μ β_behavior μ_behavior hyp.beta_pos hyp.mu_pos
        hβ_prop hμ_prop
  let E := weightedEnergy f g c β μ delta inf_f inf_g alg.x alg.y
  let W := weightedCost h k α β μ ν delta alg.x alg.y
  have hE_nonneg : ∀ n, 0 ≤ E n := by
    intro n
    have hf_n : 0 ≤ f (alg.x n) - inf_f := sub_nonneg.mpr (hf _)
    have hg_n : 0 ≤ g (alg.y n) - inf_g := sub_nonneg.mpr (hg _)
    have hc_n : 0 ≤ c (alg.x n) (alg.y n) := hyp.c_nonneg _ _
    have hμd_n : 0 ≤ μ n / delta n := div_nonneg (le_of_lt (hyp.mu_pos n))
      (le_of_lt (hdelta_pos n))
    have hβd_n : 0 ≤ β n / delta n := div_nonneg (le_of_lt (hyp.beta_pos n))
      (le_of_lt (hdelta_pos n))
    have hβμd_n : 0 ≤ (β n * μ n) / delta n := div_nonneg
      (mul_nonneg (le_of_lt (hyp.beta_pos n)) (le_of_lt (hyp.mu_pos n)))
      (le_of_lt (hdelta_pos n))
    dsimp [E, weightedEnergy]
    exact add_nonneg (add_nonneg (mul_nonneg hμd_n hf_n) (mul_nonneg hβd_n hg_n))
      (mul_nonneg hβμd_n hc_n)
  have hW_nonneg : ∀ n, 0 ≤ W n := by
    intro n
    have hμd_n : 0 ≤ μ n / delta n := div_nonneg (le_of_lt (hyp.mu_pos n))
      (le_of_lt (hdelta_pos n))
    have hβd_n : 0 ≤ β n / delta n := div_nonneg (le_of_lt (hyp.beta_pos n))
      (le_of_lt (hdelta_pos n))
    have ha_n : 0 ≤ α n := hyp.alpha_nonneg n
    have hv_n : 0 ≤ ν n := hyp.nu_nonneg n
    have hh_n : 0 ≤ h (alg.x n) (alg.x (n+1)) := hyp.h_nonneg _ _
    have hk_n : 0 ≤ k (alg.y n) (alg.y (n+1)) := hyp.k_nonneg _ _
    dsimp [W, weightedCost]
    exact add_nonneg (mul_nonneg (mul_nonneg hμd_n ha_n) hh_n)
      (mul_nonneg (mul_nonneg hβd_n hv_n) hk_n)
  have hE_step : ∀ n, E (n+1) + W n ≤ E n := by
    intro n
    have hraw := lemma_2_3 alg hyp n
    have hscaled := div_le_div_of_nonneg_right hraw (le_of_lt (hdelta_pos n))
    have hscaled' :
        (μ n / delta n) * f (alg.x (n+1)) +
          (β n / delta n) * g (alg.y (n+1)) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) +
          (μ n / delta n) * α n * h (alg.x n) (alg.x (n+1)) +
          (β n / delta n) * ν n * k (alg.y n) (alg.y (n+1)) ≤
        (μ n / delta n) * f (alg.x n) +
          (β n / delta n) * g (alg.y n) +
          ((β n * μ n) / delta n) * c (alg.x n) (alg.y n) := by
      calc
        _ = (μ n * f (alg.x (n+1)) + β n * g (alg.y (n+1)) +
            β n * μ n * c (alg.x (n+1)) (alg.y (n+1)) +
            μ n * α n * h (alg.x n) (alg.x (n+1)) +
            β n * ν n * k (alg.y n) (alg.y (n+1))) / delta n := by
              field_simp [ne_of_gt (hdelta_pos n)]
        _ ≤ (μ n * f (alg.x n) + β n * g (alg.y n) +
            β n * μ n * c (alg.x n) (alg.y n)) / delta n := hscaled
        _ = _ := by
              field_simp [ne_of_gt (hdelta_pos n)]
    have hshift :
        (μ n / delta n) * (f (alg.x (n+1)) - inf_f) +
          (β n / delta n) * (g (alg.y (n+1)) - inf_g) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) + W n ≤
        E n := by
      dsimp [E, W, weightedEnergy, weightedCost]
      calc
        _ = ((μ n / delta n) * f (alg.x (n+1)) +
            (β n / delta n) * g (alg.y (n+1)) +
            ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) +
            (μ n / delta n) * α n * h (alg.x n) (alg.x (n+1)) +
            (β n / delta n) * ν n * k (alg.y n) (alg.y (n+1))) -
            ((μ n / delta n) * inf_f + (β n / delta n) * inf_g) := by ring
        _ ≤ ((μ n / delta n) * f (alg.x n) +
            (β n / delta n) * g (alg.y n) +
            ((β n * μ n) / delta n) * c (alg.x n) (alg.y n)) -
            ((μ n / delta n) * inf_f + (β n / delta n) * inf_g) := by
              exact sub_le_sub_right hscaled' _
        _ = E n := by
              simp [E, weightedEnergy] <;> ring
    have hcoef : E (n+1) ≤
        (μ n / delta n) * (f (alg.x (n+1)) - inf_f) +
          (β n / delta n) * (g (alg.y (n+1)) - inf_g) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) := by
      have hf_n1 : 0 ≤ f (alg.x (n+1)) - inf_f := sub_nonneg.mpr (hf _)
      have hg_n1 : 0 ≤ g (alg.y (n+1)) - inf_g := sub_nonneg.mpr (hg _)
      have hc_n1 : 0 ≤ c (alg.x (n+1)) (alg.y (n+1)) := hyp.c_nonneg _ _
      have h1 := mul_le_mul_of_nonneg_right (hμd n) hf_n1
      have h2 := mul_le_mul_of_nonneg_right (hβd n) hg_n1
      have h3 := mul_le_mul_of_nonneg_right (hβμd n) hc_n1
      dsimp [E, weightedEnergy]
      nlinarith
    have hcoefW := add_le_add_left hcoef (W n)
    have hcoefW' : E (n+1) + W n ≤
        (μ n / delta n) * (f (alg.x (n+1)) - inf_f) +
          (β n / delta n) * (g (alg.y (n+1)) - inf_g) +
          ((β n * μ n) / delta n) * c (alg.x (n+1)) (alg.y (n+1)) + W n := by
      nlinarith
    exact le_trans hcoefW' hshift
  have hE_succ : ∀ n, E (n+1) ≤ E n := by
    intro n
    exact le_trans (le_add_of_nonneg_right (hW_nonneg n)) (hE_step n)
  have hE_antitone : Antitone E := antitone_nat_of_succ_le hE_succ
  have hE_bdd : BddBelow (Set.range E) := by
    refine ⟨0, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hE_nonneg n
  let L : ℝ := ⨅ n, E n
  have hE_tendsto : Tendsto E atTop (𝓝 L) := by
    dsimp [L]
    exact tendsto_atTop_ciInf hE_antitone hE_bdd
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, W n
  have hS_mono : Monotone S := by
    refine monotone_nat_of_le_succ ?_
    intro N
    dsimp [S]
    rw [Finset.sum_range_succ]
    linarith [hW_nonneg N]
  have hS_tel : ∀ N, S N ≤ E 0 - E N := by
    intro N
    induction N with
    | zero => simp [S]
    | succ N ih =>
        rw [show S (N+1) = S N + W N by simp [S, Finset.sum_range_succ]]
        have htel := hE_step N
        have hdrop : W N ≤ E N - E (N+1) := by linarith
        calc
          S N + W N ≤ (E 0 - E N) + (E N - E (N+1)) := add_le_add ih hdrop
          _ = E 0 - E (N+1) := by ring
  have hS_bound : ∀ N, S N ≤ E 0 := by
    intro N
    have htel := hS_tel N
    linarith [hE_nonneg N]
  have hS_bdd : BddAbove (Set.range S) := by
    refine ⟨E 0, ?_⟩
    rintro z ⟨N, rfl⟩
    exact hS_bound N
  have hS_tendsto : Tendsto S atTop (𝓝 (⨆ N, S N)) :=
    tendsto_atTop_ciSup hS_mono hS_bdd
  have hW_sum : Summable W := by
    refine ⟨⨆ N, S N, ?_⟩
    exact (hasSum_iff_tendsto_nat_of_nonneg (fun n => hW_nonneg n) _).2 hS_tendsto
  exact ⟨inf_f, inf_g, L, hf, hg, hE_antitone, hE_tendsto, hW_sum⟩
```

## Proof explanation
The proof begins by extracting lower bounds from the hypothesis bundle. The tactic
`rcases hyp.f_bdd_below with ⟨inf_f, hf⟩`
produces a real number $inf_f$ and the inequality $hf:\forall x,\ f(x)\ge inf_f$. Similarly,
`rcases hyp.g_bdd_below with ⟨inf_g, hg⟩`
produces $inf_g$ and $hg:\forall y,\ g(y)\ge inf_g$. These are exactly the first two conclusions of the theorem.

Next the proof defines

$$
\delta_n=\operatorname{deltaSeq}(\beta,\mu,\beta_{\rm behavior},\mu_{\rm behavior}).
$$

It proves `hdelta_pos : ∀ n, 0 < δ_n`. The proof is by cases on the two selected monotonicity behaviors. If both are nonincreasing, then $\delta_n=1$, so positivity is immediate. If $\beta$ is nonincreasing and $\mu$ is nondecreasing, then $\delta_n=\mu_n$, and `hyp.mu_pos n` gives $\mu_n>0$. If $\beta$ is nondecreasing and $\mu$ is nonincreasing, then $\delta_n=\beta_n$, and `hyp.beta_pos n` gives $\beta_n>0$. If both are nondecreasing, then $\delta_n=\beta_n\mu_n$, and positivity follows from $\beta_n>0$ and $\mu_n>0$ by `mul_pos`.

The proof then specializes the three monotonicity lemmas supplied in the context. The lemma `mu_div_delta_nonincreasing` says that, under the positivity and monotonicity assumptions on $\beta$ and $\mu$,

$$
\frac{\mu_{n+1}}{\delta_{n+1}}\le \frac{\mu_n}{\delta_n}.
$$

This becomes `hμd`. The lemma `beta_div_delta_nonincreasing` gives

$$
\frac{\beta_{n+1}}{\delta_{n+1}}\le \frac{\beta_n}{\delta_n},
$$

stored as `hβd`. The lemma `betamu_div_delta_nonincreasing` gives

$$
\frac{\beta_{n+1}\mu_{n+1}}{\delta_{n+1}}
\le
\frac{\beta_n\mu_n}{\delta_n},
$$

stored as `hβμd`. These three inequalities are the coefficient monotonicities that later let the proof compare the energy at $n+1$ with the coefficients at $n$.

The proof defines the local abbreviations $E_n$ for the weighted energy and $W_n$ for the weighted cost. It first shows `hE_nonneg : ∀ n, 0 ≤ E_n`. For a fixed $n$, one has

$$
f(x_n)-inf_f\ge0,\qquad g(y_n)-inf_g\ge0,\qquad c(x_n,y_n)\ge0.
$$

Also, because $\beta_n>0$, $\mu_n>0$, and $\delta_n>0$,

$$
\frac{\mu_n}{\delta_n}\ge0,\qquad
\frac{\beta_n}{\delta_n}\ge0,\qquad
\frac{\beta_n\mu_n}{\delta_n}\ge0.
$$

Therefore each of the three terms in $E_n$ is nonnegative, so $E_n\ge0$.

Similarly, `hW_nonneg : ∀ n, 0 ≤ W_n` is proved using

$$
\alpha_n\ge0,\quad \nu_n\ge0,\quad
h(x_n,x_{n+1})\ge0,\quad k(y_n,y_{n+1})\ge0,
$$

together with nonnegativity of $\mu_n/\delta_n$ and $\beta_n/\delta_n$. Hence both summands in $W_n$ are nonnegative.

The central step is `hE_step : ∀ n, E_{n+1}+W_n\le E_n`. It starts from the cited lemma `lemma_2_3`, applied to `alg` and `hyp`. That lemma gives the raw descent inequality

$$
\begin{aligned}
&\mu_n f(x_{n+1})+\beta_n g(y_{n+1})
+\beta_n\mu_n c(x_{n+1},y_{n+1})\\
&\quad+\mu_n\alpha_n h(x_n,x_{n+1})
+\beta_n\nu_n k(y_n,y_{n+1})\\
&\le
\mu_n f(x_n)+\beta_n g(y_n)+\beta_n\mu_n c(x_n,y_n).
\end{aligned}
$$

This is the algorithm’s one-step decrease: the new objective values plus the new coupling term plus the move costs are no larger than the old weighted objective and coupling term.

Since $\delta_n>0$, the proof divides the raw inequality by $\delta_n$ using `div_le_div_of_nonneg_right`. After clearing denominators with `field_simp` and rearranging with `ring`, it obtains the scaled inequality

$$
\begin{aligned}
&\frac{\mu_n}{\delta_n} f(x_{n+1})
+\frac{\beta_n}{\delta_n} g(y_{n+1})
+\frac{\beta_n\mu_n}{\delta_n} c(x_{n+1},y_{n+1})\\
&\quad+\frac{\mu_n}{\delta_n}\alpha_n h(x_n,x_{n+1})
+\frac{\beta_n}{\delta_n}\nu_n k(y_n,y_{n+1})\\
&\le
\frac{\mu_n}{\delta_n} f(x_n)
+\frac{\beta_n}{\delta_n} g(y_n)
+\frac{\beta_n\mu_n}{\delta_n} c(x_n,y_n).
\end{aligned}
$$

Subtracting the same quantity

$$
\frac{\mu_n}{\delta_n}inf_f+\frac{\beta_n}{\delta_n}inf_g
$$

from both sides and rearranging gives the intermediate inequality `hshift`:

$$
\begin{aligned}
&\frac{\mu_n}{\delta_n}(f(x_{n+1})-inf_f)
+\frac{\beta_n}{\delta_n}(g(y_{n+1})-inf_g)
+\frac{\beta_n\mu_n}{\delta_n}c(x_{n+1},y_{n+1})
+W_n\\
&\le E_n.
\end{aligned}
$$

Indeed, $W_n$ is precisely the two move-cost terms in the scaled inequality.

The proof then compares $E_{n+1}$ with the first three terms appearing on the left side of `hshift`. Since

$$
\frac{\mu_{n+1}}{\delta_{n+1}}\le\frac{\mu_n}{\delta_n},\quad
\frac{\beta_{n+1}}{\delta_{n+1}}\le\frac{\beta_n}{\delta_n},\quad
\frac{\beta_{n+1}\mu_{n+1}}{\delta_{n+1}}
\le\frac{\beta_n\mu_n}{\delta_n},
$$

and since

$$
f(x_{n+1})-inf_f\ge0,\quad
g(y_{n+1})-inf_g\ge0,\quad
c(x_{n+1},y_{n+1})\ge0,
$$

each coefficient at index $n+1$ can be replaced by the larger or equal coefficient at index $n$. This yields

$$
E_{n+1}
\le
\frac{\mu_n}{\delta_n}(f(x_{n+1})-inf_f)
+\frac{\beta_n}{\delta_n}(g(y_{n+1})-inf_g)
+\frac{\beta_n\mu_n}{\delta_n}c(x_{n+1},y_{n+1}).
$$

Adding $W_n$ to both sides and combining with `hshift` gives

$$
E_{n+1}+W_n\le E_n.
$$

Because $W_n\ge0$, the preceding inequality implies $E_{n+1}\le E_n$. The proof converts this into `hE_antitone : Antitone E` using `antitone_nat_of_succ_le`, whose visible consequence here is that a sequence on $\mathbb N$ satisfying $E_{n+1}\le E_n$ for all $n$ is nonincreasing.

It also shows $E$ is bounded below: since each $E_n\ge0$, the range of $E$ has lower bound $0$. The proof then defines

$$
L=\inf_n E_n.
$$

Using `tendsto_atTop_ciInf hE_antitone hE_bdd`, it obtains

$$
E_n\to L \quad \text{as } n\to\infty.
$$

Thus the antitone and bounded-below energy sequence converges to its infimum.

Finally the proof handles summability of $W$. It defines the partial sums

$$
S_N=\sum_{n=0}^{N-1} W_n.
$$

First, `hS_mono : Monotone S` is proved by observing that

$$
S_{N+1}=S_N+W_N\ge S_N
$$

because $W_N\ge0$. Next, `hS_tel : ∀ N, S_N\le E_0-E_N` is proved by induction. The induction step uses $E_{N+1}+W_N\le E_N$, which is equivalent to

$$
W_N\le E_N-E_{N+1}.
$$

Adding this to the induction hypothesis gives

$$
S_N+W_N\le (E_0-E_N)+(E_N-E_{N+1})=E_0-E_{N+1}.
$$

Since $E_N\ge0$, it follows that

$$
S_N\le E_0
$$

for every $N$. Hence the monotone sequence $S$ is bounded above by $E_0$.

The proof then applies `tendsto_atTop_ciSup hS_mono hS_bdd`, which gives convergence of the partial sums to their supremum:

$$
S_N\to \sup_N S_N.
$$

Because $W_n\ge0$ for every $n$, the lemma `hasSum_iff_tendsto_nat_of_nonneg` allows this convergence of nonnegative partial sums to be converted into summability of $W$. Finally, the proof assembles the witnesses $inf_f$, $inf_g$, and $L$, together with the lower-bound inequalities, the antitone property of $E$, the convergence $E_n\to L$, and the summability of $W$, yielding the stated theorem.

