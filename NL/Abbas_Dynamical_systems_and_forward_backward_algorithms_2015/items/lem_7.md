## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_7.lean`

## Lean statement
```lean
theorem limit_zero_of_memLp_deriv_bound (F G : ℝ → ℝ) (p r : ENNReal)
    (hp : 1 ≤ p) (hp_top : p ≠ (⊤ : ENNReal)) (hr : 1 ≤ r)
    (hF_nonneg : ∀ t, 0 ≤ F t) (hF_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval F 0 b)
    (hF : MemLp F p volume) (hG : MemLp G r volume)
    (hderiv : ∀ᵐ t ∂volume, deriv F t ≤ G t) : Tendsto F atTop (nhds 0)
```

## Statement explanation
The declaration `limit_zero_of_memLp_deriv_bound` is a theorem about two functions $F,G:\mathbb R\to\mathbb R$, two extended nonnegative real exponents $p,r$, and Lebesgue measure $\mathrm{volume}$ on $\mathbb R$. The hypotheses are:

- $1\le p$, $p\ne \top$, and $1\le r$. Thus $p$ is a finite exponent at least $1$, and $r$ is an exponent at least $1$.
- $F(t)\ge 0$ for every $t\in\mathbb R$.
- For every $b\gt 0$, $F$ is absolutely continuous on the interval $[0,b]$.
- $F\in L^p(\mathbb R)$ and $G\in L^r(\mathbb R)$, expressed by `MemLp F p volume` and `MemLp G r volume`.
- For almost every $t$ with respect to Lebesgue measure,

$$
\mathrm{deriv}F(t)\le G(t).
$$

The conclusion is

$$
F(t)\to 0 \qquad (t\to+\infty),
$$

formally `Tendsto F atTop (nhds 0)`.

Mathematically, the theorem says that a nonnegative absolutely continuous function on the positive half-line must vanish at infinity if its derivative is bounded above almost everywhere by an $L^r$ function and the function itself lies in $L^p$ for some finite $p\ge1$. The proof is by contradiction: if $F$ stayed above a fixed positive level arbitrarily far to the right, then the derivative bound would force $F$ to remain above half that level on infinitely many disjoint intervals of positive length. That would force the $L^p$ mass of $F$ to be infinite, contradicting $F\in L^p$.

## Lean proof
```lean
by
  have hincrement : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b →
      F b - F a ≤ ∫ x in a..b, G x :=
    fun a b ha hab => increment_le_interval_integral F G r hr hF_ac hG hderiv ha hab
  have hsmall : ∀ eta : ℝ, 0 < eta → ∃ T L : ℝ, 0 ≤ T ∧ 0 < L ∧
      ∀ {a b : ℝ}, T ≤ a → a ≤ b → b - a ≤ L →
        (∫ x in a..b, G x) ≤ eta :=
    eventual_interval_integral_upper hr hG
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨epsilon, hepsilon, hhigh⟩
  have hhigh' : ∀ R : ℝ, ∃ t ≥ R, epsilon ≤ F t :=
    fun R => by
      rcases hhigh R with ⟨t, htR, ht⟩
      exact ⟨t, htR, by simpa [Real.dist_eq, abs_of_nonneg (hF_nonneg t)] using ht⟩
  rcases hsmall (epsilon / 2) (by linarith) with
    ⟨T, L, hT, hL, hsmall_interval⟩
  let t : ℕ → ℝ := Nat.rec (Classical.choose (hhigh' (T + L)))
    (fun _ x => Classical.choose (hhigh' (x + 2 * L)))
  have ht_zero : T + L ≤ t 0 := (Classical.choose_spec (hhigh' (T + L))).1
  have ht_high : ∀ n, epsilon ≤ F (t n) := by
    intro n
    induction n with
    | zero => exact (Classical.choose_spec (hhigh' (T + L))).2
    | succ n ih =>
      exact (Classical.choose_spec (hhigh' (t n + 2 * L))).2
  have ht_step : ∀ n, t n + 2 * L ≤ t (n + 1) :=
    fun n => (Classical.choose_spec (hhigh' (t n + 2 * L))).1
  have ht_lower : ∀ n, T + L ≤ t n := by
    intro n
    induction n with
    | zero => exact ht_zero
    | succ n ih => linarith [ht_step n]
  let J : ℕ → Set ℝ := fun n => Set.Ioc (t n - L) (t n)
  have hJpos : ∀ n, J n ⊆ Set.Ioi 0 := by
    intro n x hx
    change t n - L < x ∧ x ≤ t n at hx
    have hn := ht_lower n
    change 0 < x
    linarith
  have hlower : ∀ n x, x ∈ J n → epsilon / 2 ≤ F x := by
    intro n x hx
    change t n - L < x ∧ x ≤ t n at hx
    have hxn : T ≤ x := by
      have hn := ht_lower n
      linarith
    have hlen : t n - x ≤ L := by linarith
    have hinc := hincrement (a := x) (b := t n) (le_trans hT hxn) hx.2
    have hsmall' := hsmall_interval hxn hx.2 hlen
    linarith [ht_high n]
  have hsep : ∀ {m n : ℕ}, m < n → t m + 2 * L ≤ t n := by
    intro m n hmn
    exact Nat.le_induction (ht_step m)
      (fun k _ ih => by linarith [ht_step k]) n (by omega : m + 1 ≤ n)
  have hpointpow : ∀ n x, x ∈ J n →
      (epsilon / 2) ^ p.toReal ≤ |F x| ^ p.toReal := by
    intro n x hx
    have hlow := hlower n x hx
    rw [abs_of_nonneg (hF_nonneg x)]
    exact Real.rpow_le_rpow (by linarith) hlow ENNReal.toReal_nonneg
  have hFpow : IntegrableOn (fun x => |F x| ^ p.toReal) (Set.Ioi 0) :=
    (hF.integrable_norm_rpow (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top).restrict
  have hint : ∀ n, IntegrableOn (fun x => |F x| ^ p.toReal) (J n) :=
    fun n => hFpow.mono_set (hJpos n)
  have hmass_one : ∀ n, (epsilon / 2) ^ p.toReal * L ≤
      ∫ x in J n, |F x| ^ p.toReal := by
    intro n
    have hconst : IntegrableOn (fun _ : ℝ => (epsilon / 2) ^ p.toReal) (J n) := by
      simp [J, Real.volume_Ioc]
    have hmono : (∫ _x in J n, (epsilon / 2) ^ p.toReal) ≤
        ∫ x in J n, |F x| ^ p.toReal := by
      apply integral_mono_ae hconst (hint n)
      change (fun _x => (epsilon / 2) ^ p.toReal) ≤ᵐ[
        volume.restrict (Set.Ioc (t n - L) (t n))] fun x => |F x| ^ p.toReal
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (by
        filter_upwards with x hx
        exact hpointpow n x hx)
    calc
      (epsilon / 2) ^ p.toReal * L = ∫ _x in J n, (epsilon / 2) ^ p.toReal := by
        rw [integral_const]
        simp [J, hL.le]
        ring
      _ ≤ ∫ x in J n, |F x| ^ p.toReal := hmono
  have hmass : ∀ N : ℕ, (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) ≤
      ∫ x in Set.Ioi 0, |F x| ^ p.toReal := by
    intro N
    let U : Set ℝ := ⋃ n ∈ Finset.range N, J n
    have hU : U ⊆ Set.Ioi 0 := by
      intro x hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨n, hx⟩
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨hn, hx⟩
      exact hJpos n hx
    have hdisj : Set.Pairwise Set.univ (Function.onFun Disjoint J) := by
      intro m hm n hn hmn
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · apply Set.disjoint_left.2
        intro x hxm hxn
        change t m - L < x ∧ x ≤ t m at hxm
        change t n - L < x ∧ x ≤ t n at hxn
        have hs := hsep hlt
        linarith
      · apply Set.disjoint_left.2
        intro x hxm hxn
        change t m - L < x ∧ x ≤ t m at hxm
        change t n - L < x ∧ x ≤ t n at hxn
        have hs := hsep hgt
        linarith
    have hsum : (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) ≤
        ∑ n ∈ Finset.range N, ∫ x in J n, |F x| ^ p.toReal := by
      calc
        (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) =
            ∑ _n ∈ Finset.range N, ((epsilon / 2) ^ p.toReal * L) := by simp
        _ ≤ ∑ n ∈ Finset.range N, ∫ x in J n, |F x| ^ p.toReal := by
          gcongr with n hn
          exact hmass_one n
    have hUnion : (∫ x in U, |F x| ^ p.toReal) =
        ∑ n ∈ Finset.range N, ∫ x in J n, |F x| ^ p.toReal := by
      dsimp [U]
      exact integral_biUnion_finset (Finset.range N)
        (fun n _ => measurableSet_Ioc) (fun m hm n hn hmn => hdisj (by simp) (by simp) hmn)
        (fun n _ => hint n)
    calc
      (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) ≤ ∫ x in U, |F x| ^ p.toReal := by
        rw [hUnion]
        exact hsum
      _ ≤ ∫ x in Set.Ioi 0, |F x| ^ p.toReal :=
        setIntegral_mono_set hFpow
          (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg (F x)) p.toReal)
          (Eventually.of_forall fun x hx => hU hx)
  have hc_pos : 0 < (epsilon / 2) ^ p.toReal * L :=
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) hL
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x in Set.Ioi 0, |F x| ^ p.toReal) /
    ((epsilon / 2) ^ p.toReal * L))
  have hN' : ∫ x in Set.Ioi 0, |F x| ^ p.toReal <
      (N : ℝ) * ((epsilon / 2) ^ p.toReal * L) :=
    (div_lt_iff₀ hc_pos).mp (by exact_mod_cast hN)
  linarith [hmass N]
```

## Proof explanation
The proof begins by recording two consequences of the cited lemmas.

First, it establishes the increment inequality

```math
F(b)-F(a)\le \int_a^b G(x)\,dx
```

for all $0\le a\le b$. This is exactly the conclusion of `increment_le_interval_integral`, applied with the present $F,G,r$. The hypotheses supplied to that lemma are $1\le r$, the absolute continuity of $F$ on every $[0,b]$ with $b\gt 0$, the membership $G\in L^r$, and the almost-everywhere derivative bound $\mathrm{deriv}F(t)\le G(t)$. The lemma converts the pointwise almost-everywhere differential inequality into an integral inequality controlling the increase of $F$.

Second, the proof records the small-interval property

$$
\forall \eta>0,\ \exists T,L,\ 0\le T,\ 0<L,
$$

such that for all $a,b$,

```math
T\le a,\quad a\le b,\quad b-a\le L
\quad\Longrightarrow\quad
\int_a^b G(x)\,dx\le \eta.
```

This is the conclusion of `eventual_interval_integral_upper`, applied with $1\le r$ and $G\in L^r$. It says that, sufficiently far to the right, the integral of $G$ over any interval of length at most $L$ is as small as desired.

The proof then argues by contradiction. It assumes the negation of $F(t)\to0$. Using the metric characterization of convergence along `atTop`, the negation becomes: there exists $\varepsilon\gt 0$ such that for every $R$ there is some $t\ge R$ with

$$
\varepsilon\le \mathrm{dist}(F(t),0).
$$

Because $F(t)\ge0$, we have $\mathrm{dist}(F(t),0)=|F(t)|=F(t)$. Thus there are arbitrarily large $t$ with

$$
\varepsilon\le F(t).
$$

The command `push_neg` is what turns the negated metric convergence statement into this existential form, and `rcases` extracts the witnesses $\varepsilon$, the positivity proof, and the higher-and-higher points.

Applying the small-interval property with $\eta=\varepsilon/2$ gives numbers $T,L$ with $T\ge0$, $L\gt 0$, and such that every interval $[a,b]$ lying to the right of $T$ and having length at most $L$ satisfies

```math
\int_a^b G(x)\,dx\le \frac{\varepsilon}{2}.
```

Next the proof constructs a sequence $t_n$ recursively. Since $F$ is at least $\varepsilon$ at arbitrarily large arguments, it chooses

$$
t_0\ge T+L,\qquad F(t_0)\ge\varepsilon,
$$

and then, given $t_n$, chooses

$$
t_{n+1}\ge t_n+2L,\qquad F(t_{n+1})\ge\varepsilon.
$$

The Lean construction uses `Classical.choose` to select these points from the existential statement. The properties are proved by induction: every $t_n$ satisfies $t_n\ge T+L$, every $t_n$ satisfies $F(t_n)\ge\varepsilon$, and every step satisfies $t_n+2L\le t_{n+1}$. From these step inequalities the proof also obtains the separation property

$$
m<n \quad\Longrightarrow\quad t_m+2L\le t_n.
$$

This is proved by iterating the step inequality, using natural-number induction and natural arithmetic.

For each $n$, define the interval

$$
J_n=(t_n-L,t_n].
$$

Because $t_n\ge T+L$ and $T\ge0$, each $J_n$ lies inside $(0,\infty)$. If $x\in J_n$, then

$$
T\le x\le t_n
$$

and

$$
t_n-x\le L.
$$

Therefore the increment inequality applies to $a=x$ and $b=t_n$, giving

```math
F(t_n)-F(x)\le \int_x^{t_n}G(u)\,du.
```

The interval $[x,t_n]$ is far enough to the right and has length at most $L$, so the small-interval property gives

```math
\int_x^{t_n}G(u)\,du\le \frac{\varepsilon}{2}.
```

Since $F(t_n)\ge\varepsilon$, it follows that

$$
F(x)\ge \frac{\varepsilon}{2}
$$

for every $x\in J_n$. This is the key lower bound on each interval $J_n$.

The proof then raises this lower bound to the power $p_{\mathrm{toReal}}$, the real value of the extended real exponent $p$. Since $F(x)\ge0$, one has $|F(x)|=F(x)$. Since $p_{\mathrm{toReal}}\ge0$ and $\varepsilon/2\le F(x)$, the monotonicity of real powers for nonnegative bases gives

$$
\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}
\le |F(x)|^{p_{\mathrm{toReal}}}
$$

for $x\in J_n$. This uses the lemma `Real.rpow_le_rpow`, whose content is exactly that $u\le v$ with $u,v\ge0$ implies $u^s\le v^s$ for nonnegative real exponents $s$.

Next, the proof obtains integrability of the function $x\mapsto |F(x)|^{p_{\mathrm{toReal}}}$ on $(0,\infty)$. From $F\in L^p$, together with $p\ne0$ and $p\ne\top$, the `MemLp` lemma `hF.integrable_norm_rpow` gives that $x\mapsto |F(x)|^{p_{\mathrm{toReal}}}$ is integrable on $\mathbb R$. Restricting to $(0,\infty)$ gives integrability there. Since each $J_n\subseteq(0,\infty)$, the restricted integrability on every $J_n$ follows by monotonicity of integrability on subsets.

For each fixed $n$, the constant

$$
c=\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}
$$

satisfies $c\le |F(x)|^{p_{\mathrm{toReal}}}$ on $J_n$. The interval $J_n$ has length $L$, so

```math
\int_{J_n} c\,dx=cL.
```

Therefore, using `integral_mono_ae` to compare the constant integrand with the nonnegative integrand $|F|^{p_{\mathrm{toReal}}}$, the proof obtains

```math
\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L
\le
\int_{J_n}|F(x)|^{p_{\mathrm{toReal}}}\,dx.
```

The computation of the constant integral uses `integral_const` and the fact that the Lebesgue measure of $(t_n-L,t_n]$ is $L$.

The intervals $J_n$ are pairwise disjoint. Indeed, if $m\lt n$, then $t_m+2L\le t_n$. Any $x\in J_m$ satisfies $x\le t_m$, while any $x\in J_n$ satisfies

$$
x>t_n-L\ge t_m+L.
$$

Thus $x\gt t_m$, contradicting $x\le t_m$. The Lean proof packages this as a pairwise disjointness statement and proves it by splitting into the cases $m\lt n$ and $n\lt m$.

For any natural number $N$, let

$$
U=\bigcup_{n=0}^{N-1}J_n.
$$

This union is contained in $(0,\infty)$, and the $J_n$ are pairwise disjoint. The integral over the finite disjoint union equals the sum of the integrals:

```math
\int_U |F(x)|^{p_{\mathrm{toReal}}}\,dx
=\sum_{n=0}^{N-1}
\int_{J_n}|F(x)|^{p_{\mathrm{toReal}}}\,dx.
```

This is the content of `integral_biUnion_finset`, applied to the finite family of disjoint measurable intervals. Using the lower bound on each $J_n$, the proof obtains

```math
N\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L
\le
\int_U |F(x)|^{p_{\mathrm{toReal}}}\,dx.
```

Since $U\subseteq(0,\infty)$ and the integrand is nonnegative, the set integral over $U$ is at most the set integral over $(0,\infty)$. This uses `setIntegral_mono_set`, whose mathematical meaning here is that enlarging the domain of integration cannot decrease the integral of a nonnegative function. Hence

```math
N\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L
\le
\int_{(0,\infty)}|F(x)|^{p_{\mathrm{toReal}}}\,dx
```

for every $N$.

Finally, the proof observes that

$$
\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L>0.
$$

The first factor is positive because $\varepsilon/2\gt 0$ and the real power of a positive number is positive; the second is positive because $L\gt 0$. Therefore one may choose a natural number $N$ with

```math
N>
\frac{\int_{(0,\infty)}|F(x)|^{p_{\mathrm{toReal}}}\,dx}
{\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L}.
```

This uses the Archimedean property via `exists_nat_gt`. Multiplying by the positive denominator gives

```math
\int_{(0,\infty)}|F(x)|^{p_{\mathrm{toReal}}}\,dx
<
N\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L.
```

But the previous inequality says the reverse:

```math
N\left(\frac{\varepsilon}{2}\right)^{p_{\mathrm{toReal}}}L
\le
\int_{(0,\infty)}|F(x)|^{p_{\mathrm{toReal}}}\,dx.
```

This contradiction is closed by `linarith`. Hence the assumption that $F(t)$ does not tend to $0$ as $t\to+\infty$ is false, and therefore

$$
F(t)\to 0 \qquad (t\to+\infty).
$$

