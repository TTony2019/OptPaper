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
The theorem `limit_zero_of_memLp_deriv_bound` states the following. Let \(F,G:\mathbb R\to\mathbb R\) be real-valued functions, and let \(p,r\) be extended nonnegative real numbers, i.e. elements of \(\mathrm{ENNReal}=[0,\infty]\). Assume that
\[
1\le p,\qquad p\ne \top,\qquad 1\le r,
\]
so in particular \(p\) is finite and nonzero. Assume that \(F\) is nonnegative:
\[
\forall t,\quad 0\le F(t).
\]
Assume that \(F\) is absolutely continuous on the interval from \(0\) to \(b\) for every positive \(b\):
\[
\forall b>0,\quad \mathrm{AbsolutelyContinuousOnInterval}\ F\ 0\ b.
\]
Assume that \(F\in L^p\) with respect to Lebesgue measure, and \(G\in L^r\) with respect to Lebesgue measure:
\[
\mathrm{MemLp}\ F\ p\ \mathrm{volume},\qquad \mathrm{MemLp}\ G\ r\ \mathrm{volume}.
\]
Finally, assume that for almost every \(t\) with respect to Lebesgue measure,
\[
\mathrm{deriv}\ F(t)\le G(t).
\]
The conclusion is that \(F\) tends to \(0\) as \(t\to+\infty\):
\[
\mathrm{Tendsto}\ F\ \mathrm{atTop}\ (\mathrm{nhds}\ 0).
\]
Equivalently, for every \(\varepsilon>0\) there exists \(R\) such that for all \(t\ge R\),
\[
|F(t)|<\varepsilon.
\]
Because \(F\) is nonnegative, this is equivalent to \(F(t)\to 0\) from above as \(t\to\infty\).

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
The proof is by contradiction. It first extracts two useful consequences of the hypotheses, then assumes the limit is not zero and constructs infinitely many separated intervals on which \(F\) has uniformly positive mass, contradicting the \(L^p\)-integrability of \(F\).

First, the proof establishes an increment inequality:
\[
F(b)-F(a)\le \int_a^b G(x)\,dx
\]
for all \(a,b\) with \(0\le a\le b\). This is done using the library lemma `increment_le_interval_integral`, applied to the absolute continuity of \(F\), the derivative bound, and the integrability assumptions on \(G\). This inequality is the main link between the derivative bound and the growth of \(F\).

Second, the proof obtains a small-interval-integral property for \(G\). Using the lemma `eventual_interval_integral_upper` and the assumption \(G\in L^r\) with \(1\le r\), it proves that for every \(\eta>0\) there exist real numbers \(T\ge 0\) and \(L>0\) such that whenever
\[
T\le a\le b,\qquad b-a\le L,
\]
one has
\[
\int_a^b G(x)\,dx\le \eta.
\]
This says that sufficiently far to the right, interval integrals of \(G\) over intervals of bounded length become uniformly small. The proof applies this with \(\eta=\varepsilon/2\), where \(\varepsilon\) comes from the contradiction assumption.

The main contradiction begins with `by_contra`. It assumes that \(F\) does not tend to \(0\) at \(+\infty\). The command `rw [Metric.tendsto_atTop]` rewrites the metric tendsto condition into the usual epsilon-and-R form. Then `push Not` pushes the negation through the quantifiers, producing a positive \(\varepsilon\) such that for every \(R\) there exists \(t\ge R\) with
\[
\varepsilon\le \operatorname{dist}(F(t),0).
\]
Using nonnegativity of \(F\), the proof simplifies this to
\[
\varepsilon\le F(t).
\]
Thus for every \(R\), there are arbitrarily large times \(t\ge R\) at which \(F(t)\ge\varepsilon\).

Choose \(T\) and \(L\) from the small-interval-integral property for \(G\) with \(\eta=\varepsilon/2\). The proof then recursively constructs a sequence \(t_n\) of real numbers such that
\[
t_0\ge T+L,\qquad t_{n+1}\ge t_n+2L,
\]
and such that
\[
F(t_n)\ge \varepsilon
\]
for every \(n\). This is done with `Classical.choose` and `Nat.rec`. The first inequality is called `ht_step` in the proof. An induction then gives
\[
t_n\ge T+L
\]
for every \(n\).

For each \(n\), define the interval
\[
J_n=(t_n-L,\ t_n].
\]
These intervals are subsets of \((0,\infty)\), because \(t_n\ge T+L\) and \(T\ge 0\), so \(t_n-L\ge T\ge 0\).

The proof then shows that on each \(J_n\),
\[
F(x)\ge \frac{\varepsilon}{2}.
\]
Indeed, if \(x\in J_n\), then \(t_n-L<x\le t_n\). In particular, \(x\ge T\) and \(t_n-x\le L\). Applying the increment inequality with \(a=x\) and \(b=t_n\),
\[
F(t_n)-F(x)\le \int_x^{t_n} G(u)\,du.
\]
By the small-interval-integral property of \(G\), the right side is at most \(\varepsilon/2\). Since \(F(t_n)\ge \varepsilon\), linear arithmetic, performed by `linarith`, gives
\[
F(x)\ge \varepsilon/2.
\]

Using disjointness of the \(J_n\), the proof then converts this pointwise lower bound into an integral lower bound. The intervals \(J_m\) and \(J_n\) are disjoint when \(m<n\), because the recursive spacing gives
\[
t_m+2L\le t_n,
\]
so \(J_m\) ends at \(t_m\), while \(J_n\) begins at \(t_n-L\ge t_m+L\). This separation is proved by the local argument involving `hsep` and `linarith`.

Since \(F(x)\ge \varepsilon/2>0\) on \(J_n\), and \(F\) is nonnegative, one has
\[
|F(x)|\ge \varepsilon/2.
\]
Raising to the real power \(p.toReal\), using monotonicity of the real power function, gives
\[
|F(x)|^{p.toReal}\ge \left(\frac{\varepsilon}{2}\right)^{p.toReal}.
\]
This is the content of the local lemma `hpointpow`.

Next, the proof uses the \(L^p\) assumption on \(F\). Since \(p\) is finite, nonzero, and at least \(1\), the lemma `hF.integrable_norm_rpow` gives that
\[
x\mapsto |F(x)|^{p.toReal}
\]
is integrable over the whole real line, hence over \((0,\infty)\) and over each \(J_n\). This is represented by `hFpow` and `hint`.

On each interval \(J_n\), the constant function
\[
x\mapsto \left(\frac{\varepsilon}{2}\right)^{p.toReal}
\]
is pointwise dominated by \(x\mapsto |F(x)|^{p.toReal}\). Therefore, by monotonicity of the integral, the proof obtains
\[
\left(\frac{\varepsilon}{2}\right)^{p.toReal}L
\le
\int_{J_n} |F(x)|^{p.toReal}\,dx.
\]
Here the left side is the integral of the constant function over \(J_n\), whose Lebesgue measure is \(L\). The relevant integral computation uses `integral_const` and the measure computation for an interval, with `simp` and `ring` closing the algebraic arithmetic.

For any natural number \(N\), let \(U\) be the union of the first \(N\) intervals \(J_0,\dots,J_{N-1}\). Since these intervals are pairwise disjoint, the integral over \(U\) is the sum of the integrals over the individual intervals. The command `integral_biUnion_finset` is used for this finite disjoint union. Summing the lower bound over \(n=0,\dots,N-1\) gives
\[
N\cdot \left(\frac{\varepsilon}{2}\right)^{p.toReal}L
\le
\int_U |F(x)|^{p.toReal}\,dx.
\]
Since \(U\subseteq (0,\infty)\), monotonicity of the set integral gives
\[
\int_U |F(x)|^{p.toReal}\,dx
\le
\int_{(0,\infty)} |F(x)|^{p.toReal}\,dx.
\]
Thus for every \(N\),
\[
N\cdot \left(\frac{\varepsilon}{2}\right)^{p.toReal}L
\le
\int_{(0,\infty)} |F(x)|^{p.toReal}\,dx.
\]

Finally, the factor
\[
m:=\left(\frac{\varepsilon}{2}\right)^{p.toReal}L
\]
is strictly positive. Let
\[
M:=\int_{(0,\infty)} |F(x)|^{p.toReal}\,dx.
\]
The Archimedean property of the reals gives a natural number \(N\) such that
\[
N>\frac{M}{m}.
\]
Equivalently,
\[
Nm>M.
\]
The command `exact_mod_cast` handles the natural-to-real casting in this step. But the previous inequality states
\[
Nm\le M,
\]
a contradiction. The proof concludes with `linarith [hmass N]`, using the contradiction between the lower bound and the upper bound.

Important Lean tactics used in the proof include: `intro` to introduce local variables, `rw` to rewrite using metric tendsto and integral identities, `simp` to simplify measure and arithmetic goals, `exact` to supply direct proof terms, `linarith` to close linear inequalities, `by_contra` for contradiction, `rcases` for destructuring existentials, `induction` to prove facts about all natural numbers, `gcongr` for generalized congruence reasoning with sums, `filter_upwards` to prove almost-everywhere properties, and `calc` for chained inequalities.

