## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/thm_1.lean`

## Lean statement
```lean
theorem theorem_2_4_b {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β β ν)
    (hyp : H21toH24 X Y f g h k c α β β ν)
    (hbeta_nonincreasing : ∀ n : ℕ, β (n+1) ≤ β n) :
    ∃ S : ℝ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      (α n * h (alg.x n) (alg.x (n+1)) + ν n * k (alg.y n) (alg.y (n+1))))) atTop (𝓝 S)
```

## Statement explanation
The declaration `theorem_2_4_b` says the following. Let \(X\) and \(Y\) be arbitrary types. There are real-valued functions
\[
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,
\]
two “movement cost” functions
\[
h:X\to X\to\mathbb R,\qquad k:Y\to Y\to\mathbb R,
\]
and a coupling cost
\[
c:X\to Y\to\mathbb R.
\]
There are also three sequences of real numbers
\[
\alpha,\beta,\nu:\mathbb N\to\mathbb R.
\]
The argument `alg : CA2 X Y f g h k c α β β ν` is an algorithm object. From the proof, it supplies two sequences \(x_n\in X\) and \(y_n\in Y\), written in Lean as `alg.x n` and `alg.y n`, together with the two update inequalities `alg.step_x` and `alg.step_y`. The argument `hyp : H21toH24 X Y f g h k c α β β ν` is a package of hypotheses. The proof uses the following consequences of it: \(\alpha_n\ge 0\), \(\nu_n\ge 0\), \(\beta_n>0\), \(h(x,x)=0\), \(k(y,y)=0\), \(h(x,x')\ge 0\), \(k(y,y')\ge 0\), \(c(x,y)\ge 0\), \(f\) is bounded below, and \(g\) is bounded below. The final hypothesis is
\[
hbeta\_nonincreasing : \forall n:\mathbb N,\quad \beta(n+1)\le \beta(n),
\]
so the sequence \(\beta\) is nonincreasing.

The conclusion is that there exists a real number \(S\) such that the partial sums
\[
N\mapsto \sum_{n=0}^{N-1}\Bigl(\alpha_n h(x_n,x_{n+1})+\nu_n k(y_n,y_{n+1})\Bigr)
\]
converge to \(S\) as \(N\to\infty\). In ordinary language, the accumulated weighted movement costs in the \(x\)-variable and in the \(y\)-variable form a convergent series. The theorem does not identify the limit \(S\) beyond saying that it is the supremum of the partial sums; the proof shows this by proving that the partial sums are nondecreasing and bounded above in \(\mathbb R\).

## Lean proof
```lean
by
  set E := fun (i : ℕ) => f (alg.x i) + g (alg.y i) + β i * c (alg.x i) (alg.y i) with hE
  set term := fun (n : ℕ) => α n * h (alg.x n) (alg.x (n+1)) + ν n * k (alg.y n) (alg.y (n+1)) with hterm
  set S_seq := fun (N : ℕ) => (∑ n ∈ Finset.range N, term n) with hS_seq
  -- Key inequality (from dividing Lemma 2.3 by β_n ≡ μ_n):
  -- E(i+1) + α_i*h + ν_i*k ≤ E(i)  with β_i on the LHS,
  -- then replace β_i by β_{i+1} using nonincrease. Final form: E(i+1) + term i ≤ E(i)
  have hone_step : ∀ i : ℕ, E (i+1) + term i ≤ E i := by
    intro i
    -- Step x with ξ = x_i, simplify h(x_i, x_i) = 0
    have hx := alg.step_x i (alg.x i)
    have hx_simp : f (alg.x (i+1)) + α i * h (alg.x i) (alg.x (i+1)) + β i * c (alg.x (i+1)) (alg.y i) ≤
        f (alg.x i) + β i * c (alg.x i) (alg.y i) := by
      simpa [hyp.h_diag_zero (alg.x i)] using hx
    -- Step y with η = y_i, simplify k(y_i, y_i) = 0
    have hy := alg.step_y i (alg.y i)
    have hy_simp : g (alg.y (i+1)) + β i * c (alg.x (i+1)) (alg.y (i+1)) + ν i * k (alg.y i) (alg.y (i+1)) ≤
        g (alg.y i) + β i * c (alg.x (i+1)) (alg.y i) := by
      simpa [hyp.k_diag_zero (alg.y i)] using hy
    -- Add the two and cancel the common β_i*c(x_{i+1}, y_i) term
    have hadd := add_le_add hx_simp hy_simp
    have hmain : f (alg.x (i+1)) + g (alg.y (i+1)) + β i * c (alg.x (i+1)) (alg.y (i+1)) +
        α i * h (alg.x i) (alg.x (i+1)) + ν i * k (alg.y i) (alg.y (i+1)) ≤
        f (alg.x i) + g (alg.y i) + β i * c (alg.x i) (alg.y i) := by
      linarith
    -- Since β is nonincreasing and c ≥ 0: β_{i+1}*c ≤ β_i*c
    have hbeta_c : β (i+1) * c (alg.x (i+1)) (alg.y (i+1)) ≤
        β i * c (alg.x (i+1)) (alg.y (i+1)) :=
      mul_le_mul_of_nonneg_right (hbeta_nonincreasing i) (hyp.c_nonneg _ _)
    -- Now combine: E(i+1) = f+g+β_{i+1}*c ≤ f+g+β_i*c, then add nonneg terms, use hmain
    unfold E term
    nlinarith
  -- Each term is nonnegative, so partial sums form a monotone sequence
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ term n := by
    intro n
    unfold term
    have h1 : 0 ≤ α n * h (alg.x n) (alg.x (n+1)) :=
      mul_nonneg (hyp.alpha_nonneg n) (hyp.h_nonneg _ _)
    have h2 : 0 ≤ ν n * k (alg.y n) (alg.y (n+1)) :=
      mul_nonneg (hyp.nu_nonneg n) (hyp.k_nonneg _ _)
    nlinarith
  have hS_succ : ∀ N : ℕ, S_seq N ≤ S_seq (N+1) := by
    intro N
    unfold S_seq
    rw [Finset.sum_range_succ]
    have h : 0 ≤ term N := hterm_nonneg N
    nlinarith
  have hS_mono : Monotone S_seq :=
    monotone_nat_of_le_succ hS_succ
  -- E is bounded below by Mf + Mg (since f, g bounded below, β>0, c≥0)
  rcases hyp.f_bdd_below with ⟨Mf, hMf⟩
  rcases hyp.g_bdd_below with ⟨Mg, hMg⟩
  have hE_lower : ∀ i : ℕ, Mf + Mg ≤ E i := by
    intro i
    unfold E
    have hf : Mf ≤ f (alg.x i) := hMf (alg.x i)
    have hg : Mg ≤ g (alg.y i) := hMg (alg.y i)
    have hc_nonneg : 0 ≤ c (alg.x i) (alg.y i) := hyp.c_nonneg _ _
    have hbeta_pos : 0 < β i := hyp.beta_pos i
    nlinarith
  -- Telescoping sum: S_seq(N) = Σ_{i=0}^{N-1} term(i) ≤ E(0) - E(N)
  have hsum_bound : ∀ N : ℕ, S_seq N ≤ E 0 - E N := by
    intro N
    induction' N with N ih
    · unfold S_seq; simp
    · unfold S_seq
      rw [Finset.sum_range_succ]
      have hterm_bound : term N ≤ E N - E (N+1) := by
        linarith [hone_step N]
      nlinarith
  have hS_upper : ∀ N : ℕ, S_seq N ≤ E 0 - (Mf + Mg) := by
    intro N
    have h1 : S_seq N ≤ E 0 - E N := hsum_bound N
    have h2 : Mf + Mg ≤ E N := hE_lower N
    linarith
  -- Bounded monotone sequence in ℝ converges to its supremum
  have h_bdd : BddAbove (Set.range S_seq) := by
    refine ⟨E 0 - (Mf + Mg), ?_⟩
    rintro y ⟨N, rfl⟩
    exact hS_upper N
  refine ⟨⨆ n, S_seq n, tendsto_atTop_ciSup hS_mono h_bdd⟩
```

## Proof explanation
The proof begins by introducing three abbreviations with `set`. First,
\[
E_i=f(x_i)+g(y_i)+\beta_i c(x_i,y_i)
\]
is a Lyapunov-type energy at step \(i\). Second,
\[
T_n=\alpha_n h(x_n,x_{n+1})+\nu_n k(y_n,y_{n+1})
\]
is the \(n\)-th term of the series whose convergence is being proved. Third,
\[
S_N=\sum_{n=0}^{N-1}T_n
\]
is the \(N\)-th partial sum, using `Finset.range N` for \(\{0,\dots,N-1\}\).

The main step is the inequality
\[
E_{i+1}+T_i\le E_i
\]
for every \(i\). To prove it, the proof introduces an arbitrary \(i\) with `intro i`. It applies the \(x\)-update inequality `alg.step_x i (alg.x i)`, which is the algorithm’s inequality for the \(x\)-step with test point \(\xi=x_i\). After simplifying \(h(x_i,x_i)\) to zero using `hyp.h_diag_zero`, this gives
\[
f(x_{i+1})+\alpha_i h(x_i,x_{i+1})+\beta_i c(x_{i+1},y_i)
\le
f(x_i)+\beta_i c(x_i,y_i).
\]
The tactic `simpa` both rewrites \(h(x_i,x_i)=0\) and simplifies the resulting inequality. Mathematically, this says that moving from \(x_i\) to \(x_{i+1}\) does not increase the \(x\)-part of the augmented objective, including the coupling cost at the current \(y_i\).

Similarly, the proof applies `alg.step_y i (alg.y i)`, the \(y\)-update inequality with test point \(\eta=y_i\). After simplifying \(k(y_i,y_i)\) to zero using `hyp.k_diag_zero`, it obtains
\[
g(y_{i+1})+\beta_i c(x_{i+1},y_{i+1})+\nu_i k(y_i,y_{i+1})
\le
g(y_i)+\beta_i c(x_{i+1},y_i).
\]
This says that the \(y\)-step does not increase the \(y\)-part of the augmented objective.

The proof then uses `add_le_add` to add the two inequalities. The common term \(\beta_i c(x_{i+1},y_i)\) cancels, and `linarith` derives
\[
\begin{aligned}
&f(x_{i+1})+g(y_{i+1})+\beta_i c(x_{i+1},y_{i+1})
+\alpha_i h(x_i,x_{i+1})+\nu_i k(y_i,y_{i+1})\\
&\qquad\le
f(x_i)+g(y_i)+\beta_i c(x_i,y_i).
\end{aligned}
\]
This is the combined descent inequality for one full iteration, before replacing \(\beta_i\) by \(\beta_{i+1}\).

Next the proof compares the coupling terms at step \(i+1\). Since \(\beta\) is nonincreasing, \(\beta_{i+1}\le \beta_i\), and since \(c(x_{i+1},y_{i+1})\ge 0\), the lemma `mul_le_mul_of_nonneg_right` gives
\[
\beta_{i+1}c(x_{i+1},y_{i+1})
\le
\beta_i c(x_{i+1},y_{i+1}).
\]
Therefore the energy \(E_{i+1}\), which uses \(\beta_{i+1}\), is no larger than the expression using \(\beta_i\) at the new points. Combining this with the previous combined descent inequality, and unfolding the definitions of \(E\) and \(T\), the tactic `nlinarith` concludes
\[
E_{i+1}+T_i\le E_i.
\]

The proof then shows that each \(T_n\) is nonnegative. Indeed,
\[
\alpha_n h(x_n,x_{n+1})\ge 0
\]
because \(\alpha_n\ge 0\) and \(h(x_n,x_{n+1})\ge 0\), and similarly
\[
\nu_n k(y_n,y_{n+1})\ge 0
\]
because \(\nu_n\ge 0\) and \(k(y_n,y_{n+1})\ge 0\). Hence \(0\le T_n\). Consequently,
\[
S_{N+1}=S_N+T_N\ge S_N.
\]
The proof obtains this by rewriting with `Finset.sum_range_succ`, which expresses the sum up to \(N+1\) as the sum up to \(N\) plus the term \(T_N\). The lemma `monotone_nat_of_le_succ` then turns the pointwise inequalities \(S_N\le S_{N+1}\) into the statement that the full sequence \(S_N\) is monotone.

To obtain an upper bound for the partial sums, the proof uses the lower bounds for \(f\) and \(g\). It destructs `hyp.f_bdd_below` and `hyp.g_bdd_below` with `rcases`, obtaining constants \(M_f\) and \(M_g\) such that
\[
M_f\le f(x)\quad\text{for all }x\in X,
\qquad
M_g\le g(y)\quad\text{for all }y\in Y.
\]
For every \(i\),
\[
E_i=f(x_i)+g(y_i)+\beta_i c(x_i,y_i)\ge M_f+M_g,
\]
because \(f(x_i)\ge M_f\), \(g(y_i)\ge M_g\), \(\beta_i>0\), and \(c(x_i,y_i)\ge 0\), so \(\beta_i c(x_i,y_i)\ge 0\). This is the inequality `hE_lower`.

Now the proof uses the one-step inequality \(E_{i+1}+T_i\le E_i\) to get
\[
T_i\le E_i-E_{i+1}.
\]
It proves by induction on \(N\) that
\[
S_N=\sum_{n=0}^{N-1}T_n
\le
\sum_{n=0}^{N-1}(E_n-E_{n+1})
=
E_0-E_N.
\]
The base case \(N=0\) is the empty sum \(S_0=0\), and \(0\le E_0-E_0\). The induction step uses `Finset.sum_range_succ` to write \(S_{N+1}=S_N+T_N\), then applies the induction hypothesis and the bound \(T_N\le E_N-E_{N+1}\). This is a telescoping estimate.

Combining this telescoping estimate with \(M_f+M_g\le E_N\) gives
\[
S_N\le E_0-(M_f+M_g)
\]
for every \(N\). Hence the set of all partial sums is bounded above, which the proof records as `BddAbove (Set.range S_seq)` with the explicit upper bound \(E_0-(M_f+M_g)\).

Finally, since \(S_N\) is monotone and bounded above in \(\mathbb R\), the theorem `tendsto_atTop_ciSup` applies. It states the standard fact that such a monotone sequence converges to its supremum:
\[
S_N\to \sup_{N} S_N
\]
as \(N\to\infty\). The proof therefore takes
\[
S=\sup_N S_N,
\]
written in Lean as `⨆ n, S_seq n`, and uses `refine ⟨..., ...⟩` to provide this real number as the existential witness. The resulting convergence is exactly the conclusion of the theorem: the series of weighted movement costs converges.

