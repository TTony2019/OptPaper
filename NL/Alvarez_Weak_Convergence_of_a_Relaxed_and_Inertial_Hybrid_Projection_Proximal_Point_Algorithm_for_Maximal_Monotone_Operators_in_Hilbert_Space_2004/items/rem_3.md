## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/rem_3.lean`

## Lean statement
```lean
theorem remark_3_condition_33_from_312
    (x y eta : ℕ → H) (lam alpha : ℕ → ℝ) (xbar : H)
    (hy : ∀ k : ℕ, y k = x k + alpha k • (x k - x (k - 1)))
    (h31 : Summable fun k : ℕ ↦ lam k * ‖eta k‖)
    (h312 : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖)
    (hineq :
      ∀ k : ℕ,
        ‖x (k + 1) - xbar‖ ≤
          ‖x k - xbar‖ + alpha k * ‖x k - x (k - 1)‖ +
            lam k * ‖eta k‖)
    (hlam_nonneg : ∀ k : ℕ, 0 ≤ lam k) :
    (∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l)) ∧
      Bornology.IsBounded (Set.range y) ∧
      Summable (fun k : ℕ ↦ lam k * ‖eta k‖ * ‖y k‖)
```

## Statement explanation
The declaration is a theorem about sequences in an ambient real normed vector space $H$. Its data are sequences

$$
x,y,\eta:\mathbb N\to H,\qquad \lambda,\alpha:\mathbb N\to\mathbb R,
$$

and a point $\bar x\in H$. Here $k-1$ is Lean’s natural-number subtraction, so for $k=0$ it is simply $0$.

The hypotheses are as follows.

1. For every $k\in\mathbb N$,

$$
y_k=x_k+\alpha_k(x_k-x_{k-1}).
$$

Thus $y$ is obtained from $x$ by an inertial or extrapolated correction involving the previous difference $x_k-x_{k-1}$.

2. The series

$$
\sum_{k=0}^{\infty}\lambda_k\|\eta_k\|
$$

converges.

3. The series

$$
\sum_{k=0}^{\infty}\alpha_k\|x_k-x_{k-1}\|
$$

converges. Note that no sign condition is imposed on $\alpha_k$.

4. For every $k\in\mathbb N$,

$$
\|x_{k+1}-\bar x\|
\le
\|x_k-\bar x\|
+\alpha_k\|x_k-x_{k-1}\|
+\lambda_k\|\eta_k\|.
$$

This controls how much the distance from $x_k$ to $\bar x$ can increase from one step to the next.

5. For every $k\in\mathbb N$,

$$
0\le \lambda_k.
$$

The conclusion is the conjunction of three assertions:

$$
\bigl(\exists\,l\in\mathbb R,\ \|x_k-\bar x\|\to l\bigr)
\;\wedge\;
\{y_k:k\in\mathbb N\}\text{ is bounded}
\;\wedge\;
\sum_{k=0}^{\infty}\lambda_k\|\eta_k\|\,\|y_k\|<\infty.
$$

In words: the distance sequence $\|x_k-\bar x\|$ converges to a finite real limit; the sequence $y$ has bounded range; and the weighted series involving $\lambda_k\|\eta_k\|\|y_k\|$ is summable.

The mathematical idea is that the two summable perturbations

$$
\alpha_k\|x_k-x_{k-1}\|,\qquad \lambda_k\|\eta_k\|
$$

are collectively summable. The inequality says that the distance from $x_k$ to $\bar x$ can grow only by the $k$-th perturbation term. Therefore the quantity obtained by subtracting the partial sums of the perturbations from $\|x_k-\bar x\|$ is nonincreasing. Since those partial sums converge, the original distance sequence also converges. The summability of $\alpha_k\|x_k-x_{k-1}\|$ forces the correction terms $\alpha_k(x_k-x_{k-1})$ to be bounded, which makes $y$ bounded. Finally, boundedness of $y$ lets one compare $\lambda_k\|\eta_k\|\|y_k\|$ with a constant multiple of the summable series $\lambda_k\|\eta_k\|$.

## Lean proof
```lean
by
  let d : ℕ → ℝ := fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ + lam k * ‖eta k‖
  have hd_summable : Summable d := Summable.add h312 h31
  let s : ℕ → ℝ := fun n : ℕ ↦ (Finset.range n).sum d
  have hd_hasSum : HasSum d (∑' k, d k) := Summable.hasSum hd_summable
  have hs_tendsto : Tendsto s atTop (𝓝 (∑' k, d k)) := by
    simpa [s, HasSum] using hd_hasSum.comp Filter.tendsto_finset_range
  let φ : ℕ → ℝ := fun k : ℕ ↦ ‖x k - xbar‖
  let ψ : ℕ → ℝ := fun k : ℕ ↦ φ k - s k
  have hpsi_nonincr : ∀ k, ψ (k + 1) ≤ ψ k := by
    intro k
    dsimp [ψ, φ, s, d]
    rw [Finset.sum_range_succ]
    linarith [hineq k]
  have hs_bddAbove : BddAbove (Set.range s) := hs_tendsto.bddAbove_range
  obtain ⟨Bu, hBu⟩ := hs_bddAbove
  have hs_le_Bu (k : ℕ) : s k ≤ Bu := hBu (Set.mem_range_self k)
  have hpsi_bdd_below : ∀ k, -Bu ≤ ψ k := by
    intro k
    dsimp [ψ, φ]
    have h_nonneg : 0 ≤ ‖x k - xbar‖ := norm_nonneg _
    linarith [hs_le_Bu k]
  have hpsi_anti : Antitone ψ := by
    exact antitone_nat_of_succ_le hpsi_nonincr
  have hpsi_bddBelow : BddBelow (Set.range ψ) := by
    refine ⟨-Bu, ?_⟩
    rintro z ⟨k, rfl⟩
    exact hpsi_bdd_below k
  set psiInf := ⨅ n, ψ n with hpsiInf_def
  have hψ_tendsto : Tendsto ψ atTop (𝓝 psiInf) := by
    simpa [psiInf] using tendsto_atTop_ciInf hpsi_anti hpsi_bddBelow
  have hφ_tendsto : Tendsto φ atTop (𝓝 (psiInf + (∑' k, d k))) := by
    have h_eq : φ = ψ + s := by
      ext k
      dsimp [ψ, φ, s]
      ring
    rw [h_eq]
    exact Filter.Tendsto.add hψ_tendsto hs_tendsto
  have h_goal1 : ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l) :=
    ⟨psiInf + (∑' k, d k), by simpa [φ] using hφ_tendsto⟩
  have hφ_bddAbove : BddAbove (Set.range φ) := hφ_tendsto.bddAbove_range
  obtain ⟨M, hM⟩ := hφ_bddAbove
  have hφk_le_M (k : ℕ) : ‖x k - xbar‖ ≤ M := hM (Set.mem_range_self k)
  have h_term_tendsto :
      Tendsto (fun k : ℕ => alpha k * ‖x k - x (k - 1)‖) atTop (𝓝 0) :=
    h312.tendsto_atTop_zero
  have h_abs_term_tendsto :
      Tendsto (fun k : ℕ => |alpha k * ‖x k - x (k - 1)‖|) atTop (𝓝 0) := by
    simpa [abs_zero] using h_term_tendsto.abs
  have h_abs_term_bdd :
      BddAbove (Set.range fun k : ℕ => |alpha k| * ‖x k - x (k - 1)‖) := by
    have htmp := h_abs_term_tendsto.bddAbove_range
    simpa [abs_mul, abs_of_nonneg (norm_nonneg _)] using htmp
  obtain ⟨B₁, hB₁⟩ := h_abs_term_bdd
  have h_alpha_term_bound (k : ℕ) : |alpha k| * ‖x k - x (k - 1)‖ ≤ B₁ :=
    hB₁ (Set.mem_range_self k)
  have hy_norm_bound (k : ℕ) : ‖y k‖ ≤ M + ‖xbar‖ + B₁ := by
    rw [hy k]
    calc
      ‖x k + alpha k • (x k - x (k - 1))‖
          ≤ ‖x k‖ + ‖alpha k • (x k - x (k - 1))‖ := norm_add_le _ _
      _ = ‖x k‖ + |alpha k| * ‖x k - x (k - 1)‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ = ‖(x k - xbar) + xbar‖ + |alpha k| * ‖x k - x (k - 1)‖ := by
        congr 1
        abel_nf
      _ ≤ ‖x k - xbar‖ + ‖xbar‖ + |alpha k| * ‖x k - x (k - 1)‖ := by
        have htri := norm_add_le (x k - xbar) xbar
        linarith
      _ ≤ M + ‖xbar‖ + B₁ := by
        linarith [hφk_le_M k, h_alpha_term_bound k]
  set C := M + ‖xbar‖ + B₁ with hC_def
  have h_range_y_bdd : Bornology.IsBounded (Set.range y) := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * C, ?_⟩
    rintro z ⟨i, rfl⟩ w ⟨j, rfl⟩
    have hdist : dist (y i) (y j) ≤ ‖y i‖ + ‖y j‖ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using norm_add_le (y i) (-y j)
    linarith [hdist, hy_norm_bound i, hy_norm_bound j]
  have h_lam_eta_nonneg (k : ℕ) : 0 ≤ lam k * ‖eta k‖ :=
    mul_nonneg (hlam_nonneg k) (norm_nonneg _)
  have h_term_nonneg (k : ℕ) : 0 ≤ lam k * ‖eta k‖ * ‖y k‖ :=
    mul_nonneg (h_lam_eta_nonneg k) (norm_nonneg _)
  have h_term_le (k : ℕ) : lam k * ‖eta k‖ * ‖y k‖ ≤ C * (lam k * ‖eta k‖) := by
    have hyC : ‖y k‖ ≤ C := hy_norm_bound k
    nlinarith [h_lam_eta_nonneg k]
  have h31_const : Summable (fun k : ℕ => C * (lam k * ‖eta k‖)) :=
    h31.mul_left C
  have h_summable_33 : Summable (fun k : ℕ => lam k * ‖eta k‖ * ‖y k‖) :=
    Summable.of_nonneg_of_le h_term_nonneg h_term_le h31_const
  exact ⟨h_goal1, h_range_y_bdd, h_summable_33⟩
```

## Proof explanation
The proof begins by defining

$$
d_k=\alpha_k\|x_k-x_{k-1}\|+\lambda_k\|\eta_k\|.
$$

The first summability hypothesis gives summability of $\alpha_k\|x_k-x_{k-1}\|$, and the second gives summability of $\lambda_k\|\eta_k\|$. The lemma `Summable.add` states that the sum of two summable real sequences is summable, so $d$ is summable.

Next the proof defines the partial-sum sequence

$$
s_n=\sum_{k=0}^{n-1} d_k.
$$

Since $d$ is summable, the lemma `Summable.hasSum` gives that the finite sums of $d$ have total sum $\sum_{k=0}^{\infty}d_k$. Composing this with the map $n\mapsto\{0,\dots,n-1\}$ via `Filter.tendsto_finset_range` gives

$$
s_n\to \sum_{k=0}^{\infty}d_k.
$$

Thus the accumulated perturbation $s_n$ converges to a finite real number.

The proof then defines

$$
\phi_k=\|x_k-\bar x\|,\qquad \psi_k=\phi_k-s_k.
$$

The key monotonicity claim is $\psi_{k+1}\le \psi_k$. Indeed,

$$
\psi_{k+1}=\phi_{k+1}-s_{k+1}
=\phi_{k+1}-(s_k+d_k),
$$

while $\psi_k=\phi_k-s_k$. Thus $\psi_{k+1}\le\psi_k$ is equivalent to

$$
\phi_{k+1}\le \phi_k+d_k
=\phi_k+\alpha_k\|x_k-x_{k-1}\|+\lambda_k\|\eta_k\|,
$$

which is exactly the hypothesis `hineq`. In Lean, `Finset.sum_range_succ` rewrites $s_{k+1}=s_k+d_k$, and `linarith` finishes the arithmetic. The lemma `antitone_nat_of_succ_le` then converts the consecutive inequality $\psi_{k+1}\le\psi_k$ into the statement that $\psi$ is antitone, i.e. nonincreasing.

Because $s_n$ converges, its range is bounded above; the proof uses `bddAbove_range` and chooses a real number $B_u$ such that $s_k\le B_u$ for all $k$. Since $\phi_k=\|x_k-\bar x\|\ge0$, it follows that

$$
\psi_k=\phi_k-s_k\ge -B_u.
$$

So $\psi$ is bounded below. The lemma `tendsto_atTop_ciInf` states that an antitone sequence of real numbers which is bounded below converges to its infimum. The proof sets $\mathrm{psiInf}=\inf_n \psi_n$ and obtains

$$
\psi_k\to \mathrm{psiInf}.
$$

Since $s_k\to \sum_{k=0}^{\infty}d_k$, and since $\phi=\psi+s$, the addition rule for limits gives

$$
\phi_k=\|x_k-\bar x\|\to \mathrm{psiInf}+\sum_{k=0}^{\infty}d_k.
$$

This proves the first part of the conclusion: the distance sequence converges.

The proof then records that a convergent sequence is bounded above. Applying this to $\phi$, it chooses $M$ with

$$
\|x_k-\bar x\|=\phi_k\le M
$$

for every $k$.

Next it studies the term

$$
a_k=\alpha_k\|x_k-x_{k-1}\|.
$$

Since $\sum_k a_k$ is summable, the lemma `Summable.tendsto_atTop_zero` gives

$$
a_k\to0.
$$

Taking absolute values preserves the limit, so

$$
|a_k|\to0.
$$

A convergent sequence is bounded above, hence there is $B_1$ such that

$$
|a_k|\le B_1.
$$

Because

$$
|a_k|
=|\alpha_k\|x_k-x_{k-1}\||
=|\alpha_k|\,\|x_k-x_{k-1}\|,
$$

this gives the bound

$$
|\alpha_k|\,\|x_k-x_{k-1}\|\le B_1.
$$

Now the proof bounds $y_k$. Using the defining relation $y_k=x_k+\alpha_k(x_k-x_{k-1})$, the triangle inequality gives

$$
\|y_k\|
\le
\|x_k\|+\|\alpha_k(x_k-x_{k-1})\|.
$$

The norm of a scalar multiple is

$$
\|\alpha_k(x_k-x_{k-1})\|
=|\alpha_k|\,\|x_k-x_{k-1}\|.
$$

Also,

$$
x_k=(x_k-\bar x)+\bar x,
$$

so

$$
\|x_k\|\le \|x_k-\bar x\|+\|\bar x\|.
$$

Combining these inequalities with $\|x_k-\bar x\|\le M$ and
$|\alpha_k|\,\|x_k-x_{k-1}\|\le B_1$, the proof obtains

$$
\|y_k\|\le M+\|\bar x\|+B_1.
$$

It then sets

$$
C=M+\|\bar x\|+B_1.
$$

Thus $\|y_k\|\le C$ for all $k$.

To prove that the range of $y$ is bounded, the proof rewrites boundedness using `Metric.isBounded_iff`. In a metric space this says that a set is bounded exactly when there is a radius bounding all pairwise distances between points of the set. The proof chooses radius $2C$. For any two indices $i,j$,

$$
\mathrm{dist}(y_i,y_j)
=\|y_i-y_j\|
\le
\|y_i\|+\|y_j\|
\le
C+C=2C.
$$

The first inequality is the triangle inequality applied to $y_i+(-y_j)$. Therefore $\{y_k:k\in\mathbb N\}$ is bounded. This proves the second part of the conclusion.

Finally the proof handles the summability of

$$
u_k=\lambda_k\|\eta_k\|\,\|y_k\|.
$$

Since $\lambda_k\ge0$ and $\|\eta_k\|\ge0$, we have

$$
0\le \lambda_k\|\eta_k\|.
$$

Multiplying by the nonnegative number $\|y_k\|$ gives

$$
0\le \lambda_k\|\eta_k\|\,\|y_k\|.
$$

Also, from $\|y_k\|\le C$,

$$
\lambda_k\|\eta_k\|\,\|y_k\|
\le
C\bigl(\lambda_k\|\eta_k\|\bigr).
$$

The sequence $C(\lambda_k\|\eta_k\|)$ is summable because the original sequence $\lambda_k\|\eta_k\|$ is summable and multiplication by a constant preserves summability; in Lean this is `Summable.mul_left`. The comparison test `Summable.of_nonneg_of_le` then says that if $0\le u_k\le v_k$ for all $k$ and $\sum_k v_k$ converges, then $\sum_k u_k$ converges. Applying it with

$$
u_k=\lambda_k\|\eta_k\|\,\|y_k\|,
\qquad
v_k=C(\lambda_k\|\eta_k\|)
$$

proves

$$
\sum_{k=0}^{\infty}\lambda_k\|\eta_k\|\,\|y_k\|<\infty.
$$

This is the third part of the conclusion.

The final `exact ⟨h_goal1, h_range_y_bdd, h_summable_33⟩` simply packages the three proved statements into the conjunction required by the theorem. The reference declarations about set-valued operators are not used in this proof.

