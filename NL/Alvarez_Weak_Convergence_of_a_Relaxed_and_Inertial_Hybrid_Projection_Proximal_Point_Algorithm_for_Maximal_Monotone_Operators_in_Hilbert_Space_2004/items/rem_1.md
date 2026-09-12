## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/rem_1.lean`

## Lean statement
```lean
theorem remark_1_finite_dimensional_convergence
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (x v y z : ℕ → H) (lam rho : ℕ → ℝ)
    (hS : (SetValuedOperator.zeros A).Nonempty)
    (hlam_sq_diverges : ¬ Summable fun k : ℕ ↦ (lam k) ^ 2)
    (hweighted : Summable fun k : ℕ ↦ (lam k) ^ 2 * ‖v k‖ ^ 2)
    (hfinite : FiniteDimensional ℝ H)
    (hdist :
      ∀ xbar ∈ SetValuedOperator.zeros A,
        ∃ l : ℝ, Tendsto (fun k : ℕ ↦ ‖x k - xbar‖) atTop (𝓝 l))
    (h_conn_25 :
      Tendsto
        (fun k : ℕ ↦
          ‖x (k + 1) - ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k)‖)
        atTop (𝓝 0))
    (h_incl_213 :
      ∀ k : ℕ,
        (rho k)⁻¹ • v k ∈ A ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k))
    (hR1_pos : ∃ R1 > (0 : ℝ), ∀ k : ℕ, R1 ≤ rho k)
    (hR2_lt_two : ∃ R2 : ℝ, R2 < 2 ∧ ∀ k : ℕ, rho k ≤ R2) :
    ∃ xstar ∈ SetValuedOperator.zeros A, Tendsto x atTop (𝓝 xstar)
```

## Statement explanation
The declaration is a finite-dimensional strong-convergence statement for a relaxed/inertial algorithm. The ambient space is $H$, which in this file is treated as the real Hilbert/normed space on which norms, scalar multiplication, weak convergence, and set-valued operators are considered. The operator $A$ is a set-valued operator from $H$ to $H$, and the hypothesis $hA$ says that $A$ is maximal monotone.

The sequences are $x,v,y,z:\mathbb N\to H$, and the scalar sequences are $\lambda,\rho:\mathbb N\to\mathbb R$. The set `SetValuedOperator.zeros A` is the zero set of $A$, namely the set of points $u$ such that $0\in A u$. Thus $hS$ says that $A$ has at least one zero.

The numerical hypotheses are:

- $hlam\_sq\_diverges$: the series $\sum_k (\lambda_k)^2$ is not summable.
- $hweighted$: the weighted series $\sum_k (\lambda_k)^2\|v_k\|^2$ is summable.
- $hfinite$: $H$ is finite-dimensional over $\mathbb R$.
- $hdist$: for every zero $\bar x\in \operatorname{zeros}(A)$, the real sequence $\|x_k-\bar x\|$ converges to some limit $l$.
- $hR1\_pos$: there exists $R_1>0$ such that $R_1\le \rho_k$ for all $k$.
- $hR2\_lt\_two$: there exists $R_2<2$ such that $\rho_k\le R_2$ for all $k$.

The algorithmic hypotheses involve the auxiliary sequence

$$
p_k=(\rho_k)^{-1}z_k+\bigl(1-(\rho_k)^{-1}\bigr)y_k.
$$

The condition $h\_conn\_25$ says

$$
\bigl\|x_{k+1}-p_k\bigr\|\to 0,
$$

so $x_{k+1}$ is asymptotically close to the relaxed combination $p_k$. The condition $h\_incl\_213$ says that for every $k$,

$$
(\rho_k)^{-1}v_k\in A(p_k).
$$

The conclusion is that there exists a zero $\hat x\in \operatorname{zeros}(A)$ such that

$$
x_k\to \hat x
$$

strongly in $H$. In other words, under maximal monotonicity, existence of a zero, finite dimensionality, the summability/divergence assumptions on $\lambda$, convergence of the distances to every zero, the asymptotic connection $x_{k+1}-p_k\to0$, the inclusion condition, and the lower/upper bounds on $\rho$, the sequence $x$ converges strongly to some zero of $A$. The displayed proof unpacks the upper bound $hR2\_lt\_two$ but does not use it later; the lower bound $R_1$ is used.

## Lean proof
```lean
by
  rcases hS with ⟨xbar0, hxbar0⟩
  rcases hdist xbar0 hxbar0 with ⟨l0, hl0⟩
  have hdiff_bdd : Bornology.IsBounded (Set.range (fun k : ℕ ↦ x k - xbar0)) :=
    bounded_range_of_tendsto_norm hl0
  have hx_bdd : Bornology.IsBounded (Set.range x) := by
    rcases isBounded_iff_forall_norm_le.mp hdiff_bdd with ⟨C, hC⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖xbar0‖, ?_⟩
    intro w hw
    rcases hw with ⟨k, rfl⟩
    calc
      ‖x k‖ = ‖(x k - xbar0) + xbar0‖ := by abel
      _ ≤ ‖x k - xbar0‖ + ‖xbar0‖ := norm_add_le _ _
      _ ≤ C + ‖xbar0‖ := by
        linarith [hC (x k - xbar0) ⟨k, rfl⟩]
  rcases residual_subsequence_of_weighted_summability hweighted hlam_sq_diverges with
    ⟨φ, hφ_strictMono, hφ_tendsto⟩
  letI : FiniteDimensional ℝ H := hfinite
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨R, hR⟩
  have h_sub_mem_ball (j : ℕ) : x (φ j + 1) ∈ Metric.closedBall (0 : H) R := by
    have hj := hR (x (φ j + 1)) ⟨φ j + 1, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hj
  rcases (ProperSpace.isCompact_closedBall (0 : H) R).tendsto_subseq h_sub_mem_ball with
    ⟨xhat, _hxhat_ball, ψ, hψ_strictMono, hψ_tendsto⟩
  have h_x_sub_tendsto :
      Tendsto (fun j : ℕ ↦ x (φ (ψ j) + 1)) atTop (𝓝 xhat) := by
    simpa [Function.comp] using hψ_tendsto
  have h_conn_25_vec :
      Tendsto
        (fun k : ℕ ↦
          x (k + 1) - ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k))
        atTop (𝓝 (0 : H)) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr h_conn_25
  let p (k : ℕ) : H := (rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k
  let k_seq (j : ℕ) : ℕ := φ (ψ j)
  have hk_seq_strictMono : StrictMono k_seq := hφ_strictMono.comp hψ_strictMono
  have hp_tendsto : Tendsto (fun j : ℕ ↦ p (k_seq j)) atTop (𝓝 xhat) := by
    have h1 : Tendsto (fun j : ℕ ↦ x (k_seq j + 1)) atTop (𝓝 xhat) := by
      simpa [k_seq] using h_x_sub_tendsto
    have h2 : Tendsto (fun j : ℕ ↦ x (k_seq j + 1) - p (k_seq j))
        atTop (𝓝 (0 : H)) := by
      simpa [p] using h_conn_25_vec.comp hk_seq_strictMono.tendsto_atTop
    have h := h1.sub h2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  rcases hR1_pos with ⟨R1, hR1_pos, hR1_le⟩
  rcases hR2_lt_two with ⟨R2, _hR2_lt_two, _hR2_ge⟩
  have hv_sub_tendsto : Tendsto (fun j : ℕ ↦ v (k_seq j)) atTop (𝓝 (0 : H)) := by
    simpa [k_seq] using hφ_tendsto.comp hψ_strictMono.tendsto_atTop
  have hv_scaled_tendsto :
      Tendsto (fun j : ℕ ↦ (rho (k_seq j))⁻¹ • v (k_seq j)) atTop (𝓝 (0 : H)) := by
    have hnorm_bound (j : ℕ) :
        ‖(rho (k_seq j))⁻¹ • v (k_seq j)‖ ≤ R1⁻¹ * ‖v (k_seq j)‖ := by
      have hρ_pos : 0 < rho (k_seq j) := lt_of_lt_of_le hR1_pos (hR1_le (k_seq j))
      have h_abs_inv : |(rho (k_seq j))⁻¹| ≤ R1⁻¹ := by
        rw [abs_of_pos (inv_pos.mpr hρ_pos)]
        exact (inv_le_inv₀ hρ_pos hR1_pos).mpr (hR1_le (k_seq j))
      calc
        ‖(rho (k_seq j))⁻¹ • v (k_seq j)‖ =
            |(rho (k_seq j))⁻¹| * ‖v (k_seq j)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ R1⁻¹ * ‖v (k_seq j)‖ :=
          mul_le_mul_of_nonneg_right h_abs_inv (norm_nonneg _)
    have hnorm_tendsto :
        Tendsto (fun j : ℕ ↦ ‖(rho (k_seq j))⁻¹ • v (k_seq j)‖) atTop (𝓝 0) := by
      have hprod :
          Tendsto (fun j : ℕ ↦ R1⁻¹ * ‖v (k_seq j)‖) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul hv_sub_tendsto.norm)
      exact squeeze_zero (fun j ↦ norm_nonneg _) hnorm_bound hprod
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm_tendsto
  have hp_weak_tendsto :
      Tendsto (fun j : ℕ ↦ toWeakSpace ℝ H (p (k_seq j))) atTop
        (𝓝 (toWeakSpace ℝ H xhat)) := by
    have hcont : Continuous (toWeakSpace ℝ H : H → WeakSpace ℝ H) := by
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using (toWeakSpaceCLM ℝ H).continuous
    exact (hcont.tendsto xhat).comp hp_tendsto
  have hxhat_zeros : xhat ∈ SetValuedOperator.zeros A := by
    rw [SetValuedOperator.mem_zeros_iff]
    exact weak_strong_closedness_maximal_monotone_graph A hA hp_weak_tendsto hv_scaled_tendsto
      (by
        intro j
        simpa [p] using h_incl_213 (k_seq j))
  rcases hdist xhat hxhat_zeros with ⟨lhat, hlhat⟩
  have hindex_tendsto : Tendsto (fun j : ℕ ↦ k_seq j + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun j : ℕ ↦ Nat.le_add_right (k_seq j) 1)
      hk_seq_strictMono.tendsto_atTop
  have hlhat_eq_zero : lhat = 0 := by
    have hsub_lhat :
        Tendsto (fun j : ℕ ↦ ‖x (k_seq j + 1) - xhat‖) atTop (𝓝 lhat) :=
      hlhat.comp hindex_tendsto
    have hsub_zero :
        Tendsto (fun j : ℕ ↦ ‖x (k_seq j + 1) - xhat‖) atTop (𝓝 0) := by
      have hdiff := (by
        simpa [k_seq] using h_x_sub_tendsto :
          Tendsto (fun j : ℕ ↦ x (k_seq j + 1)) atTop (𝓝 xhat))
      simpa using (hdiff.sub (tendsto_const_nhds (x := xhat))).norm
    exact tendsto_nhds_unique hsub_lhat hsub_zero
  have hnorm_zero : Tendsto (fun k : ℕ ↦ ‖x k - xhat‖) atTop (𝓝 0) := by
    simpa [hlhat_eq_zero] using hlhat
  have hx_tendsto : Tendsto x atTop (𝓝 xhat) := by
    have hdiff : Tendsto (fun k : ℕ ↦ x k - xhat) atTop (𝓝 (0 : H)) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm_zero
    simpa [sub_add_cancel] using hdiff.add (tendsto_const_nhds (x := xhat))
  exact ⟨xhat, hxhat_zeros, hx_tendsto⟩
```

## Proof explanation
The proof first extracts a zero $\bar x_0$ from $hS$ and uses the distance-convergence hypothesis for that zero. From $hdist\ \bar x_0\ hxbar_0$, it obtains a real number $l_0$ such that

$$
\|x_k-\bar x_0\|\to l_0.
$$

It then applies `bounded_range_of_tendsto_norm` to the sequence $x_k-\bar x_0$. That lemma says that if the norms of a sequence $a_k$ converge to a real number $l$, then the range of $a$ is bounded. Specialized here, since $\|x_k-\bar x_0\|\to l_0$, the set

$$
\{x_k-\bar x_0:k\in\mathbb N\}
$$

is bounded.

Next the proof shows that the original sequence $x$ is bounded. From `isBounded_iff_forall_norm_le.mp hdiff_bdd` it obtains a constant $C$ such that every $x_k-\bar x_0$ has norm at most $C$. For an arbitrary element $x_k$ it uses the vector identity

$$
x_k=(x_k-\bar x_0)+\bar x_0,
$$

rewritten by `abel`, and then the triangle inequality

$$
\|x_k\|
\le \|x_k-\bar x_0\|+\|\bar x_0\|
\le C+\|\bar x_0\|.
$$

The `linarith` step closes this arithmetic inequality using the bound $C$ on $\|x_k-\bar x_0\|$. Hence the range of $x$ is bounded, again via `isBounded_iff_forall_norm_le.mpr`.

The proof then applies `residual_subsequence_of_weighted_summability` to $hweighted$ and $hlam\_sq\_diverges$. The mathematical content of that lemma is: if

$$
\sum_k (\lambda_k)^2\|v_k\|^2<\infty
$$

but

$$
\sum_k (\lambda_k)^2
$$

diverges in the sense of not being summable, then there is a strictly increasing subsequence $\varphi:\mathbb N\to\mathbb N$ along which the residuals vanish:

$$
v_{\varphi(j)}\to 0.
$$

The proof therefore obtains a strictly increasing $\varphi$ and the convergence $v_{\varphi(j)}\to0$.

Because $hfinite$ says that $H$ is finite-dimensional over $\mathbb R$, the proof installs the instance `FiniteDimensional ℝ H` and then uses `FiniteDimensional.proper ℝ H` to get that $H$ is a proper space. In a proper space, closed balls are compact. From the boundedness of the range of $x$, the proof obtains $R$ with $\|x_k\|\le R$ for all $k$. Therefore every element $x_{\varphi(j)+1}$ lies in the closed ball `Metric.closedBall 0 R`. Since that closed ball is compact, `ProperSpace.isCompact_closedBall ... .tendsto_subseq` gives a subsequence $\psi$ of the indices and a point $\hat x$ such that

$$
x_{\varphi(\psi(j))+1}\to \hat x.
$$

This is the central finite-dimensional step: a bounded sequence in a finite-dimensional normed space has a convergent subsequence.

The proof then converts the norm convergence $h\_conn\_25$ into vector convergence. Using `tendsto_zero_iff_norm_tendsto_zero.mpr`, it obtains

$$
x_{k+1}-p_k\to 0
$$

in $H$. It defines

$$
k_j=\varphi(\psi(j)),
$$

which is strictly increasing because it is the composition of two strictly increasing subsequences. Since

$$
x_{k_j+1}\to \hat x
$$

and

$$
x_{k_j+1}-p_{k_j}\to 0,
$$

subtracting the second convergence from the first gives

$$
p_{k_j}\to \hat x.
$$

The proof also uses the subsequence $\varphi$ to get

$$
v_{k_j}=v_{\varphi(\psi(j))}\to 0.
$$

It then uses the lower bound $R_1\le \rho_k$ with $R_1>0$. For each $j$, the scalar $\rho_{k_j}$ is positive, and

$$
\left|(\rho_{k_j})^{-1}\right|
\le R_1^{-1}.
$$

Therefore

$$
\left\|(\rho_{k_j})^{-1}v_{k_j}\right\|
\le R_1^{-1}\|v_{k_j}\|.
$$

The right-hand side tends to $0$ because $v_{k_j}\to0$. By the squeeze theorem for nonnegative sequences, the norms of the scaled residuals tend to $0$. Hence

$$
(\rho_{k_j})^{-1}v_{k_j}\to 0.
$$

Next the proof records that $p_{k_j}\to\hat x$ weakly. The map $H\to \text{WeakSpace}\,\mathbb R\,H$ is continuous, so strong convergence $p_{k_j}\to\hat x$ implies weak convergence

$$
p_{k_j}\rightharpoonup \hat x.
$$

Now the proof applies the cited theorem `weak_strong_closedness_maximal_monotone_graph`. That theorem says that if $A$ is maximal monotone, if $xs_i\rightharpoonup x$ weakly, if $vs_i\to v$ strongly, and if $vs_i\in A(xs_i)$ for every $i$, then $v\in A x$. Here the proof takes

$$
xs_i=p_{k_i},\qquad vs_i=(\rho_{k_i})^{-1}v_{k_i},\qquad x=\hat x,\qquad v=0.
$$

The weak convergence of $xs_i$ to $\hat x$, the strong convergence of $vs_i$ to $0$, and the inclusion $h\_incl\_213(k_i)$ supply all hypotheses. The conclusion is

$$
0\in A(\hat x).
$$

By the definition of `SetValuedOperator.zeros`, this means

$$
\hat x\in \operatorname{zeros}(A).
$$

Now the distance-convergence hypothesis $hdist$ is applied to this zero $\hat x$, producing a real number $\hat l$ such that

$$
\|x_k-\hat x\|\to \hat l.
$$

The proof must show $\hat l=0$. Since $k_j+1\to\infty$, the subsequence $\|x_{k_j+1}-\hat x\|$ also converges to $\hat l$. But $x_{k_j+1}\to\hat x$, so the same subsequence converges to $0$. By uniqueness of limits in a Hausdorff space, `tendsto_nhds_unique` gives $\hat l=0$. Therefore

$$
\|x_k-\hat x\|\to 0.
$$

Finally, the proof converts this norm convergence into strong convergence of $x_k$ to $\hat x$. Using `tendsto_zero_iff_norm_tendsto_zero.mpr`, it obtains

$$
x_k-\hat x\to 0.
$$

Adding the constant sequence $\hat x$ gives

$$
(x_k-\hat x)+\hat x=x_k\to \hat x.
$$

Thus the proof concludes with the witness $\hat x$, the established fact that $\hat x\in \operatorname{zeros}(A)$, and the strong convergence $x_k\to\hat x$.

