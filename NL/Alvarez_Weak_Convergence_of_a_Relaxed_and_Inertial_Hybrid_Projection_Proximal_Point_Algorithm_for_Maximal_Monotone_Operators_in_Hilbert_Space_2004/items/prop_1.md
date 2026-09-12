## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/prop_1.lean`

## Lean statement
```lean
theorem proposition_2_5
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    (sigma : ℝ) (hsigma : 0 ≤ sigma ∧ sigma < 1)
    (alg : RelaxedInertialHPPA A lam alphaSeq rho sigma)
    (hlam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k)
    (halpha_mem : ∀ k : ℕ, 0 ≤ alphaSeq k ∧ alphaSeq k < 1)
    (halpha_mono : ∀ k : ℕ, alphaSeq k ≤ alphaSeq (k + 1))
    (hp_pos_alphaBar_R1_R2 : 0 < pCoeff R1 R2 alphaBar)
    (halphaBar_lt_one : alphaBar < 1)
    (halphaBar_bound : ∀ k : ℕ, alphaSeq k ≤ alphaBar)
    (hR1_pos : 0 < R1) (hR1_le : ∀ k : ℕ, R1 ≤ rho k)
    (hR2_lt_two : R2 < 2) (hR2_ge : ∀ k : ℕ, rho k ≤ R2)
    (hS : (SetValuedOperator.zeros A).Nonempty) :
    Summable (fun k : ℕ ↦ ‖alg.x k - alg.x (k - 1)‖ ^ 2) ∧
      ∃ xhat ∈ SetValuedOperator.zeros A,
        Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
          (𝓝 (toWeakSpace ℝ H xhat))
```

## Statement explanation
The declaration `proposition_2_5` is a theorem about a relaxed inertial hybrid projection/proximal point algorithm applied to a set-valued operator $A\colon H\rightrightarrows H$, where $H$ is the ambient real Hilbert space. The data of the statement include sequences

$$
\lambda,\ \alpha,\ \rho : \mathbb N \to \mathbb R
$$

(written `lam`, `alphaSeq`, and `rho`), real constants $\sigma,R_1,R_2,\bar\alpha$ (written `sigma`, `R1`, `R2`, and `alphaBar`), and an algorithm object

$$
\texttt{alg} : \texttt{RelaxedInertialHPPA}\ A\ \lambda\ \alpha\ \rho\ \sigma .
$$

The iterates used in the statement are $x_k := \texttt{alg.x k}$; the proof also uses the auxiliary sequence $v_k := \texttt{alg.v k}$.

The hypotheses are as follows. The operator $A$ is maximal monotone. The relaxation parameter satisfies

$$
0 \le \sigma < 1 .
$$

The sequence $\lambda$ has a positive lower bound, meaning there exists $\lambda_0\gt 0$ such that

$$
\lambda_0 \le \lambda_k
$$

for every $k\in\mathbb N$. The sequence $\alpha$ satisfies

$$
0 \le \alpha_k < 1
$$

for every $k$, and it is nondecreasing:

$$
\alpha_k \le \alpha_{k+1}.
$$

The hypothesis `hp_pos_alphaBar_R1_R2` says that the Lean quantity `pCoeff R1 R2 alphaBar`, a coefficient depending on $R_1,R_2,\bar\alpha$, is positive:

$$
\mathrm{pCoeff}(R_1,R_2,\bar\alpha)>0.
$$

The number $\bar\alpha$ satisfies

$$
\bar\alpha < 1
$$

and bounds the inertial sequence from above:

$$
\alpha_k \le \bar\alpha
$$

for every $k$. The sequence $\rho$ is bounded above and below by positive constants:

$$
R_1>0,\qquad R_1 \le \rho_k,\qquad R_2<2,\qquad \rho_k \le R_2
$$

for every $k$. Finally, $A$ has a zero:

$$
(\texttt{SetValuedOperator.zeros}\ A).\text{Nonempty}.
$$

By the definition of `zeros`, $`A.\texttt{zeros}=A.\texttt{inverse}\,0`$, and by `mem_zeros_iff`, membership $x\in A.\texttt{zeros}$ is equivalent to $0\in A x$. Thus the hypothesis says that there exists some $x$ with $0\in A x$.

The conclusion of the theorem is a conjunction. First,

```math
\mathrm{Summable}\left(k\mapsto \|x_k-x_{k-1}\|^2\right),
```

so the squared successive differences of the $x$-iterates are summable. Here Lean's natural-number subtraction is truncated, so for $k=0$ the term is $`\|x_0-x_0\|^2=0`$. Second, there exists a zero$\hat x$of$A$,

$$
\hat x \in \texttt{SetValuedOperator.zeros}\ A,
$$

such that the iterates converge weakly to $\hat x$:

```math
\texttt{Tendsto}\left(k\mapsto \texttt{toWeakSpace}\,\mathbb R\,H\,(x_k)\right)\ \texttt{atTop}\ \left(\mathcal N(\texttt{toWeakSpace}\,\mathbb R\,H\,\hat x)\right).
```

Equivalently, $x_k\rightharpoonup \hat x$ in the weak topology as $k\to\infty$. Thus the theorem asserts squared-summable movement of the iterates and weak convergence of the algorithm to a zero of the maximal monotone operator, under the stated parameter bounds and nonemptiness of the zero set.

## Lean proof
```lean
by
  by_cases hv_nonzero : ∀ k : ℕ, alg.v k ≠ 0
  · exact proposition_2_5_nonterminating A hA sigma hsigma alg hv_nonzero
      hlam_lower halpha_mem halpha_mono hp_pos_alphaBar_R1_R2 halphaBar_lt_one
      halphaBar_bound hR1_pos hR1_le hR2_lt_two hR2_ge hS
  · push Not at hv_nonzero
    rcases hv_nonzero with ⟨K, hvK⟩
    have htail := alg.finite_stop_if_zero K hvK
    have hsummable_sq :
        Summable (fun k : ℕ ↦ ‖alg.x k - alg.x (k - 1)‖ ^ 2) := by
      apply summable_of_hasFiniteSupport
      rw [Function.HasFiniteSupport]
      refine (Set.finite_lt_nat (K + 2)).subset ?_
      intro n hn
      by_contra hlt
      have hge : K + 2 ≤ n := le_of_not_gt hlt
      have hn_tail : K + 1 ≤ n := by omega
      have hprev_tail : K + 1 ≤ n - 1 := by omega
      have hxn := (htail n hn_tail).1
      have hxprev := (htail (n - 1) hprev_tail).1
      have hzero : ‖alg.x n - alg.x (n - 1)‖ ^ 2 = 0 := by
        simp [hxn, hxprev]
      exact hn hzero
    have halpha_summable :
        Summable fun k : ℕ ↦ alphaSeq k * ‖alg.x k - alg.x (k - 1)‖ ^ 2 := by
      refine hsummable_sq.of_nonneg_of_le ?hnonneg ?hle
      · intro k
        exact mul_nonneg (halpha_mem k).1 (sq_nonneg _)
      · intro k
        have ha_le_one : alphaSeq k ≤ 1 := le_of_lt (halpha_mem k).2
        exact mul_le_of_le_one_left (sq_nonneg _) ha_le_one
    let params : ParameterAssumptions alg.x :=
      { lam := lam
        alpha := alphaSeq
        rho := rho
        lam_lower := hlam_lower
        alpha_mem := halpha_mem
        alpha_upper := ⟨alphaBar, halphaBar_lt_one, halphaBar_bound⟩
        alpha_summable := halpha_summable
        rho_lower := ⟨R1, hR1_pos, hR1_le⟩
        rho_upper := ⟨R2, hR2_lt_two, hR2_ge⟩ }
    have hweak :
        ∃ xhat ∈ SetValuedOperator.zeros A,
          Tendsto (fun k : ℕ ↦ toWeakSpace ℝ H (alg.x k)) atTop
            (𝓝 (toWeakSpace ℝ H xhat)) := by
      rcases theorem_2_2 A hA sigma hsigma alg params rfl rfl rfl hS with
        ⟨_, _, _, hweak⟩
      exact hweak
    exact ⟨hsummable_sq, hweak⟩
```

## Proof explanation
The proof begins with a case split on whether the auxiliary sequence $v_k$ ever vanishes:

```math
\texttt{by\_cases}\ \ hv_{\text{nonzero}} : \forall k:\mathbb N,\ \texttt{alg.v k}\neq 0.
```

The two cases correspond to the nonterminating and terminating behavior of the algorithm.

In the first case, $v_k\neq 0$ for every $k$. The proof applies the previously established theorem `proposition_2_5_nonterminating`, passing to it exactly the same operator $A$, maximal monotonicity hypothesis, parameter $\sigma$, its bound $0\le \sigma\lt 1$, the algorithm object `alg`, the nonvanishing hypothesis, and all the remaining hypotheses of the current theorem. That theorem says, under precisely these assumptions plus $\forall k,\ v_k\neq0$, that

```math
\mathrm{Summable}\left(k\mapsto \|x_k-x_{k-1}\|^2\right)
```

and that there exists a zero $\hat x\in A.\texttt{zeros}$ to which $x_k$ converges weakly. Therefore `exact proposition_2_5_nonterminating ...` directly proves the desired conjunction in this case.

In the second case, the nonvanishing assertion is false. The tactic `push Not at hv_nonzero` pushes the negation through the universal quantifier, producing an existential statement. Then `rcases hv_nonzero with ⟨K, hvK⟩` extracts an index $K\in\mathbb N$ and a proof

$$
\texttt{alg.v K}=0.
$$

Thus at some finite index the auxiliary sequence vanishes.

The proof then invokes

```math
\texttt{htail} := \texttt{alg.finite\_stop\_if\_zero}\ K\ hvK.
```

The complete statement of this algorithm property is not present in the supplied context, but the proof uses only the following visible consequence: for every index $n$ with $K+1\le n$, the first projection `(htail n ...).1` gives an equality for `alg.x n` identifying it with a common tail value. Consequently, if both $n$ and $n-1$ lie in that tail, the two equalities identify $x_n$ and $x_{n-1}$, so their difference is zero. This is why the proof only needs the finite-stop statement for indices at least $K+1$.

Next the proof establishes

```math
\texttt{hsummable\_sq} :
\mathrm{Summable}\left(k\mapsto \|x_k-x_{k-1}\|^2\right).
```

It uses `summable_of_hasFiniteSupport`, which says that if a sequence has finite support, then it is summable. The tactic `rw [Function.HasFiniteSupport]` rewrites the goal into the form that the support of the sequence is contained in a finite set. The proof chooses the finite initial segment

```math
\{n\in\mathbb N:n<K+2\},
```

provided by `Set.finite_lt_nat (K + 2)`, and uses `refine ... .subset ?_` to reduce to showing that the support is contained in this finite set.

To prove this containment, the proof takes an arbitrary $n$ in the support of the sequence and argues by contradiction. If it were not true that $n\lt K+2$, then $K+2\le n$. The tactic `omega` derives the arithmetic consequences

$$
K+1\le n,\qquad K+1\le n-1.
$$

Thus both $n$ and $n-1$ are in the stationary tail. Applying `htail` to $n$ and to $n-1$ gives the two tail equalities `hxn` and `hxprev`, and `simp [hxn, hxprev]` reduces

```math
\|x_n-x_{n-1}\|^2
```

to $0$. Since $n$ was assumed to lie in the support, the sequence value at $n$ should be nonzero, but the proof has shown it is zero. The line `exact hn hzero` supplies that contradiction. Hence every support element satisfies $n\lt K+2$, so the support is finite. Therefore `hsummable_sq` holds.

The proof then derives a summability statement for the weighted sequence:

```math
\texttt{halpha\_summable} :
\mathrm{Summable}\left(k\mapsto \alpha_k\,\|x_k-x_{k-1}\|^2\right).
```

It uses `hsummable_sq.of_nonneg_of_le`, a comparison principle for summability: if a nonnegative sequence is pointwise bounded above by a summable nonnegative sequence, then it is summable. The nonnegativity proof uses the hypothesis $0\le \alpha_k$ from `halpha_mem k`, together with the fact that a squared norm is nonnegative. The comparison proof uses $\alpha_k\lt 1$ from `halpha_mem k`, hence $\alpha_k\le1$, and the fact that $`\|x_k-x_{k-1}\|^2\ge0`$. The lemma `mul_le_of_le_one_left` gives

```math
\alpha_k\|x_k-x_{k-1}\|^2 \le \|x_k-x_{k-1}\|^2.
```

Since the right-hand sequence was already proved summable, the weighted sequence is summable as well. This is needed to build the parameter package required by the next theorem.

The proof then constructs

$$
\texttt{params} : \texttt{ParameterAssumptions}\ \texttt{alg.x}.
$$

The fields are filled with the original sequences and hypotheses: `lam := lam`, `alpha := alphaSeq`, `rho := rho`; the lower bound for `lam` is `hlam_lower`; the membership hypothesis for `alpha` is `halpha_mem`; the upper-bound field for `alpha` is supplied by $\bar\alpha$, using `halphaBar_lt_one` and `halphaBar_bound`; the summability field is the just-proved `halpha_summable`; the lower and upper bounds for `rho` are supplied by $R_1$ and $R_2$, using `hR1_pos`, `hR1_le`, `hR2_lt_two`, and `hR2_ge`. Thus `params` records exactly the parameter assumptions on the algorithm iterates that the next theorem needs.

The proof then establishes the weak-convergence part. It applies `theorem_2_2` with the operator $A$, its maximal monotonicity, the relaxation parameter $\sigma$, its bound, the algorithm object `alg`, the freshly constructed `params`, the equalities `rfl`, `rfl`, `rfl`, and the nonemptiness hypothesis `hS`. The three `rfl` proofs are the equalities

$$
\lambda=\texttt{params.lam},\qquad
\alpha=\texttt{params.alpha},\qquad
\rho=\texttt{params.rho},
$$

which hold by definition because `params` was constructed with exactly these sequences.

The cited theorem `theorem_2_2` has four conclusions under those assumptions. First, for every zero $\bar x$ of $A$, the distance sequence $`\|x_k-\bar x\|`$ converges to some real limit. Second,

```math
\left\|x_{k+1}-\left(\rho_k^{-1}z_k+(1-\rho_k^{-1})y_k\right)\right\| \to 0.
```

Third,

```math
\|v_k\|\to 0.
```

Fourth, there exists $x^\star\in A.\texttt{zeros}$ such that

$$
x_k\rightharpoonup x^\star
$$

weakly. The proof destructs this fourfold conjunction with

```math
\texttt{rcases theorem\_2\_2 ... with } \langle \_, \_, \_, \texttt{hweak}\rangle,
```

discarding the first three conclusions and retaining exactly the weak-convergence conclusion as `hweak`. Therefore `hweak` is precisely

```math
\exists \hat x\in \texttt{SetValuedOperator.zeros}\ A,\quad
\texttt{Tendsto}\left(k\mapsto \texttt{toWeakSpace}\,\mathbb R\,H\,(x_k)\right)\ \texttt{atTop}\
\left(\mathcal N(\texttt{toWeakSpace}\,\mathbb R\,H\,\hat x)\right).
```

Finally, the proof combines the two established parts with

```math
\texttt{exact}\ \langle \texttt{hsummable\_sq}, \texttt{hweak}\rangle.
```

This constructs the required conjunction: squared summability of the successive differences and weak convergence of the iterates to a zero of the maximal monotone operator. In the terminating branch, the hypotheses not used for this final combination, such as the positivity of `pCoeff` and the monotonicity of $\alpha$, are not needed; the finite-stop property and the parameter bounds used to build `params` are enough.

