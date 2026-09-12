## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/lem_2.lean`

## Lean statement
```lean
theorem hpe_weakly_converges_to_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (A : HPEIterates H T)
    (hzero : ∃ xStar, (0 : H) ∈ T xStar) :
    ∃ xStar, (0 : H) ∈ T xStar ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (A.x k)) atTop
        (nhds (toWeakSpace ℝ H xStar))
```

## Statement explanation
The declaration `hpe_weakly_converges_to_zero` is a weak-convergence theorem for HPE iterates. Its ambient object is a type $H$ equipped with a normed additive commutative group structure, a real inner product space structure, and completeness; thus $H$ is a real Hilbert space. The operator $T : H \to \mathcal P(H)$ is a set-valued operator on $H$, and the hypothesis `hT` says that $T$ is maximal monotone. The object $A$ is an HPE iteration associated with $T$; the proof uses that it supplies sequences $A.x_k, A.y_k, A.v_k \in H$, scalar parameters $A.\varepsilon_k \in \mathbb R$, the nonnegativity facts $0 \le A.\varepsilon_k$, and the membership facts that $A.v_k$ lies in the $\varepsilon_k$-enlargement of $T$ at $A.y_k$. The hypothesis `hzero` says that $T$ has at least one zero, namely there exists $x_* \in H$ such that $0 \in T x_*$.

The conclusion is existential: there exists $x_* \in H$ such that $0 \in T x_*$ and the primal sequence $A.x_k$ converges weakly to $x_*$. The weak convergence is expressed as convergence in the weak space, namely

$$
\mathrm{toWeakSpace}_{\mathbb R,H}(A.x_k) \longrightarrow
\mathrm{toWeakSpace}_{\mathbb R,H}(x_*).
$$

In ordinary Hilbert-space language, this means that every weak sequential cluster point of $A.x_k$ is a zero of $T$, that there is at most one such weak sequential cluster point, and hence the whole sequence $A.x_k$ weakly converges to a zero of $T$. The statement does not assert strong convergence, nor does it assert that $T$ has a unique zero.

## Lean proof
```lean
by
  rcases hpe_asymptotics A hzero with ⟨hxBounded, hyx0, hε0, hvNorm0, _⟩
  have hcluster_zero : ∀ p : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H p) →
        (0 : H) ∈ T p := by
    intro p hp
    rcases hp with ⟨φ, hφmono, hφx⟩
    have hxφ : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (φ j))) atTop
        (nhds (toWeakSpace ℝ H p)) := by
      simpa [Function.comp] using hφx
    have hyφ := hpe_y_subseq_tendsto_weakly_of_x_subseq A hφmono hxφ hyx0
    have hvφ : Tendsto (fun j ↦ A.v (φ j)) atTop (nhds (0 : H)) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa [Function.comp] using hvNorm0.comp hφmono.tendsto_atTop
    have hεφ : Tendsto (fun j ↦ A.ε (φ j)) atTop (nhds 0) := by
      simpa [Function.comp] using hε0.comp hφmono.tendsto_atTop
    exact epsilon_enlargement_demiclosed hT (fun j ↦ A.y (φ j)) (fun j ↦ A.v (φ j))
      (fun j ↦ A.ε (φ j)) p 0 hyφ hvφ hεφ (fun j ↦ A.ε_nonneg (φ j))
      (fun j ↦ A.enlargement_mem (φ j))
  have hunique : ∀ p q : H,
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H q) →
          p = q := by
    intro p q hp hq
    have hp0 := hcluster_zero p hp
    have hq0 := hcluster_zero q hq
    rcases hpe_distance_converges A hp0 with ⟨Lp, _, hdistP⟩
    rcases hpe_distance_converges A hq0 with ⟨Lq, _, hdistQ⟩
    rcases hp with ⟨φ, hφmono, hφweak⟩
    rcases hq with ⟨ψ, hψmono, hψweak⟩
    have hdistPφ : Tendsto (fun j ↦ ‖A.x (φ j) - p‖) atTop (nhds Lp) := by
      simpa [Function.comp] using hdistP.comp hφmono.tendsto_atTop
    have hdistQφ : Tendsto (fun j ↦ ‖A.x (φ j) - q‖) atTop (nhds Lq) := by
      simpa [Function.comp] using hdistQ.comp hφmono.tendsto_atTop
    have hdistPψ : Tendsto (fun j ↦ ‖A.x (ψ j) - p‖) atTop (nhds Lp) := by
      simpa [Function.comp] using hdistP.comp hψmono.tendsto_atTop
    have hdistQψ : Tendsto (fun j ↦ ‖A.x (ψ j) - q‖) atTop (nhds Lq) := by
      simpa [Function.comp] using hdistQ.comp hψmono.tendsto_atTop
    have hφweak' : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (φ j))) atTop
        (nhds (toWeakSpace ℝ H p)) := by simpa [Function.comp] using hφweak
    have hψweak' : Tendsto (fun j ↦ toWeakSpace ℝ H (A.x (ψ j))) atTop
        (nhds (toWeakSpace ℝ H q)) := by simpa [Function.comp] using hψweak
    by_contra hpq
    have hqp : q ≠ p := Ne.symm hpq
    have hLq_gt_Lp := opial_lemma_paper (fun j ↦ A.x (φ j)) p q hφweak' hqp
    rw [hdistQφ.liminf_eq, hdistPφ.liminf_eq] at hLq_gt_Lp
    have hLp_gt_Lq := opial_lemma_paper (fun j ↦ A.x (ψ j)) q p hψweak' hpq
    rw [hdistPψ.liminf_eq, hdistQψ.liminf_eq] at hLp_gt_Lq
    linarith
  rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint A.x).2
      ⟨hxBounded, hunique⟩ with ⟨xStar, hxStarWeak⟩
  have hxStarCluster :
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (A.x k)) (toWeakSpace ℝ H xStar) :=
    ⟨id, strictMono_id, by simpa [Function.comp] using hxStarWeak⟩
  exact ⟨xStar, hcluster_zero xStar hxStarCluster, hxStarWeak⟩
```

## Proof explanation
First, the proof invokes `hpe_asymptotics A hzero` and destructs its five-part conclusion. This theorem says that if $A$ is an HPE iteration and $T$ has a zero, then the primal iterates are bounded,

$$
\mathrm{range}(A.x) \text{ is bounded},
$$

and the following asymptotic relations hold:

$$
\|A.y_k - A.x_k\| \to 0,\qquad
A.\varepsilon_k \to 0,\qquad
\|A.v_k\| \to 0,\qquad
\|A.c_k \cdot A.v_k\| \to 0.
$$

The proof keeps the first four facts as $hxBounded$, $hyx0$, $hε0$, and $hvNorm0$, and discards the last one. These facts are then used to identify weak cluster points and to control the auxiliary sequences.

Next, the proof establishes `hcluster_zero`, which states that for every $p \in H$, if $\mathrm{toWeakSpace}_{\mathbb R,H}(p)$ is a sequential cluster point of the sequence

$$
u_k = \mathrm{toWeakSpace}_{\mathbb R,H}(A.x_k),
$$

then $0 \in T p$. The definition of `IsSequentialClusterPt` says that there is a strictly increasing subsequence $\varphi : \mathbb N \to \mathbb N$ such that $u_{\varphi(j)}$ converges to $\mathrm{toWeakSpace}_{\mathbb R,H}(p)$. The proof introduces $p$ and the cluster-point hypothesis with `intro`, then destructs it with `rcases` into a strictly increasing $\varphi$ and the convergence

$$
A.x_{\varphi(j)} \rightharpoonup p.
$$

The `simpa [Function.comp]` step rewrites the composition $u \circ \varphi$ as the explicit sequence $j \mapsto \mathrm{toWeakSpace}_{\mathbb R,H}(A.x_{\varphi(j)})$.

The theorem `hpe_y_subseq_tendsto_weakly_of_x_subseq` is then applied to $A$, the strictly increasing sequence $\varphi$, the weak convergence $A.x_{\varphi(j)} \rightharpoonup p$, and the asymptotic relation $\|A.y_k - A.x_k\| \to 0$. Its conclusion is

$$
A.y_{\varphi(j)} \rightharpoonup p.
$$

Mathematically, this is a “same weak limit” statement: since $A.y_k$ differs from $A.x_k$ by a strongly null sequence, the auxiliary sequence $A.y_k$ has the same weak limit as $A.x_k$ along any subsequence.

The proof also needs strong convergence of the dual-type sequence $A.v_{\varphi(j)}$ to $0$. From `hvNorm0`, which gives $\|A.v_k\| \to 0$, the proof composes with the strictly increasing $\varphi$, obtaining $\|A.v_{\varphi(j)}\| \to 0$. The lemma `tendsto_zero_iff_norm_tendsto_zero.mpr` is used in the direction that says a normed-space sequence tends to zero whenever its norm tends to zero; hence

$$
A.v_{\varphi(j)} \to 0
$$

strongly in $H$. Similarly, composing $A.\varepsilon_k \to 0$ with $\varphi$ gives

$$
A.\varepsilon_{\varphi(j)} \to 0.
$$

The nonnegativity and enlargement-membership fields supply

$$
A.\varepsilon_{\varphi(j)} \ge 0,\qquad
A.v_{\varphi(j)} \in T^{A.\varepsilon_{\varphi(j)}}(A.y_{\varphi(j)}).
$$

At this point the proof applies `epsilon_enlargement_demiclosed`. This theorem says that if $T$ is maximal monotone, if $y_j$ converges weakly to $y_\infty$, if $v_j$ converges strongly to $v_\infty$, if $\varepsilon_j \to 0$, if $\varepsilon_j \ge 0$, and if $v_j \in T^{\varepsilon_j}(y_j)$ for all $j$, then $v_\infty \in T y_\infty$. In the current application, the roles are

$$
y_j = A.y_{\varphi(j)},\qquad
v_j = A.v_{\varphi(j)},\qquad
\varepsilon_j = A.\varepsilon_{\varphi(j)},\qquad
y_\infty = p,\qquad
v_\infty = 0.
$$

The hypotheses just established give $A.y_{\varphi(j)} \rightharpoonup p$, $A.v_{\varphi(j)} \to 0$, $A.\varepsilon_{\varphi(j)} \to 0$, nonnegativity, and the required enlargement membership. The conclusion is exactly $0 \in T p$. This proves `hcluster_zero`.

The proof then proves `hunique`: any two weak sequential cluster points of $A.x$ are equal. Suppose $p$ and $q$ are weak sequential cluster points. By `hcluster_zero`, both are zeros of $T$:

$$
0 \in T p,\qquad 0 \in T q.
$$

Now the theorem `hpe_distance_converges` is applied to $A$ and to the zero $p$, and then to $A$ and the zero $q$. This theorem says that if $x_*$ is a zero of $T$, then the distance sequence $\|A.x_k - x_*\|$ converges to some nonnegative real limit. Thus there exist $L_p, L_q \ge 0$ such that

$$
\|A.x_k - p\| \to L_p,\qquad
\|A.x_k - q\| \to L_q.
$$

The proof keeps these limits and the convergence statements as $hdistP$ and $hdistQ$.

From the cluster-point hypotheses for $p$ and $q$, the proof extracts strictly increasing subsequences $\varphi$ and $\psi$ such that

$$
A.x_{\varphi(j)} \rightharpoonup p,\qquad
A.x_{\psi(j)} \rightharpoonup q.
$$

Composing the distance convergences along these subsequences gives

$$
\|A.x_{\varphi(j)} - p\| \to L_p,\qquad
\|A.x_{\varphi(j)} - q\| \to L_q,
$$

and

$$
\|A.x_{\psi(j)} - p\| \to L_p,\qquad
\|A.x_{\psi(j)} - q\| \to L_q.
$$

The `simpa [Function.comp]` steps again convert composition notation into explicit subsequences.

To show $p=q$, the proof argues by contradiction using `by_contra`. If $p \ne q$, then also $q \ne p$ by `Ne.symm`. The theorem `opial_lemma_paper` is then applied twice. This theorem says that in a complete real inner product space, if a sequence $x_j$ converges weakly to $x_\infty$, and if $z \ne x_\infty$, then

$$
\liminf_{j} \|x_j - z\|
>
\liminf_{j} \|x_j - x_\infty\|.
$$

First it is applied to the subsequence $A.x_{\varphi(j)}$, whose weak limit is $p$, with $z=q$, using $q \ne p$. This yields

$$
\liminf_j \|A.x_{\varphi(j)} - q\|
>
\liminf_j \|A.x_{\varphi(j)} - p\|.
$$

Since the corresponding distance sequences converge to $L_q$ and $L_p$, the rewrites `rw [hdistQφ.liminf_eq, hdistPφ.liminf_eq]` replace the liminf values by their limits, giving

$$
L_q > L_p.
$$

Second, `opial_lemma_paper` is applied to $A.x_{\psi(j)}$, whose weak limit is $q$, with $z=p$, using $p \ne q$. This gives

$$
\liminf_j \|A.x_{\psi(j)} - p\|
>
\liminf_j \|A.x_{\psi(j)} - q\|.
$$

Rewriting with `hdistPψ.liminf_eq` and `hdistQψ.liminf_eq` gives

$$
L_p > L_q.
$$

The inequalities $L_q > L_p$ and $L_p > L_q$ are contradictory, and `linarith` closes the contradiction. Therefore $p=q$, proving `hunique`.

Finally, the proof applies `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` to the sequence $A.x$. This theorem states that a sequence in the Hilbert space is weakly convergent if and only if it is bounded and has at most one weak sequential cluster point. Using the reverse direction, the proof supplies the boundedness obtained from `hpe_asymptotics` and the uniqueness obtained as `hunique`. It obtains a point $x_*$ such that

$$
\mathrm{toWeakSpace}_{\mathbb R,H}(A.x_k)
\longrightarrow
\mathrm{toWeakSpace}_{\mathbb R,H}(x_*).
$$

The proof then observes that $x_*$ itself is a weak sequential cluster point: take the identity subsequence, which is strictly monotone by `strictMono_id`, and use the already-established weak convergence. The `simpa [Function.comp]` step removes the identity composition. Therefore `hcluster_zero xStar hxStarCluster` gives

$$
0 \in T x_*.
$$

Combining this zero property with the weak convergence just obtained, the final `exact` packages the witness and proves the stated existential conclusion.

