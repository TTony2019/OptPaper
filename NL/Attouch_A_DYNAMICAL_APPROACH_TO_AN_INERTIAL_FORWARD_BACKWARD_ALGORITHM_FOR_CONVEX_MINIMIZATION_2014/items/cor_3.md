## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_3.lean`

## Lean statement
```lean
theorem corollary11 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (u y : ℕ → H) (q : H) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hcompact : IsBoundedlyInfCompact Θ)
    (hweak : Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
      (nhds (toWeakSpace ℝ H q))) :
      Filter.Tendsto u Filter.atTop (nhds q) ∧ q ∈ Optimization.argminSet Θ
```

## Statement explanation
Let $H$ be a complete real inner product space. The functions in the statement are

$$
\phi,\Theta:H\to \mathrm{EReal},\qquad \psi:H\to\mathbb R,\qquad
\mathrm{gradPsi}:H\to H,
$$

where $\mathrm{EReal}=\mathbb R\cup\{-\infty,+\infty\}$ is the extended real line. The real parameters are $a,b,\lambda,L_{\psi}\in\mathbb R$. The sequences are $u,y:\mathbb N\to H$, and $q\in H$. The hypotheses are:

- `hH : IFBHypothesis phi Theta psi gradPsi a b lam Lpsi`, the standing hypotheses of the inertial forward-backward setting relating $\phi,\Theta,\psi,\mathrm{gradPsi}$ and the parameters. In the proof, the used parts are `hH.theta_bounded_below`, `hH.phi_proper.2`, and `hH.theta_eq`: a lower bound for $\Theta$, a point at which $\phi$ is not $+\infty$, and an identity rewriting $\Theta$ in terms of $\phi$ and $\psi$.
- `hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y`, saying that $(u,y)$ is an inertial forward-backward trajectory for those data.
- `hcompact : IsBoundedlyInfCompact Θ`, a compactness assumption on $\Theta$. In the proof it is used exactly to assert that for every real $r$ and every $R>0$, the closure of

  $$
  \{v\in H:\Theta(v)\le r\ \text{and}\ \|v\|\le R\}
  $$

  is compact.
- `hweak : Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop (nhds (toWeakSpace ℝ H q))`, meaning that $u_k$ converges to $q$ in the weak topology of $H$, i.e. $u_k\rightharpoonup q$.

The conclusion is the conjunction

$$
\Bigl(u_k\to q\ \text{in the norm topology of }H\Bigr)
\quad\land\quad
\Bigl(q\in\mathrm{argminSet}\Theta\Bigr).
$$

The set $\mathrm{argminSet}\Theta$ is defined by

$$
\mathrm{argminSet}\Theta
=
\{x\in H:\forall y\in H,\ \Theta(x)\le \Theta(y)\}.
$$

Thus the theorem says: under the inertial forward-backward hypotheses, if $\Theta$ is boundedly inf-compact and the iterates $u_k$ converge weakly to $q$, then they actually converge strongly to $q$, and $q$ is a global minimizer of $\Theta$.

## Lean proof
```lean
by
  rcases proposition6 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨hTheta, hclusterMin, _⟩
  have hqcluster : IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k))
      (toWeakSpace ℝ H q) :=
    ⟨id, strictMono_id, by simpa [Function.comp_def] using hweak⟩
  have hqmin : q ∈ Optimization.argminSet Θ := hclusterMin q hqcluster
  rcases (bounded_range_of_tendsto_weakly hweak).exists_pos_norm_le with ⟨R, hRpos, hR⟩
  have hLbot : sInf (Set.range Θ) ≠ (⊥ : EReal) := by
    rcases hH.theta_bounded_below with ⟨m, hm⟩
    have hml : (m : EReal) ≤ sInf (Set.range Θ) := by
      apply le_sInf
      rintro z ⟨x, rfl⟩
      exact hm x
    intro hbot
    rw [hbot] at hml
    exact (not_le_of_gt (EReal.bot_lt_coe m)) hml
  have hTheta_q_top : Θ q ≠ (⊤ : EReal) := by
    rcases hH.phi_proper.2 with ⟨x, hx⟩
    have hqx : Θ q ≤ Θ x := by
      rw [Optimization.mem_argminSet_iff_eq_sInf] at hqmin
      rw [hqmin]
      exact sInf_le (Set.mem_range_self x)
    have hxtop : Θ x < (⊤ : EReal) := by
      rw [hH.theta_eq]
      exact EReal.add_lt_top (lt_top_iff_ne_top.mp hx) (EReal.coe_ne_top _)
    exact ne_of_lt (lt_of_le_of_lt hqx hxtop)
  have hLtop : sInf (Set.range Θ) ≠ (⊤ : EReal) := by
    intro htop
    have hle : (⊤ : EReal) ≤ Θ q := by
      rw [← htop]
      exact sInf_le (Set.mem_range_self q)
    exact hTheta_q_top (top_unique hle)
  let r : ℝ := (sInf (Set.range Θ)).toReal + 1
  have hLr : sInf (Set.range Θ) < (r : EReal) := by
    rw [← EReal.coe_toReal hLtop hLbot]
    exact_mod_cast lt_add_one (sInf (Set.range Θ)).toReal
  have hevent : ∀ᶠ k in Filter.atTop, Θ (u k) < (r : EReal) :=
    hTheta.eventually_lt_const hLr
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  let A : Set H := {v | Θ v ≤ (r : EReal) ∧ ‖v‖ ≤ R}
  let K : Set H := closure A
  have hKcompact : IsCompact K := by
    dsimp [K, A]
    exact hcompact r R hRpos
  have hvK : ∀ n : ℕ, u (N + n) ∈ K := by
    intro n
    apply subset_closure
    constructor
    · exact le_of_lt (hN (N + n) (Nat.le_add_right N n))
    · exact hR (u (N + n)) (Set.mem_range_self _)
  have hunique : ∀ p : H, IsSequentialClusterPt (fun n ↦ u (N + n)) p → p = q := by
    intro p hp
    rcases hp.exists_subseq_tendsto with ⟨f, hf, hfp⟩
    have hindex : Filter.Tendsto (fun n ↦ N + f n) Filter.atTop Filter.atTop := by
      simpa [Nat.add_comm] using (Filter.tendsto_add_atTop_nat N).comp hf.tendsto_atTop
    have hweakq : Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (u (N + f n)))
        Filter.atTop (nhds (toWeakSpace ℝ H q)) := hweak.comp hindex
    have hweakp : Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (u (N + f n)))
        Filter.atTop (nhds (toWeakSpace ℝ H p)) := by
      simpa [Function.comp_def, toWeakSpaceCLM_eq_toWeakSpace] using
        (toWeakSpaceCLM ℝ H).continuous.tendsto p |>.comp hfp
    apply (toWeakSpace ℝ H).injective
    exact tendsto_nhds_unique hweakp hweakq
  have htail : Filter.Tendsto (fun n ↦ u (N + n)) Filter.atTop (nhds q) :=
    tendsto_of_unique_sequential_cluster_point hKcompact.isSeqCompact hvK hunique
  have hstrong : Filter.Tendsto u Filter.atTop (nhds q) := by
    apply (Filter.tendsto_add_atTop_iff_nat N).mp
    simpa [Nat.add_comm] using htail
  exact ⟨hstrong, hqmin⟩
```

## Proof explanation
The proof first invokes `proposition6` with the same data $\phi,\Theta,\psi,\mathrm{gradPsi},a,b,\lambda,L_{\psi},u,y$ and the hypotheses `hH` and `hIFB`. That proposition gives three facts. The first is

$$
\Theta(u_k)\longrightarrow \inf_{x\in H}\Theta(x)
\quad\text{in }\mathrm{EReal}.
$$

The proof names this `hTheta`. The second is that every weak sequential cluster point of $u_k$ is a minimizer of $\Theta$:

$$
\forall r\in H,\quad
\mathrm{IsSequentialClusterPt}\bigl(k\mapsto \mathrm{toWeakSpace}(u_k),\mathrm{toWeakSpace}(r)\bigr)
\implies r\in\mathrm{argminSet}\Theta .
$$

The proof names this `hclusterMin`. The third conclusion of `proposition6` is discarded with the wildcard in the `rcases`. Here `IsSequentialClusterPt(u,x)` means that there exists a strictly increasing subsequence $u_{\varphi(n)}$ converging to $x$.

Because `hweak` itself says that the whole weak-space sequence $\mathrm{toWeakSpace}(u_k)$ converges to $\mathrm{toWeakSpace}(q)$, the point $q$ is a weak sequential cluster point: one may take the subsequence to be the identity map, which is strictly monotone. The proof records this as `hqcluster`, and then applies `hclusterMin` to obtain

$$
q\in\mathrm{argminSet}\Theta .
$$

This is the first half of the final conclusion.

Next, the weak convergence hypothesis is used with the lemma `bounded_range_of_tendsto_weakly`. That lemma states that if a sequence converges weakly to a point, then its range is bounded. Applied to $u_k\rightharpoonup q$, it gives that $\{u_k:k\in\mathbb N\}$ is bounded. The proof extracts a positive radius $R>0$ such that

$$
\forall v\in\{u_k:k\in\mathbb N\},\qquad \|v\|\le R.
$$

This will later keep the relevant tail of the sequence inside a closed ball.

The proof then shows that the extended-real value $\inf_{x\in H}\Theta(x)$ is neither $-\infty$ nor $+\infty$. First, from `hH.theta_bounded_below` it obtains a real number $m$ such that

$$
(m:\mathrm{EReal})\le \Theta(x)\quad\text{for all }x\in H.
$$

Therefore $(m:\mathrm{EReal})$ is a lower bound for the range of $\Theta$, so

$$
(m:\mathrm{EReal})\le \inf_{x\in H}\Theta(x).
$$

If the infimum were $-\infty$, this would give $(m:\mathrm{EReal})\le -\infty$, which is impossible because $-\infty<(m:\mathrm{EReal})$. Hence the infimum is not $-\infty$. This is the step `hLbot`.

Next the proof shows that $\Theta(q)\ne+\infty$. From `hH.phi_proper.2` it chooses a point $x$ with $\phi(x)<+\infty$. Since $q$ is a minimizer of $\Theta$, the lemma `mem_argminSet_iff_eq_sInf` gives

$$
\Theta(q)=\inf_{y\in H}\Theta(y).
$$

Consequently $\Theta(q)\le \Theta(x)$. The equality `hH.theta_eq` rewrites $\Theta(x)$ in terms of $\phi(x)$ and the real value $\psi(x)$, and because $\phi(x)<+\infty$ while $(\psi(x):\mathrm{EReal})$ is not $+\infty$, the extended-real sum is still strictly below $+\infty$. Thus $\Theta(x)<+\infty$, and since $\Theta(q)\le \Theta(x)$, also $\Theta(q)<+\infty$. Hence $\Theta(q)\ne+\infty$. This is `hTheta_q_top`.

Using that, the proof shows that the infimum itself is not $+\infty$. If it were $+\infty$, then the defining inequality $\inf\Theta\le \Theta(q)$ would force $+\infty\le \Theta(q)$, hence $\Theta(q)=+\infty$, contradicting $\Theta(q)\ne+\infty$. Therefore the infimum is not $+\infty$. This is `hLtop`.

Since the infimum is neither $-\infty$ nor $+\infty$, it is a finite extended real number. The proof defines

$$
r=\bigl(\inf\Theta\bigr)_{\mathrm{toReal}}+1.
$$

The lemma `EReal.coe_toReal` identifies the finite extended real $\inf\Theta$ with the coercion of its real part, so the inequality $a<a+1$ for real numbers gives

$$
\inf\Theta < (r:\mathrm{EReal}).
$$

Because $\Theta(u_k)\to\inf\Theta$, the convergence is eventually below any larger threshold; hence `eventually_lt_const` gives

$$
\forall^{\mathrm{eventually}} k,\quad \Theta(u_k)<(r:\mathrm{EReal}).
$$

Unwrapping “eventually at top” gives an index $N$ such that

$$
\forall k\ge N,\quad \Theta(u_k)<r.
$$

Now the proof defines

$$
A=\{v\in H:\Theta(v)\le r\ \text{and}\ \|v\|\le R\},
\qquad
K=\overline A .
$$

The boundedly inf-compactness hypothesis `hcompact`, applied to $r$ and $R>0$, gives that $K$ is compact. For each $n$, the index $N+n$ satisfies $N+n\ge N$, so $\Theta(u_{N+n})<r$, hence $\Theta(u_{N+n})\le r$. Also $\|u_{N+n}\|\le R$ by the boundedness of the range of $u$. Therefore $u_{N+n}\in A\subseteq K$. Thus the tail sequence $n\mapsto u_{N+n}$ lies entirely in the compact set $K$.

The proof next proves that this tail has a unique sequential cluster point, namely $q$. Let $p$ be any sequential cluster point of $n\mapsto u_{N+n}$. By the definition of sequential cluster point, there is a strictly increasing map $f:\mathbb N\to\mathbb N$ such that

$$
u_{N+f(n)}\to p
$$

in the norm topology. Since $f(n)\to\infty$, also $N+f(n)\to\infty$. Composing the weak convergence $u_k\rightharpoonup q$ with the index map $n\mapsto N+f(n)$ gives

$$
\mathrm{toWeakSpace}(u_{N+f(n)})\to \mathrm{toWeakSpace}(q).
$$

On the other hand, the canonical map from $H$ to its weak topology is continuous, so the strong convergence $u_{N+f(n)}\to p$ implies weak convergence

$$
\mathrm{toWeakSpace}(u_{N+f(n)})\to \mathrm{toWeakSpace}(p).
$$

Limits in the weak topology are unique, so

$$
\mathrm{toWeakSpace}(p)=\mathrm{toWeakSpace}(q).
$$

The canonical map to the weak space is injective, hence $p=q$. Therefore $q$ is the only sequential cluster point of the tail $n\mapsto u_{N+n}$.

At this point the proof applies `tendsto_of_unique_sequential_cluster_point`. That theorem says that if $C$ is sequentially compact, a sequence lies in $C$, and every sequential cluster point of the sequence equals a fixed point $x$, then the sequence converges to $x$. Here $C=K$ is compact, hence sequentially compact; the tail $u_{N+n}$ lies in $K$; and its only sequential cluster point is $q$. Therefore

$$
u_{N+n}\to q
$$

in the norm topology.

Finally, convergence of the shifted sequence $n\mapsto u_{N+n}$ to $q$ is equivalent to convergence of the original sequence $k\mapsto u_k$ to $q$. The proof uses `Filter.tendsto_add_atTop_iff_nat` for this equivalence and then simplifies the index arithmetic. Thus

$$
u_k\to q
$$

strongly. Together with the earlier minimizer property $q\in\mathrm{argminSet}\Theta$, this proves the theorem.

The Lean tactics reflect these mathematical steps: `rcases` destructs the conjunction from `proposition6` and the eventual-at-top statement; `intro` introduces a hypothetical point or assumption; `rw` rewrites with equalities such as the minimizer characterization, the lower-bound contradiction, and `hH.theta_eq`; `apply` reduces a goal to a sufficient subgoal; `simpa` handles definitional simplifications such as the identity subsequence and the weak-space embedding; `exact` closes the goals with the established inequality or convergence; `let` introduces the abbreviations $r$, $A$, and $K$; `dsimp` unfolds those local abbreviations before applying `hcompact`; and `exact_mod_cast` converts the real inequality $a<a+1$ to the corresponding extended-real inequality. No use of `linarith` occurs in this proof.

