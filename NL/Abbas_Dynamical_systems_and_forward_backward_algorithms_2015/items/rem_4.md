## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_4.lean`

## Lean statement
```lean
theorem variable_relaxation_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (mu : ℝ) (h : ℕ → ℝ) (beta delta eps : ℝ)
    (alg : VariableRelaxationBackwardForwardAlgorithm Phi hPhi B mu h)
    (heps : 0 < eps) (hsteps : ∀ k, eps ≤ h k ∧ h k ≤ delta - eps)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hdelta : delta = 1 / 2 + min 1 (beta / mu))
    (hS : S.Nonempty)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    :
    ∃ ybar, ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩ ybar ∈ S ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (alg.y k)) atTop
        (nhds (toWeakSpace ℝ H ybar))
```

## Statement explanation
The theorem is set in a complete real inner product space $H$, i.e. a real Hilbert space. It is given an extended-real-valued function $\Phi$ on $H$, whose values are required to lie above the bottom element of $\mathbb{EReal}$, together with a proof `hPhi` that $\Phi$ belongs to the class $\Gamma_0(H)$, the proper convex lower semicontinuous extended-real functions. The set $S\subseteq H$ is a candidate solution set, $B:H\to H$ is a single-valued operator, $\mu$ is a positive scalar satisfying $\mu<2\beta$, and $h:\mathbb N\to\mathbb R$ is a variable relaxation sequence. The object `VariableRelaxationBackwardForwardAlgorithm Phi hPhi B mu h` packages the algorithm iterates and update equations. The real parameters $\delta$ and $\varepsilon$ satisfy $\varepsilon>0$, the inequalities

$$
\varepsilon\le h_k\le \delta-\varepsilon
$$

for every $k$, and

$$
\delta=\frac12+\min\left(1,\frac{\beta}{\mu}\right).
$$

The hypothesis `hB` says that $B$ is $\beta$-cocoercive on all of $H$. The hypothesis `hsolution` identifies $S$ exactly as the solution set of the monotone inclusion $0\in Bz+\partial\Phi(z)$: for every $z$,

$$
z\in S \iff -Bz\in \partial\Phi(z).
$$

The assumption `hS` says $S$ is nonempty.

The conclusion is that there exists a point $\bar y\in H$ such that

$$
\mathrm{Prox}_{\mu\Phi}(\bar y)\in S
$$

and the algorithm’s iterates $y_k$, where $y_k$ denotes `alg.y k`, converge weakly to $\bar y$:

$$
y_k \rightharpoonup \bar y.
$$

Thus the proximal image of the weak limit belongs to the solution set. The theorem does not assert that $\bar y$ itself belongs to $S$; it asserts that $\mathrm{Prox}_{\mu\Phi}(\bar y)$ does.

## Lean proof
```lean
by
  let P : H → H := ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
  let T : H → H := fun y ↦ P y - mu • B (P y)
  have hP : FirmlyNonexpansive P := by
    simpa [P, ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
        (ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, hmu.1⟩)
  have hTlip : LipschitzWith 1 T := by
    simpa [T, P, Function.comp_def] using
      (forward_step_lipschitz_one_local B beta mu hmu hB).comp
        (lipschitzWith_one_of_firmlyNonexpansive hP)
  have hC : (Function.fixedPoints T).Nonempty := by
    rcases hS with ⟨z, hz⟩
    refine ⟨z - mu • B z, ?_⟩
    have hzfix := fixed_backward_forward_solution_implies_fixed_local Phi hPhi B mu hmu.1 z
      ((hsolution z).1 hz)
    change T (z - mu • B z) = z - mu • B z
    dsimp [T, P]
    rw [hzfix]
  have hC₀ := hC
  obtain ⟨p₀, hp₀⟩ := hC₀
  have hupdate : ∀ n, alg.y (n + 1) = (1 - h n) • alg.y n + h n •
      (P (alg.y n) - mu • B (P (alg.y n))) := by
    intro n
    rw [alg.forward_step n, alg.prox_step n]
  have hseq₀ := variable_relaxation_distance_and_residual_tendsto_local
    P B beta mu delta eps h hmu heps hdelta hsteps hB hP alg.y hupdate p₀
    (by simpa [T] using hp₀)
  have hbounded : Bornology.IsBounded (Set.range alg.y) :=
    bounded_range_of_convergent_distance_to_point hseq₀.1
  have hdist : ∀ z ∈ Function.fixedPoints T, ∃ l : ℝ,
      Tendsto (fun n ↦ ‖alg.y n - z‖) atTop (nhds l) := by
    intro z hz
    exact (variable_relaxation_distance_and_residual_tendsto_local
      P B beta mu delta eps h hmu heps hdelta hsteps hB hP alg.y hupdate z
      (by simpa [T] using hz)).1
  have hcluster : ∀ z : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (alg.y n))
        (toWeakSpace ℝ H z) → z ∈ Function.fixedPoints T := by
    intro z hz
    rcases hz with ⟨phi, hphi, hphiweak⟩
    have hres : Tendsto (fun n ↦ alg.y (phi n) - T (alg.y (phi n))) atTop (nhds 0) := by
      simpa [T] using hseq₀.2.comp hphi.tendsto_atTop
    rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C, hCbound⟩
    have hsubbound : ∃ K : ℝ, ∀ n, ‖alg.y (phi n) - z‖ ≤ K := by
      refine ⟨C + ‖z‖, ?_⟩
      intro n
      calc
        ‖alg.y (phi n) - z‖ ≤ ‖alg.y (phi n)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ C + ‖z‖ := add_le_add (hCbound _ (Set.mem_range_self (phi n))) le_rfl
    have hphiweak' : Tendsto (fun n ↦ toWeakSpace ℝ H (alg.y (phi n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      simpa [Function.comp_def] using hphiweak
    exact nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local T hTlip
      (fun n ↦ alg.y (phi n)) z hphiweak' hres hsubbound
  rcases opial_lemma hC alg.y hdist hcluster with ⟨ybar, hybar, hyweak⟩
  exact ⟨ybar, fixed_backward_forward_prox_mem_solution_local Phi hPhi S B mu hmu.1
    hsolution ybar (by simpa [T, P] using hybar), hyweak⟩
```

## Proof explanation
The proof first defines two maps. It sets

$$
P=\mathrm{Prox}_{\mu\Phi},
$$

the scaled proximity operator of $\Phi$ with parameter $\mu$, and

$$
T(y)=P(y)-\mu B(P(y)).
$$

The map $T$ is the fixed-point map associated with the backward-forward step.

The first important fact is that $P$ is firmly nonexpansive. To see this, Lean uses `smul_mem_gammaZero`, which says that if $\Phi\in\Gamma_0(H)$ and $\mu>0$, then $\mu\Phi\in\Gamma_0(H)$. The proof `hmu.1` supplies $0<\mu$. Then it applies `proximityOperator_firmlyNonexpansive_of_mem_gammaZero`, which states that if $f\in\Gamma_0(H)$, then the proximity operator $\mathrm{Prox}_f$ is firmly nonexpansive. Specialized here, $\mathrm{Prox}_{\mu\Phi}$ is firmly nonexpansive, because $\mu\Phi\in\Gamma_0(H)$. In Hilbert-space form, firm nonexpansiveness of $P$ means

$$
\|P(x)-P(y)\|^2\le \langle P(x)-P(y),x-y\rangle
$$

for all $x,y\in H$. The Lean step `simpa [P, ERealFunction.scaledProximityOperator]` unfolds the definition of the scaled proximity operator so that the cited theorem applies exactly to $P$.

Next the proof shows that $T$ is $1$-Lipschitz. It uses `forward_step_lipschitz_one_local`, which says that if $0<\mu<2\beta$ and $B$ is $\beta$-cocoercive on all of $H$, then the forward map

$$
x\mapsto x-\mu B(x)
$$

is $1$-Lipschitz. The hypothesis `hmu` supplies $0<\mu<2\beta$, and `hB` supplies cocoercivity. Also, by `lipschitzWith_one_of_firmlyNonexpansive`, the firmly nonexpansive map $P$ is $1$-Lipschitz. The composition of the two $1$-Lipschitz maps gives the $1$-Lipschitz property of

$$
y\mapsto P(y)-\mu B(P(y))=T(y).
$$

This is exactly what the `simpa [T, P, Function.comp_def]` step verifies.

The proof then shows that the fixed-point set of $T$ is nonempty. Since $S$ is nonempty, it chooses a point $z\in S$. From `hsolution`, the membership $z\in S$ yields

$$
-Bz\in\partial\Phi(z).
$$

Now `fixed_backward_forward_solution_implies_fixed_local` applies: if $\Phi\in\Gamma_0(H)$, $\mu>0$, and $-Bz\in\partial\Phi(z)$, then

$$
P(z-\mu Bz)=z.
$$

Using this equality, the proof shows that $z-\mu Bz$ is a fixed point of $T$:

$$
T(z-\mu Bz)=P(z-\mu Bz)-\mu B(P(z-\mu Bz))=z-\mu Bz.
$$

The Lean commands `change`, `dsimp [T, P]`, and `rw [hzfix]` carry out this rewriting. Hence $\mathrm{Fix}(T)$ is nonempty. The proof stores this as `hC` and then obtains a point $p_0$ with $T(p_0)=p_0$.

Next, the proof derives the recurrence satisfied by the algorithm iterates. The algorithm fields `alg.forward_step` and `alg.prox_step`, rewritten by `rw`, give

$$
y_{n+1}=(1-h_n)y_n+h_n\bigl(P(y_n)-\mu B(P(y_n))\bigr).
$$

That is,

$$
y_{n+1}=(1-h_n)y_n+h_nT(y_n).
$$

The proof calls this `hupdate`.

The main convergence input is `variable_relaxation_distance_and_residual_tendsto_local`. Its content is: if $P$ is firmly nonexpansive, $B$ is $\beta$-cocoercive, $0<\mu<2\beta$, the relaxation parameters satisfy $\varepsilon\le h_k\le \delta-\varepsilon$ with $\delta=\frac12+\min(1,\beta/\mu)$, and the iterates satisfy

$$
x_{k+1}=(1-h_k)x_k+h_k\bigl(P(x_k)-\mu B(P(x_k))\bigr),
$$

then for every fixed point $p$ of $T(y)=P(y)-\mu B(P(y))$ one has both

$$
\exists l\in\mathbb R,\quad \|x_k-p\|\to l
$$

and

$$
x_k-T(x_k)\to 0.
$$

The proof applies this theorem with $x_k=y_k$ and with the fixed point $p_0$. The equality $T(p_0)=p_0$ is converted into $P(p_0)-\mu B(P(p_0))=p_0$ by `simpa [T]`. The resulting pair of conclusions is `hseq₀`: the distances $\|y_k-p_0\|$ converge, and the residuals $y_k-T(y_k)$ converge to $0$.

From the convergence of $\|y_k-p_0\|$, the proof uses `bounded_range_of_convergent_distance_to_point`, which says that if the distances from a sequence $x_k$ to some point $z$ converge, then the range of $x_k$ is bounded. Applied here, the set of all iterates $y_k$ is bounded. This is the fact `hbounded : Bornology.IsBounded (Set.range alg.y)`.

The proof then prepares the hypotheses of Opial’s lemma. First it shows that for every fixed point $z$ of $T$, the distances $\|y_k-z\|$ converge to some real limit. This again uses `variable_relaxation_distance_and_residual_tendsto_local`, now applied to the fixed point $z$, and then takes the first component of its conclusion. This produces `hdist`.

Second, the proof shows that every weak sequential cluster point of the sequence $y_k$ is a fixed point of $T$. Suppose $z$ is such a cluster point. By definition of `IsSequentialClusterPt`, there is a strictly increasing sequence $\varphi:\mathbb N\to\mathbb N$ such that

$$
y_{\varphi(n)}\rightharpoonup z
$$

weakly. The residual convergence $y_k-T(y_k)\to0$ for the full sequence implies, after composing with $\varphi$, that

$$
y_{\varphi(n)}-T(y_{\varphi(n)})\to0.
$$

The boundedness of the range of $y_k$ gives a constant $C$ such that $\|y_k\|\le C$ for all $k$. For the subsequence, the triangle inequality and the bound on the range give

$$
\|y_{\varphi(n)}-z\|\le \|y_{\varphi(n)}\|+\|z\|\le C+\|z\|.
$$

Thus the subsequence is bounded relative to $z$. Now the proof applies `nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local`. This theorem states that if $T$ is $1$-Lipschitz, $u_n$ converges weakly to $z$, $u_n-T(u_n)\to0$, and $u_n$ is bounded relative to $z$, then $T(z)=z$. Here $u_n=y_{\varphi(n)}$, so the theorem gives $T(z)=z$, i.e. $z\in\mathrm{Fix}(T)$. This is the cluster-point condition `hcluster`.

At this point all hypotheses of `opial_lemma` are available: the set $\mathrm{Fix}(T)$ is nonempty, for every point in it the distances $\|y_k-z\|$ converge, and every weak sequential cluster point of $y_k$ lies in it. The Opial lemma concludes that there exists $\bar y\in\mathrm{Fix}(T)$ such that

$$
y_k\rightharpoonup \bar y.
$$

Finally, the proof converts the fixed-point property of $\bar y$ into the required solution property. Since $\bar y\in\mathrm{Fix}(T)$, we have

$$
P(\bar y)-\mu B(P(\bar y))=\bar y.
$$

The theorem `fixed_backward_forward_prox_mem_solution_local` states that under the standing hypotheses on $\Phi$, $B$, $\mu$, and the solution characterization `hsolution`, any point $y$ satisfying $P(y)-\mu B(P(y))=y$ has $P(y)\in S$. Applying it to $y=\bar y$ gives

$$
P(\bar y)=\mathrm{Prox}_{\mu\Phi}(\bar y)\in S.
$$

Together with the weak convergence $y_k\rightharpoonup\bar y$, this proves the existential conclusion.

The Lean commands used along the way play the following roles. `let` introduces the abbreviations $P$ and $T$. `have` records intermediate mathematical facts. `simpa [...] using ...` applies a cited theorem after unfolding or simplifying definitions such as `P`, `T`, or the scaled proximity operator. `rcases` and `obtain` destruct existentials and conjunctions, for example to extract a point from the nonempty set $S$ or from the fixed-point set. `refine` supplies the required witness, such as the candidate fixed point $z-\mu Bz$. `change`, `dsimp`, and `rw` rewrite the goal into the desired fixed-point equation. `intro` introduces an arbitrary index or cluster point. The `calc` block proves the norm bound by chaining the triangle inequality with the earlier boundedness estimate. `exact` closes a goal by supplying the precise term or theorem application. No `linarith` step occurs in this proof.

