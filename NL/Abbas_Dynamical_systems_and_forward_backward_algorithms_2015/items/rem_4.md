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
The theorem assumes that \(H\) is a type equipped with a normed additive commutative group structure, a real inner product space structure, and a complete-space structure, so \(H\) is a real Hilbert space. Let \(\Phi:H\to \mathrm{EReal}\) take values in the set of extended-real numbers strictly greater than the bottom element of \(\mathrm{EReal}\), and assume \(\Phi\) belongs to the class \(\mathrm{ERealFunction.gammaZero}(H)\), written \(h_\Phi\). Let \(S\subseteq H\), \(B:H\to H\), \(\mu\in\mathbb R\), \(h:\mathbb N\to\mathbb R\), and \(\beta,\delta,\varepsilon\in\mathbb R\). Let \(\mathrm{alg}\) be a variable-relaxation backward-forward algorithm for these data, with iterates \(\mathrm{alg}.y_k\).

The hypotheses are:

- \(0<\varepsilon\).
- For every \(k\), \(\varepsilon\le h_k\le \delta-\varepsilon\).
- \(0<\mu<2\beta\).
- \(\delta=\frac12+\min\{1,\beta/\mu\}\).
- \(S\) is nonempty.
- The map \(B\) is \(\beta\)-cocoercive on all of \(H\).
- For every \(z\in H\), \(z\in S\) if and only if \(-B(z)\) belongs to the subdifferential of \(\Phi\) at \(z\).

The conclusion is that there exists a point \(\bar y\in H\) such that the scaled proximity operator of \(\Phi\) with parameter \(\mu\), applied to \(\bar y\), lies in \(S\), and the sequence \(\mathrm{alg}.y_k\) converges weakly to \(\bar y\). In Lean notation, the weak convergence is expressed as convergence of \(k\mapsto \mathrm{toWeakSpace}_{\mathbb R,H}(\mathrm{alg}.y_k)\) to \(\mathrm{toWeakSpace}_{\mathbb R,H}(\bar y)\).

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
The proof begins by defining \(P:H\to H\) as the scaled proximity operator of \(\Phi\) with parameter \(\mu\), using the positivity proof \(h_{\mu}.1\). It then defines the forward-backward fixed-point operator

\[
T(y)=P(y)-\mu B(P(y)).
\]

The first intermediate lemma proves that \(P\) is firmly nonexpansive. This is obtained from the theorem that the proximity operator of a function in \(\mathrm{gammaZero}\) is firmly nonexpansive, applied after noticing that scaling \(\Phi\) by the positive number \(\mu\) preserves membership in \(\mathrm{gammaZero}\). The Lean command `simpa` simplifies this statement using the definition of \(P\) as the scaled proximity operator.

Next, the proof shows that \(T\) is \(1\)-Lipschitz, hence nonexpansive. This is done by composing two facts: firmly nonexpansive maps are \(1\)-Lipschitz, so \(P\) is \(1\)-Lipschitz, and the forward-step map \(x\mapsto x-\mu B(x)\) is \(1\)-Lipschitz under the hypotheses on \(\mu\), \(\beta\), and the \(\beta\)-cocoercivity of \(B\). The composition gives exactly the map \(T=P-\mu B\circ P\).

The proof then shows that the fixed-point set of \(T\) is nonempty. Since \(S\) is nonempty, choose \(z\in S\). The candidate fixed point is \(z-\mu B(z)\). Using the first direction of the solution equivalence, \(-B(z)\) is in the subdifferential of \(\Phi\) at \(z\). A lemma called `fixed_backward_forward_solution_implies_fixed_local` then gives the required fixed-point equation for \(z-\mu B(z)\). After unfolding the definitions of \(T\) and \(P\) with `change` and `dsimp`, the equation is rewritten using this lemma, proving that \(T(z-\mu B(z))=z-\mu B(z)\). Thus one obtains a fixed point \(p_0\) of \(T\).

A next lemma establishes the recurrence satisfied by the algorithm iterates: for every \(n\),

\[
\mathrm{alg}.y_{n+1}
=
(1-h_n)\mathrm{alg}.y_n
+
h_n\bigl(P(\mathrm{alg}.y_n)-\mu B(P(\mathrm{alg}.y_n))\bigr).
\]

This is proved by rewriting with the algorithm fields `alg.forward_step` and `alg.prox_step`.

The proof then invokes a local convergence lemma,
`variable_relaxation_distance_and_residual_tendsto_local`, with the fixed point \(p_0\), the recurrence equation, and the step-size and cocoercivity hypotheses. This lemma has two main consequences used later: the distance from the iterates to \(p_0\) converges, and the residual

\[
\mathrm{alg}.y_n-T(\mathrm{alg}.y_n)
\]

tends to \(0\).

Because the distance from \(\mathrm{alg}.y_n\) to \(p_0\) converges, the range of the sequence \(\mathrm{alg}.y_n\) is bounded. This is obtained by the lemma `bounded_range_of_convergent_distance_to_point`.

The proof also proves a distance-convergence property for every fixed point \(z\) of \(T\): for each such \(z\), the sequence \(\|\mathrm{alg}.y_n-z\|\) converges to some real number. This follows from the same local convergence lemma applied to \(z\).

The next major step is to show that every weak sequential cluster point of the sequence \(\mathrm{alg}.y_n\) is a fixed point of \(T\). Given such a cluster point \(z\), the proof extracts a subsequence index map \(\phi\) and the weak convergence of \(\mathrm{alg}.y_{\phi(n)}\) to \(z\). The residual along this subsequence also tends to \(0\), because it is the original residual convergence composed with the subsequence map. Using the boundedness of the iterates, the proof obtains a uniform bound for the distances \(\|\mathrm{alg}.y_{\phi(n)}-z\|\). A demiclosedness-type lemma,
`nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local`, is then applied to the nonexpansive map \(T\), the bounded weakly convergent subsequence, and its zero residual limit. This yields that \(z\) is a fixed point of \(T\).

Now the proof applies Opial’s lemma. The inputs are the nonempty fixed-point set of \(T\), the sequence \(\mathrm{alg}.y_n\), the convergence of distances to every fixed point, and the fact that every weak sequential cluster point is a fixed point. Opial’s lemma returns a point \(\bar y\) such that \(\bar y\) is a fixed point of \(T\) and the sequence \(\mathrm{alg}.y_n\) converges weakly to \(\bar y\).

Finally, the proof converts the fixed-point property of \(\bar y\) into the desired solution property. A lemma called `fixed_backward_forward_prox_mem_solution_local` is applied to \(\bar y\), using the solution characterization of \(S\). It shows that \(P(\bar y)\in S\). The witness \(\bar y\) is then returned together with the weak convergence statement. The weak convergence is exactly the second component of the conclusion. The proof uses `let`, `have`, `simpa`, `rw`, `rcases`, `obtain`, `exact`, and `calc`; no `linarith` step is needed.

