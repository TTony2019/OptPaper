## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/algo_4.lean`

## Lean statement
```lean
theorem relaxed_forward_backward_stepsize_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (mu h beta : ℝ)
    (alg : RelaxedForwardBackwardAlgorithm Phi hPhi B mu h)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hh : 0 < h ∧ h ≤ 1)
    (hS : S.Nonempty)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∃ z ∈ S, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (alg.x k)) Filter.atTop
      (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The statement is a weak convergence theorem for a relaxed forward-backward algorithm in a real Hilbert space. Let \(H\) be a type equipped with a normed additive commutative group structure, a real inner product space structure, and completeness, so \(H\) is a complete real inner product space. Let  
\[
\Phi:H\to \mathrm{Set.Ioi}(\bot:\mathrm{EReal})
\]
be an extended-real-valued function taking values greater than the bottom element, and assume \(\Phi\in\mathrm{ERealFunction.gammaZero}\,H\), a class of functions used for proximity operators.

Let \(B:H\to H\) be an operator, \(S\subseteq H\) a set of solutions, and \(\mu,h,\beta:\mathbb R\) real parameters. The object \(\mathrm{alg}\) is a relaxed forward-backward algorithm for \(\Phi\), \(B\), step size \(\mu\), and relaxation parameter \(h\). The proof uses its sequence of iterates \(\mathrm{alg.x}\) and its update field \(\mathrm{alg.update}\).

The assumptions are:

- \(0<\mu<2\beta\),
- \(0<h\le 1\),
- \(S\) is nonempty,
- \(B\) is \(\beta\)-cocoercive on the whole space \(H\),
- for every \(z\), \(z\in S\) if and only if \(-Bz\) belongs to the subdifferential of \(\Phi\) at \(z\).

The conclusion is that there exists some \(z\in S\) such that the sequence
\[
k\mapsto \mathrm{toWeakSpace}\,\mathbb R\,H\,(\mathrm{alg.x}\,k)
\]
tends to
\[
\mathrm{toWeakSpace}\,\mathbb R\,H\,z
\]
in the weak topology. Thus the algorithm iterates converge weakly to a point in \(S\).

## Lean proof
```lean
by
  let T : H → H := fun z ↦ ERealFunction.scaledProximityOperator Phi hPhi
    ⟨mu, alg.mu_pos⟩ (z - mu • B z)
  have hfixed : Function.fixedPoints T = S := by
    ext z
    simp only [Function.mem_fixedPoints, Function.IsFixedPt]
    constructor
    · intro hz
      exact (hsolution z).2 (scaled_forward_backward_fixed_implies_solution Phi hPhi B mu
        alg.mu_pos z (by simpa [T] using hz))
    · intro hz
      exact scaled_forward_backward_solution_implies_fixed Phi hPhi B mu alg.mu_pos z
        ((hsolution z).1 hz)
  have hP : FirmlyNonexpansive
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩) := by
    have hg := ERealFunction.smul_mem_gammaZero Phi hPhi ⟨mu, alg.mu_pos⟩
    simpa [ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero hg
  have hF : LipschitzWith 1 (fun z : H ↦ z - mu • B z) :=
    forward_step_lipschitz_one B beta mu hmu hB
  have hTlip : LipschitzWith 1 T := by
    have hPlip := lipschitzWith_one_of_firmlyNonexpansive hP
    simpa [T, Function.comp_def] using hPlip.comp hF
  have hC : (Function.fixedPoints T).Nonempty := by rwa [hfixed]
  obtain ⟨p₀, hp₀⟩ := hC
  have hp₀eq : T p₀ = p₀ := hp₀
  have hseq₀ := forward_backward_distance_and_residual_tendsto
    (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩) B beta mu h
    hmu hh hB hP alg.x alg.update p₀ (by simpa [T] using hp₀eq)
  have hbounded : Bornology.IsBounded (Set.range alg.x) :=
    bounded_range_of_convergent_distance_to_point hseq₀.1
  have hdist : ∀ z ∈ Function.fixedPoints T, ∃ l : ℝ,
      Filter.Tendsto (fun n ↦ ‖alg.x n - z‖) Filter.atTop (nhds l) := by
    intro z hz
    exact (forward_backward_distance_and_residual_tendsto
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, alg.mu_pos⟩) B beta mu h
      hmu hh hB hP alg.x alg.update z (by simpa [T] using hz)).1
  have hcluster : ∀ z : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (alg.x n))
        (toWeakSpace ℝ H z) → z ∈ Function.fixedPoints T := by
    intro z hz
    rcases hz with ⟨phi, hphi, hphiweak⟩
    have hres : Filter.Tendsto (fun n ↦ alg.x (phi n) - T (alg.x (phi n)))
        Filter.atTop (nhds 0) := by
      simpa [T] using hseq₀.2.comp hphi.tendsto_atTop
    rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C, hCbound⟩
    have hsubbound : ∃ K : ℝ, ∀ n, ‖alg.x (phi n) - z‖ ≤ K := by
      refine ⟨C + ‖z‖, ?_⟩
      intro n
      calc
        ‖alg.x (phi n) - z‖ ≤ ‖alg.x (phi n)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ C + ‖z‖ := add_le_add (hCbound _ (Set.mem_range_self (phi n))) le_rfl
    have hphiweak' : Filter.Tendsto
        (fun n ↦ toWeakSpace ℝ H (alg.x (phi n))) Filter.atTop
        (nhds (toWeakSpace ℝ H z)) := by
      simpa [Function.comp_def] using hphiweak
    have hfix : T z = z :=
      nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero T hTlip
        (fun n ↦ alg.x (phi n)) z hphiweak' hres hsubbound
    exact hfix
  rcases opial_lemma ⟨p₀, hp₀⟩ alg.x hdist hcluster with ⟨z, hz, hlim⟩
  exact ⟨z, by rwa [← hfixed], hlim⟩
```

## Proof explanation
The proof starts by defining an operator
\[
T:H\to H,\qquad T(z)=\operatorname{prox}_{\mu\Phi}(z-\mu Bz),
\]
where \(\operatorname{prox}_{\mu\Phi}\) is the scaled proximity operator of \(\Phi\) with parameter \(\mu\).

The first major step proves that the fixed points of \(T\) are exactly the solution set \(S\). This is done by proving
\[
\operatorname{Fix}(T)=S
\]
using extension and simplification. In one direction, if \(z\) is a fixed point of \(T\), then a lemma
\[
\texttt{scaled_forward_backward_fixed_implies_solution}
\]
shows that \(-Bz\) lies in the subdifferential of \(\Phi\) at \(z\), and then the assumption \(\texttt{hsolution}\) gives \(z\in S\). In the other direction, if \(z\in S\), then \(\texttt{hsolution}\) gives the subdifferential condition, and a lemma
\[
\texttt{scaled_forward_backward_solution_implies_fixed}
\]
shows that \(z\) is a fixed point of \(T\).

Next the proof shows that the scaled proximity operator is firmly nonexpansive. Since \(\Phi\) belongs to \(\mathrm{gammaZero}\), scaling it by the positive parameter \(\mu\) keeps it in \(\mathrm{gammaZero}\), and the proximity operator of a \(\mathrm{gammaZero}\) function is firmly nonexpansive.

Then the forward step \(z\mapsto z-\mu Bz\) is shown to be \(1\)-Lipschitz. This uses the \(\beta\)-cocoercivity of \(B\) and the assumption \(0<\mu<2\beta\). Therefore \(T\), being the composition of a firmly nonexpansive operator with a \(1\)-Lipschitz operator, is itself \(1\)-Lipschitz.

Because \(S\) is nonempty and \(\operatorname{Fix}(T)=S\), the operator \(T\) has at least one fixed point \(p_0\). The proof applies a lemma
\[
\texttt{forward_backward_distance_and_residual_tendsto}
\]
to \(p_0\). This gives two facts: the distances
\[
\|\mathrm{alg.x}\,n-p_0\|
\]
converge as \(n\to\infty\), and the residuals
\[
\mathrm{alg.x}\,n-T(\mathrm{alg.x}\,n)
\]
tend to \(0\). The convergence of distances to \(p_0\) implies that the range of the sequence \(\mathrm{alg.x}\) is bounded.

The same lemma is then used to show that for every fixed point \(z\) of \(T\), the distance sequence
\[
\|\mathrm{alg.x}\,n-z\|
\]
converges.

The proof then verifies a key cluster-point property: every weak sequential cluster point of the iterates is a fixed point of \(T\). Given a weak sequential cluster point \(z\), one extracts a subsequence indexed by \(\varphi\) that converges weakly to \(z\). Since the full residual sequence tends to \(0\), the residual along this subsequence also tends to \(0\). Boundedness of the iterates gives a uniform bound on
\[
\|\mathrm{alg.x}(\varphi\,n)-z\|.
\]
A lemma
\[
\texttt{nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero}
\]
is applied to the nonexpansive operator \(T\). It states that if a bounded sequence converges weakly to \(z\) and the residuals \(T(x_n)-x_n\) tend to \(0\), then \(z\) is a fixed point of \(T\). This yields \(Tz=z\).

Finally, Opial’s lemma is invoked with the fixed point \(p_0\), the sequence \(\mathrm{alg.x}\), the convergence of distances to every fixed point, and the cluster-point property. It produces a point \(z\) in the fixed-point set of \(T\) such that the whole sequence of iterates converges weakly to \(z\). Rewriting the fixed-point set of \(T\) back to \(S\) gives the desired conclusion: there exists \(z\in S\) such that
\[
\mathrm{alg.x}\,k
\]
converges weakly to \(z\).

