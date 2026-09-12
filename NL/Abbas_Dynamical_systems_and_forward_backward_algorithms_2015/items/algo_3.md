## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/algo_3.lean`

## Lean statement
```lean
theorem forward_backward_stepsize_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (S : Set H) (h beta : ℝ)
    (alg : ForwardBackwardAlgorithm Phi hPhi B h)
    (hh : 0 < h ∧ h < 2 * beta)
    (hS : S.Nonempty)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z) :
    ∃ z ∈ S,
      Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (alg.x k)) Filter.atTop
        (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The theorem `forward_backward_stepsize_convergence` is a weak-convergence theorem for the forward-backward splitting algorithm. It assumes that \(H\) is a complete real inner product space, that \(\Phi : H \to \operatorname{EReal}_{>\bot}\) belongs to the class \(\Gamma_0(H)\) of proper lower semicontinuous convex extended-real-valued functions, and that \(B : H \to H\) is a single-valued operator. The parameter \(h\) is the algorithm step size, \(\beta\) is the cocoercivity constant of \(B\), and `alg` packages the forward-backward iteration for \((\Phi,B)\) with step \(h\). The set \(S \subseteq H\) is the solution set, characterized by
\[
z \in S \iff -B z \in \partial \Phi(z).
\]
Thus \(z \in S\) means that \(0 \in \partial \Phi(z) + B z\), i.e. \(z\) solves the monotone inclusion associated with \(\Phi\) and \(B\). The hypotheses are that \(0<h<2\beta\), that \(S\neq\emptyset\), and that the restriction of \(B\) to all of \(H\) is \(\beta\)-cocoercive. The conclusion is that there exists \(z\in S\) such that the algorithm sequence `alg.x` converges weakly to \(z\):
\[
\operatorname{toWeakSpace}_{\mathbb R}^{H}(\texttt{alg.x } k)
\longrightarrow
\operatorname{toWeakSpace}_{\mathbb R}^{H}(z).
\]
Equivalently, `alg.x` converges to \(z\) in the weak topology of \(H\).

## Lean proof
```lean
by
  let T : H → H := fun z ↦ ERealFunction.scaledProximityOperator Phi hPhi
    ⟨h, alg.h_pos⟩ (z - h • B z)
  have hfixed : Function.fixedPoints T = S := by
    ext z
    simp only [Function.mem_fixedPoints, Function.IsFixedPt]
    exact ⟨fun hz => (hsolution z).2 (scaled_forward_backward_fixed_implies_solution_local
      Phi hPhi B h alg.h_pos z (by simpa [T] using hz)), fun hz =>
      scaled_forward_backward_solution_implies_fixed_local Phi hPhi B h alg.h_pos z
        ((hsolution z).1 hz)⟩
  have hP : FirmlyNonexpansive
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨h, alg.h_pos⟩) := by
    have hg := ERealFunction.smul_mem_gammaZero Phi hPhi ⟨h, alg.h_pos⟩
    simpa [ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero hg
  have hF : LipschitzWith 1 (fun z : H ↦ z - h • B z) :=
    forward_step_lipschitz_one_local B beta h hh hB
  have hTlip : LipschitzWith 1 T := by
    have hPlip := lipschitzWith_one_of_firmlyNonexpansive hP
    simpa [T, Function.comp_def] using hPlip.comp hF
  have hC : (Function.fixedPoints T).Nonempty := by rwa [hfixed]
  obtain ⟨p₀, hp₀⟩ := hC
  have hone : 0 < (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := by norm_num
  have hupdate : ∀ n, alg.x (n + 1) = (1 - (1 : ℝ)) • alg.x n +
      (1 : ℝ) • ERealFunction.scaledProximityOperator Phi hPhi ⟨h, alg.h_pos⟩
        (alg.x n - h • B (alg.x n)) := by
    intro n
    simpa using alg.update n
  have hseq₀ := forward_backward_distance_and_residual_tendsto_local
    (ERealFunction.scaledProximityOperator Phi hPhi ⟨h, alg.h_pos⟩) B beta h 1
    hh hone hB hP alg.x hupdate p₀ (by simpa [T] using hp₀)
  have hbounded : Bornology.IsBounded (Set.range alg.x) :=
    bounded_range_of_convergent_distance_to_point hseq₀.1
  have hdist : ∀ z ∈ Function.fixedPoints T, ∃ l : ℝ,
      Filter.Tendsto (fun n ↦ ‖alg.x n - z‖) Filter.atTop (nhds l) := by
    intro z hz
    exact (forward_backward_distance_and_residual_tendsto_local
      (ERealFunction.scaledProximityOperator Phi hPhi ⟨h, alg.h_pos⟩) B beta h 1
      hh hone hB hP alg.x hupdate z (by simpa [T] using hz)).1
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
      nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local T hTlip
        (fun n ↦ alg.x (phi n)) z hphiweak' hres hsubbound
    exact hfix
  rcases opial_lemma ⟨p₀, hp₀⟩ alg.x hdist hcluster with ⟨z, hz, hlim⟩
  exact ⟨z, by rwa [← hfixed], hlim⟩
```

## Proof explanation
Write \(x_n\) for `alg.x n`. The proof defines the forward-backward operator
\[
T(z)
=
\operatorname{Prox}_{h\Phi}\bigl(z-hBz\bigr)
=
\texttt{ERealFunction.scaledProximityOperator }\Phi\ h\Phi\ \langle h,\texttt{alg.h\_pos}\rangle
\bigl(z-hBz\bigr).
\]
Here the scaled proximity operator is the proximal operator of the positively rescaled function \(h\Phi\). The proof then shows that this operator is nonexpansive, that its fixed points are exactly \(S\), and that the algorithm is its unrelaxed fixed-point iteration. Opial’s lemma then gives weak convergence to a fixed point.

1. The first algebraic step is
\[
\operatorname{Fix}(T)=S.
\]
The proof uses `ext z` to reduce equality of sets to equality of membership for an arbitrary \(z\), and `simp only [Function.mem_fixedPoints, Function.IsFixedPt]` to rewrite \(z\in\operatorname{Fix}(T)\) as \(Tz=z\). It then proves the two directions of the equivalence.

For the direction \(Tz=z \Rightarrow z\in S\), the proof invokes
`scaled_forward_backward_fixed_implies_solution_local`.
That result says that if \(\Phi\in\Gamma_0(H)\), if \(h>0\), and if
\[
\operatorname{Prox}_{h\Phi}\bigl(z-hBz\bigr)=z,
\]
then
\[
-Bz\in\partial\Phi(z).
\]
The proof supplies the positivity hypothesis through `alg.h_pos`. The conclusion \(-Bz\in\partial\Phi(z)\), together with the characterization
\[
z\in S \iff -Bz\in\partial\Phi(z),
\]
gives \(z\in S\). In Lean this uses `(hsolution z).2`.

For the reverse direction \(z\in S \Rightarrow Tz=z\), the proof uses `(hsolution z).1` to obtain \(-Bz\in\partial\Phi(z)\). It then applies
`scaled_forward_backward_solution_implies_fixed_local`.
That result is the converse of the previous one: if \(\Phi\in\Gamma_0(H)\), \(h>0\), and \(-Bz\in\partial\Phi(z)\), then
\[
\operatorname{Prox}_{h\Phi}\bigl(z-hBz\bigr)=z.
\]
This is exactly \(Tz=z\), so the reverse implication is proved.

2. The proof next shows that the proximal part is firmly nonexpansive. It defines
\[
P(z)=\operatorname{Prox}_{h\Phi}(z).
\]
The theorem `smul_mem_gammaZero` states that if \(\Phi\in\Gamma_0(H)\) and \(\gamma>0\), then \(\gamma\Phi\in\Gamma_0(H)\). Here it is applied with \(\gamma=h\), using `alg.h_pos`, so \(h\Phi\in\Gamma_0(H)\). The theorem
`proximityOperator_firmlyNonexpansive_of_mem_gammaZero`
then says that for any function in \(\Gamma_0(H)\), its proximal operator is firmly nonexpansive. Applied to \(h\Phi\), and using the definition of `scaledProximityOperator`, this gives that
\[
P=\operatorname{Prox}_{h\Phi}
\]
is firmly nonexpansive. Equivalently, for all \(u,v\),
\[
\|P(u)-P(v)\|^2 \le \langle P(u)-P(v),u-v\rangle.
\]

3. The forward step is shown to be \(1\)-Lipschitz. The theorem
`forward_step_lipschitz_one_local`
states that if \(0<\mu<2\beta\) and \(B\) is \(\beta\)-cocoercive on all of \(H\), then
\[
F(z)=z-\mu Bz
\]
is \(1\)-Lipschitz. Here \(\mu=h\), and the hypothesis \(0<h<2\beta\) is exactly `hh`. Therefore
\[
F(z)=z-hBz
\]
is \(1\)-Lipschitz.

4. Since \(P\) is firmly nonexpansive, the lemma
`lipschitzWith_one_of_firmlyNonexpansive`
gives that \(P\) is \(1\)-Lipschitz. The proof composes this with the \(1\)-Lipschitz forward step:
\[
T=P\circ F.
\]
The composition of two \(1\)-Lipschitz maps is \(1\)-Lipschitz, so `hTlip` proves that \(T\) is \(1\)-Lipschitz. In Lean this is `hPlip.comp hF`, followed by `simpa [T, Function.comp_def]` to identify the composition with \(T\).

5. Because \(S\) is nonempty and \(\operatorname{Fix}(T)=S\), the proof obtains a fixed point \(p_0\) of \(T\):
\[
Tp_0=p_0.
\]
This uses `hC : (Function.fixedPoints T).Nonempty := by rwa [hfixed]`, where `rwa` rewrites \(\operatorname{Fix}(T)\) to \(S\) and then applies `hS`.

6. The proof now applies the convergence theorem
`forward_backward_distance_and_residual_tendsto_local`.
That theorem has the following content. Suppose \(P\) is firmly nonexpansive, \(B\) is \(\beta\)-cocoercive, \(0<\mu<2\beta\), \(0<\eta\le 1\), and a sequence satisfies the relaxed forward-backward update
\[
x_{n+1}=(1-\eta)x_n+\eta P\bigl(x_n-\mu Bx_n\bigr).
\]
If \(p\) is a fixed point of the operator \(x\mapsto P(x-\mu Bx)\), then two conclusions hold:
\[
\exists l\in\mathbb R,\qquad \|x_n-p\|\to l,
\]
and
\[
x_n-P\bigl(x_n-\mu Bx_n\bigr)\to 0.
\]

In the present proof, the theorem is applied with \(P=\operatorname{Prox}_{h\Phi}\), \(\mu=h\), and relaxation parameter \(\eta=1\). The proof checks \(0<1\le 1\) by `norm_num`. The algorithm update is converted into the required update with \(\eta=1\): after simplifying \((1-1)\bullet x_n+1\bullet P(\cdots)\), the displayed equality is exactly the algorithm’s update law. This is done in the `hupdate` step using `simpa using alg.update n`.

Applying the local theorem to the fixed point \(p_0\) gives:
\[
\exists l,\quad \|x_n-p_0\|\to l,
\]
and
\[
x_n-Tx_n\to 0,
\]
because \(T(z)=P(z-hBz)\). This conjunction is `hseq₀`.

7. From the first part of `hseq₀`, the lemma
`bounded_range_of_convergent_distance_to_point`
says that if the distances \(\|x_n-z\|\) converge to a real limit, then the range of the sequence is bounded. Applied to \(p_0\), it gives
\[
\texttt{Bornology.IsBounded (Set.range alg.x)}.
\]
So the sequence \(x_n\) is bounded.

8. The proof then verifies the distance hypothesis needed for Opial’s lemma. For every fixed point \(z\) of \(T\), it reapplies `forward_backward_distance_and_residual_tendsto_local`, this time with \(p=z\). Since \(z\in\operatorname{Fix}(T)\), it satisfies
\[
P\bigl(z-hBz\bigr)=z,
\]
which is the fixed-point hypothesis of the local theorem. The first conclusion gives
\[
\exists l,\quad \|x_n-z\|\to l.
\]
Thus for every \(z\in\operatorname{Fix}(T)\), the distance sequence to \(z\) converges.

9. Next the proof shows that every weak sequential cluster point of \(x_n\) lies in \(\operatorname{Fix}(T)\). Suppose
\[
\operatorname{toWeakSpace}_{\mathbb R}^{H}(x_{\varphi(n)})
\to
\operatorname{toWeakSpace}_{\mathbb R}^{H}(z)
\]
for some strictly increasing \(\varphi:\mathbb N\to\mathbb N\). This is the content of `IsSequentialClusterPt`.

The residual convergence \(x_n-Tx_n\to 0\) from `hseq₀.2` is composed with the subsequence \(\varphi\), giving
\[
x_{\varphi(n)}-T\bigl(x_{\varphi(n)}\bigr)\to 0.
\]
The boundedness of the full sequence gives a constant \(C\) with \(\|x_n\|\le C\) for all \(n\). The proof obtains this from `isBounded_iff_forall_norm_le.mp hbounded`. Then, by the triangle inequality,
\[
\|x_{\varphi(n)}-z\|
\le \|x_{\varphi(n)}\|+\|z\|
\le C+\|z\|.
\]
So the subsequence is bounded relative to \(z\).

The theorem
`nonexpansive_eq_of_tendsto_weakly_of_residual_tendsto_zero_local`
now applies. It states that if \(T\) is \(1\)-Lipschitz, if \(u_n\) converges weakly to \(z\), if \(u_n-Tu_n\to 0\), and if \(u_n\) is bounded relative to \(z\), then
\[
Tz=z.
\]
Taking \(u_n=x_{\varphi(n)}\), the hypotheses have just been verified. Therefore \(Tz=z\), i.e. \(z\in\operatorname{Fix}(T)\). This is a demiclosedness-type step: weak cluster points of the sequence are fixed points of the nonexpansive operator \(T\).

10. Finally the proof applies `opial_lemma`. Opial’s lemma states that if \(C\) is a nonempty set, if the distances from \(x_n\) to every point of \(C\) converge, and if every weak sequential cluster point of \(x_n\) belongs to \(C\), then there exists \(z\in C\) such that \(x_n\) converges weakly to \(z\). The proof applies it with
\[
C=\operatorname{Fix}(T).
\]
The set \(C\) is nonempty because \(p_0\in C\). The distance convergence was proved in step 8, and the cluster-point condition in step 9. Therefore Opial’s lemma gives some \(z\in\operatorname{Fix}(T)\) such that
\[
\operatorname{toWeakSpace}_{\mathbb R}^{H}(x_n)
\to
\operatorname{toWeakSpace}_{\mathbb R}^{H}(z).
\]
Since \(\operatorname{Fix}(T)=S\), the final rewrite `rwa [← hfixed]` converts \(z\in\operatorname{Fix}(T)\) into \(z\in S\). Hence the algorithm sequence converges weakly to a point of the solution set \(S\), which is exactly the claimed conclusion.

The tactics in the proof play the following roles: `let` introduces the abbreviation \(T\); `ext` proves the set equality \(\operatorname{Fix}(T)=S\) pointwise; `simp` and `simpa` unfold definitions and normalize scalar arithmetic; `exact` closes goals with the cited results; `rwa` rewrites and then applies an existing hypothesis; `obtain` and `rcases` destruct nonemptiness, fixed-point, and cluster-point hypotheses; `intro` introduces arbitrary points and indices; `norm_num` proves the numerical fact \(0<1\le 1\); and `calc` performs the triangle-inequality bound. `linarith` is not used in this proof.

