## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/cor_2.lean`

## Lean statement
```lean
theorem connected_critical_set_lojasiewicz {N : Type*} [Fintype N]
    (Ω A : Set (EuclideanSpace ℝ N)) (Φ : EuclideanSpace ℝ N → ℝ)
    (_hΦreg : ContDiff ℝ 2 Φ)
    (hΩ : IsOpen Ω) (hanalytic : IsRealAnalyticOn Ω Φ)
    (hLoj : HasLojasiewiczGradientInequality Φ) (hAΩ : A ⊆ Ω) (hA : A.Nonempty)
    (hcritical : ∀ a ∈ A, gradient Φ a = 0) (hconnected : IsConnected A) :
    (∃ c : ℝ, ∀ a ∈ A, Φ a = c) ∧
    (IsCompact A → ∃ σ θ c : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      (∀ a ∈ A, Φ a = c) ∧
      ∀ x, Metric.infDist x A < σ → Real.rpow |Φ x - c| (1 - θ) ≤ ‖gradient Φ x‖)
```

## Statement explanation
The declaration `connected_critical_set_lojasiewicz` is a theorem about a real-valued function \(\Phi\) on a finite-dimensional Euclidean space \(\mathbb{R}^N\), where \(N\) is a finite type. The hypotheses are:

- \(\Phi\) is \(C^2\), i.e. twice continuously differentiable.
- \(\Omega\subseteq\mathbb{R}^N\) is open, and \(\Phi\) is real analytic on \(\Omega\).
- \(\Phi\) satisfies the global Lojasiewicz gradient inequality, encoded by `hLoj`.
- \(A\subseteq\Omega\) and \(A\neq\varnothing\).
- Every point \(a\in A\) is critical for \(\Phi\), meaning \(\nabla\Phi(a)=0\).
- \(A\) is connected.

The conclusion has two parts. First, \(\Phi\) is constant on \(A\):

\[
\exists c\in\mathbb{R},\ \forall a\in A,\ \Phi(a)=c.
\]

Second, if \(A\) is compact, then the Lojasiewicz gradient inequality can be made uniform on a whole neighbourhood of \(A\). More precisely, there exist \(\sigma>0\), \(0<\theta<1/2\), and \(c\in\mathbb{R}\) such that \(\Phi(a)=c\) for every \(a\in A\), and for every \(x\in\mathbb{R}^N\) whose distance to the set \(A\) satisfies \(\operatorname{infDist}(x,A)<\sigma\),

\[
|\Phi(x)-c|^{1-\theta}\le \|\nabla\Phi(x)\|.
\]

Thus, on a connected set of critical points inside the real-analytic region \(\Omega\), the function is constant; and if that set is compact, the local Lojasiewicz inequality at its points can be replaced by one inequality with a single exponent and a single radius measured by distance to the entire set \(A\).

## Lean proof
```lean
by
  rcases hanalytic with ⟨_, hanalyticOn⟩
  have hlocal : ∀ a ∈ A, ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ x, ‖x - a‖ < σ → Real.rpow |Φ x - Φ a| (1 - θ) ≤ ‖gradient Φ x‖ := by
    intro a ha
    exact lojasiewicz_gradient_inequality Φ a (_hΦreg.of_le (by norm_num))
      ⟨Ω, ⟨hΩ, hanalyticOn⟩, hAΩ ha⟩ (hcritical a ha) hLoj
  have hlocally_constant : ∀ a ∈ A, ∃ σ : ℝ, 0 < σ ∧
      ∀ x ∈ A, ‖x - a‖ < σ → Φ x = Φ a := by
    intro a ha
    rcases hlocal a ha with ⟨σ, θ, hσ, hθ, hθlt, hineq⟩
    refine ⟨σ, hσ, ?_⟩
    intro x hx hxa
    have hz : Real.rpow |Φ x - Φ a| (1 - θ) = 0 := by
      apply le_antisymm
      · simpa [hcritical x hx] using hineq x hxa
      · exact Real.rpow_nonneg (abs_nonneg _) _
    have habs : |Φ x - Φ a| = 0 :=
      (Real.rpow_eq_zero (abs_nonneg _) (by linarith)).mp hz
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  let a0 : EuclideanSpace ℝ N := Classical.choose hA
  have ha0 : a0 ∈ A := Classical.choose_spec hA
  let c : ℝ := Φ a0
  let P : Set {x // x ∈ A} := {x | Φ x = c}
  have hPopen : IsOpen P := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨x, hx⟩ hxP
    rcases hlocally_constant x hx with ⟨σ, hσ, hloc⟩
    filter_upwards [Metric.ball_mem_nhds (⟨x, hx⟩ : {x // x ∈ A}) hσ] with y hy
    change dist y.val x < σ at hy
    change Φ y.val = c
    exact (hloc y.val y.property (by simpa [dist_eq_norm] using hy)).trans hxP
  have hPclosed : IsClosed P := by
    exact IsClosed.preimage (hanalyticOn.continuousOn.mono hAΩ).restrict isClosed_singleton
  letI : PreconnectedSpace {x // x ∈ A} := Subtype.preconnectedSpace hconnected.isPreconnected
  have hPall : Set.univ ⊆ P :=
    isPreconnected_univ.subset_isClopen ⟨hPclosed, hPopen⟩ ⟨⟨a0, ha0⟩, trivial, rfl⟩
  have hconst : ∀ a ∈ A, Φ a = c := by
    intro a ha
    have hmem := hPall (show (⟨a, ha⟩ : {x // x ∈ A}) ∈ Set.univ by trivial)
    exact hmem
  constructor
  · exact ⟨c, hconst⟩
  intro hcompact
  choose σ θ hσ hθpos hθlt hineq using hlocal
  let U : (a : {a // a ∈ A}) → Set (EuclideanSpace ℝ N) :=
    fun a => Metric.ball a (σ a a.property)
  have hUopen : ∀ a, IsOpen (U a) := fun a => Metric.isOpen_ball
  have hUcover : A ⊆ ⋃ a, U a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (hσ x hx)
  obtain ⟨t, htcover⟩ := hcompact.elim_finite_subcover U hUopen hUcover
  have ht : t.Nonempty := by
    by_contra ht
    simp only [Finset.not_nonempty_iff_eq_empty] at ht
    rcases hA with ⟨x, hx⟩
    have : x ∈ (∅ : Set (EuclideanSpace ℝ N)) := by simpa [ht] using htcover hx
    exact this
  let θ0 : ℝ := t.inf' ht (fun a => θ a a.property)
  have hθ0pos : 0 < θ0 := by
    rw [show θ0 = t.inf' ht (fun a => θ a a.property) by rfl]
    exact (Finset.lt_inf'_iff ht).2 (fun a ha => hθpos a a.property)
  have hθ0le : ∀ a ∈ t, θ0 ≤ θ a a.property := by
    intro a ha
    exact Finset.inf'_le _ ha
  obtain ⟨a1, ha1⟩ := ht
  have hθ0lt : θ0 < 1 / 2 :=
    lt_of_le_of_lt (hθ0le a1 ha1) (hθlt a1 a1.property)
  have hsmall_nhd : ∀ a ∈ A, ∃ ε : ℝ, 0 < ε ∧
      ∀ x, dist x a < ε → |Φ x - c| < 1 := by
    intro a ha
    have hat : AnalyticAt ℝ Φ a := hanalyticOn a (hAΩ ha)
    rcases (Metric.continuousAt_iff.mp hat.continuousAt 1 zero_lt_one) with ⟨ε, hε, hεprop⟩
    refine ⟨ε, hε, ?_⟩
    intro x hxa
    have hdist := hεprop hxa
    simpa [hconst a ha, Real.dist_eq] using hdist
  choose ε hε hεsmall using hsmall_nhd
  let V : (a : {a // a ∈ A}) → Set (EuclideanSpace ℝ N) :=
    fun a => Metric.ball a (ε a a.property)
  have hVopen : ∀ a, IsOpen (V a) := by
    intro a
    exact Metric.isOpen_ball
  have hVcover : A ⊆ ⋃ a, V a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (hε x hx)
  obtain ⟨u, hucover⟩ := hcompact.elim_finite_subcover V hVopen hVcover
  let W : Set (EuclideanSpace ℝ N) := (⋃ a ∈ t, U a) ∩ (⋃ a ∈ u, V a)
  have hWopen : IsOpen W :=
    (isOpen_biUnion fun a _ => hUopen a).inter (isOpen_biUnion fun a _ => hVopen a)
  have hWcover : A ⊆ W := fun x hx => ⟨htcover hx, hucover hx⟩
  obtain ⟨δ, hδ, hδW⟩ := hcompact.exists_thickening_subset_open hWopen hWcover
  refine ⟨δ, θ0, c, hδ, hθ0pos, hθ0lt, hconst, ?_⟩
  intro x hx
  have hxW : x ∈ W := hδW ((Metric.mem_thickening_iff_infDist_lt hA).2 hx)
  rcases Set.mem_iUnion₂.1 hxW.1 with ⟨a, ha, hxa⟩
  rcases Set.mem_iUnion₂.1 hxW.2 with ⟨b, hb, hxb⟩
  have hsmall : |Φ x - c| ≤ 1 := le_of_lt (hεsmall b b.property x
    (by simpa [V, Metric.mem_ball] using hxb))
  have hlocalineq := hineq a a.property x
    (by simpa [U, Metric.mem_ball, dist_eq_norm] using hxa)
  have hlocalineq' : Real.rpow |Φ x - c| (1 - θ a a.property) ≤ ‖gradient Φ x‖ := by
    simpa [hconst a a.property] using hlocalineq
  by_cases hz : |Φ x - c| = 0
  · rw [hz]
    exact (Real.zero_rpow (x := 1 - θ0) (by linarith)).le.trans (norm_nonneg _)
  · have hpos : 0 < |Φ x - c| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    apply le_trans (Real.rpow_le_rpow_of_exponent_ge hpos hsmall (by linarith [hθ0le a ha]))
      hlocalineq'
```

## Proof explanation
The proof starts by decomposing the analyticity hypothesis `hanalytic` and keeping the component `hanalyticOn`, which is the real-analyticity information on \(\Omega\). Later this component is used both to obtain continuity of \(\Phi\) and as the analyticity witness for the local Lojasiewicz theorem.

The first main step is to prove that at every point \(a\in A\) there is a local Lojasiewicz inequality. The proof defines

\[
\texttt{hlocal}:\quad \forall a\in A,\ \exists \sigma,\theta,\ 
0<\sigma\land 0<\theta\land \theta<\frac12
\land \forall x,\ \|x-a\|<\sigma\Rightarrow
|\Phi(x)-\Phi(a)|^{1-\theta}\le \|\nabla\Phi(x)\|.
\]

To obtain this, for each \(a\in A\) it invokes the cited theorem `lojasiewicz_gradient_inequality`. That theorem says that if \(\Phi\) is \(C^1\), is real analytic near a point \(a\), has \(\nabla\Phi(a)=0\), and satisfies the global Lojasiewicz gradient inequality, then there exist \(\sigma>0\) and \(0<\theta<1/2\) such that for all \(x\) with \(\|x-a\|<\sigma\),

\[
|\Phi(x)-\Phi(a)|^{1-\theta}\le \|\nabla\Phi(x)\|.
\]

The proof supplies the required \(C^1\) regularity by lowering the given \(C^2\) hypothesis using `_hΦreg.of_le (by norm_num)`; `norm_num` discharges the numerical fact \(1\le 2\). It supplies the analyticity witness \(\Omega\) using `hΩ` and `hanalyticOn`, and it uses \(hAΩ\) to know \(a\in\Omega\). It supplies criticality from `hcritical a ha` and the global hypothesis `hLoj`.

The next step proves local constancy of \(\Phi\) on \(A\). For \(a\in A\), the proof takes the local Lojasiewicz data \(\sigma,\theta\). If \(x\in A\) and \(\|x-a\|<\sigma\), then \(x\) is also a critical point, so \(\nabla\Phi(x)=0\). The local inequality becomes

\[
|\Phi(x)-\Phi(a)|^{1-\theta}\le \|\nabla\Phi(x)\|=0.
\]

The left-hand side is nonnegative because it is a real power of an absolute value, so it must be zero. Since \(1-\theta>0\), in particular \(1-\theta\neq0\), the only way the real power can vanish is if the base vanishes. Hence

\[
|\Phi(x)-\Phi(a)|=0,
\]

and therefore \(\Phi(x)=\Phi(a)\). This proves that \(\Phi\) is locally constant on \(A\) near every point of \(A\).

The proof then chooses a base point \(a_0\in A\) using `Classical.choose hA` and sets \(c=\Phi(a_0)\). It considers the subset

\[
P=\{x\in A:\Phi(x)=c\}
\]

inside the subtype of points of \(A\). The local constancy result shows that \(P\) is open in this subtype: around any \(x\in P\), there is a relative ball in \(A\) on which \(\Phi\) remains equal to \(\Phi(x)=c\). The proof uses `rw [isOpen_iff_mem_nhds]` to reduce openness to the neighbourhood condition and `filter_upwards` to build the required neighbourhood.

The set \(P\) is also closed. Indeed, real analyticity on \(\Omega\) implies continuity of \(\Phi\) on \(\Omega\), hence on \(A\subseteq\Omega\). In the subtype topology on \(A\), the set \(P\) is the preimage of the closed singleton \(\{c\}\) under the continuous restriction of \(\Phi\) to \(A\). Thus \(P\) is closed.

Since \(A\) is connected, the subtype of points of \(A\) is preconnected. In a preconnected space, a nonempty clopen set is the whole space. Here \(P\) is clopen and contains \(a_0\), so \(P\) must be the entire subtype of points of \(A\). Therefore \(\Phi(a)=c\) for every \(a\in A\). This proves the first conjunct,

\[
\exists c\in\mathbb{R},\ \forall a\in A,\ \Phi(a)=c,
\]

using `constructor` and `exact ⟨c, hconst⟩`.

For the second conjunct, the proof assumes \(A\) is compact. It uses the earlier chosen local Lojasiewicz data \(\sigma(a),\theta(a)\) for each \(a\in A\). The open balls

\[
U_a = B(a,\sigma(a))
\]

cover \(A\). By compactness, `elim_finite_subcover` produces a finite subcover indexed by a finite nonempty set \(t\). The nonemptiness of \(t\) follows from \(A\neq\varnothing\) and the fact that \(t\) covers \(A\).

The proof then defines

\[
\theta_0=\min_{a\in t}\theta(a)
\]

using a finite infimum, written with `Finset.inf'`. Since every \(\theta(a)\) is positive, \(\theta_0>0\). Since \(t\) is nonempty, choosing some \(a_1\in t\) gives \(\theta_0\le\theta(a_1)<1/2\). Hence

\[
0<\theta_0<\frac12.
\]

Also, for every \(a\in t\),

\[
\theta_0\le \theta(a).
\]

Next, the proof needs a uniform bound \(|Φ(x)-c|<1\) near each point of \(A\). For each \(a\in A\), analyticity at \(a\) implies continuity at \(a\). Applying the epsilon-delta form of continuity with tolerance \(1\), there exists \(\epsilon(a)>0\) such that if \(\operatorname{dist}(x,a)<\epsilon(a)\), then

\[
|\Phi(x)-\Phi(a)|<1.
\]

Since \(\Phi(a)=c\) for \(a\in A\), this becomes

\[
|\Phi(x)-c|<1.
\]

The balls

\[
V_a=B(a,\epsilon(a))
\]

cover \(A\), and compactness gives another finite subcover indexed by a finite set \(u\).

Now the proof forms the open set

\[
W=\left(\bigcup_{a\in t} U_a\right)\cap\left(\bigcup_{a\in u} V_a\right).
\]

It is open because it is an intersection of unions of open balls, and it covers \(A\) because both the \(U\)-cover and the \(V\)-cover cover \(A\). Since \(A\) is compact and \(W\) is an open neighbourhood of \(A\), the theorem `exists_thickening_subset_open` gives a positive \(\delta\) such that the \(\delta\)-thickening of \(A\) is contained in \(W\). Thus, whenever

\[
\operatorname{infDist}(x,A)<\delta,
\]

the point \(x\) lies in \(W\). The proof uses `Metric.mem_thickening_iff_infDist_lt hA` to convert the distance-to-set condition into membership in the thickening.

Finally, fix \(x\) with \(\operatorname{infDist}(x,A)<\delta\). Since \(x\in W\), there are \(a\in t\) with \(x\in U_a\) and \(b\in u\) with \(x\in V_b\). From \(x\in V_b\), we get

\[
|\Phi(x)-c|<1.
\]

From \(x\in U_a\), the local Lojasiewicz inequality at \(a\) gives

\[
|\Phi(x)-\Phi(a)|^{1-\theta(a)}\le \|\nabla\Phi(x)\|.
\]

But \(\Phi(a)=c\), so this becomes

\[
|\Phi(x)-c|^{1-\theta(a)}\le \|\nabla\Phi(x)\|.
\]

The proof now splits into two cases. If \(|\Phi(x)-c|=0\), then since \(1-\theta_0>0\),

\[
|\Phi(x)-c|^{1-\theta_0}=0\le \|\nabla\Phi(x)\|.
\]

If \(|\Phi(x)-c|\neq0\), then the base \(r=|\Phi(x)-c|\) is positive, and the earlier bound gives \(r\le1\). Since \(\theta_0\le\theta(a)\), we have

\[
1-\theta(a)\le1-\theta_0.
\]

For a base \(0<r\le1\), increasing the exponent decreases the real power, so

\[
r^{1-\theta_0}\le r^{1-\theta(a)}.
\]

This is the content of `Real.rpow_le_rpow_of_exponent_ge`. Combining this with

\[
r^{1-\theta(a)}\le \|\nabla\Phi(x)\|
\]

yields

\[
|\Phi(x)-c|^{1-\theta_0}\le \|\nabla\Phi(x)\|.
\]

The linear inequalities on exponents are handled by `linarith`, using the previously established bounds \(0<\theta_0<1/2\) and \(\theta_0\le\theta(a)\). The proof then closes the existential statement by returning \(\delta\), \(\theta_0\), and \(c\), together with the constancy of \(\Phi\) on \(A\) and the uniform Lojasiewicz inequality on the \(\delta\)-neighbourhood of \(A\).

