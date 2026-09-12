## Source file
`Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators/items/thm_1.lean`

## Lean statement
```lean
theorem convergence_of_splitting_inertial_proximal
    {A : SetValuedOperator H H} {B : H → H}
    (hA_max : IsMaximalMonotone A)
    (hB_max : IsMaximalMonotone (svEmbed B))
    {β : ℝ} (hB_coco : IsCocoerciveWRT A B β)
    (hB_lipschitz : ∀ x y : H, ‖B x - B y‖ ≤ (1 / β) * ‖x - y‖)
    (x : ℕ → H) (θ lam ε : ℕ → ℝ)
    (y : ℕ → H)
    (hy : ∀ k, 1 ≤ k → y k = x k + θ k • (x k - x (k - 1)))
    (h_alg : ∀ k, 1 ≤ k → (0 : H) ∈ (lam k • enlargement A (ε k) (x (k + 1))) +
      {x (k + 1) - y k} + (lam k • svEmbed B (x k)))
    (h_delta : ∃ (δ : ℝ) (lamUnder : ℝ), 0 < lamUnder ∧ 0 < δ ∧
      ∀ k, 1 ≤ k → lamUnder ≤ lam k ∧ lam k ≤ 2 * β - δ)
    (h_theta : ∃ (θmax : ℝ), 0 ≤ θmax ∧ θmax < 1 ∧
      ∀ k, 1 ≤ k → 0 ≤ θ k ∧ θ k ≤ θmax)
    (h_eps_sum : Summable ε)
    (h_eps_pos : ∀ k, ε k ≥ 0)
    (h_summable : Summable fun k : ℕ ↦ θ (k + 1) * ‖x (k + 1) - x k‖ ^ 2)
    (hS_nonempty : ((A + svEmbed B).zeros).Nonempty)
    (h_norm_diff_tendsto : Tendsto (fun n : ℕ => ‖x (n+1) - x n‖) atTop (𝓝 0)) :
    ∃ (xstar : H), xstar ∈ (A + svEmbed B).zeros ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xstar))
```

## Statement explanation
The theorem states weak convergence of an inertial proximal splitting method for a sum of two maximal monotone operators on a real Hilbert space \(H\). Let \(A:H\rightrightarrows H\) be a set-valued operator and let \(B:H\to H\) be a single-valued map. Write \(\operatorname{svEmbed}B\) for the set-valued operator \(x\mapsto \{B(x)\}\), so that
\[
(A+\operatorname{svEmbed}B)(x)=A(x)+B(x)=\{a+B(x):a\in A(x)\}.
\]
The solution set is the zero set
\[
S=(A+\operatorname{svEmbed}B).\text{zeros}
=\{u\in H:0\in A(u)+B(u)\}.
\]
Here `zeros` is the preimage of \(0\) for a set-valued operator, so membership in \(S\) means exactly that \(0\) belongs to the value \((A+\operatorname{svEmbed}B)(u)\).

The hypotheses are the following. The operator \(A\) is maximal monotone, meaning it is monotone and maximal with respect to graph inclusion. The single-valued operator \(B\), viewed as the set-valued operator \(\operatorname{svEmbed}B\), is also maximal monotone. For a real number \(\beta\), the map \(B\) is assumed \(\beta\)-cocoercive with respect to \(A\): the hypothesis packages both \(0<\beta\) and the inequality
\[
\beta\|B(x)-B(y)\|^{2}\le \langle B(x)-B(y),x-y\rangle
\]
for all \(x\in H\) and all \(y\in S\). In addition, \(B\) is Lipschitz with constant \(1/\beta\):
\[
\|B(x)-B(y)\|\le \frac{1}{\beta}\|x-y\|
\]
for all \(x,y\in H\).

The theorem concerns sequences \(x:\mathbb N\to H\), \(y:\mathbb N\to H\), and real parameter sequences \(\theta,\lambda,\varepsilon:\mathbb N\to\mathbb R\). For every \(k\ge 1\), the inertial extrapolation step is
\[
y_k=x_k+\theta_k(x_k-x_{k-1}).
\]
The algorithm inclusion is
\[
0\in \lambda_k\,\operatorname{enl}_{A}^{\varepsilon_k}(x_{k+1})
+\{x_{k+1}-y_k\}+\lambda_k\{B(x_k)\},
\]
where \(\operatorname{enl}_{A}^{\varepsilon}\) is the enlargement of \(A\): a point \(v\) belongs to \(\operatorname{enl}_{A}^{\varepsilon}(x)\) when
\[
-\varepsilon\le \langle u-v,z-x\rangle
\]
for every \(z\in H\) and every \(u\in A(z)\). Thus the algorithm uses an approximate inclusion for \(A\), with error \(\varepsilon_k\), and an explicit evaluation of \(B\) at \(x_k\).

The step sizes are assumed to satisfy uniform bounds: there exist \(\delta>0\) and \(\lambda_{\text{under}}>0\) such that for every \(k\ge 1\),
\[
\lambda_{\text{under}}\le \lambda_k\le 2\beta-\delta.
\]
The inertial parameters satisfy: there exists \(\theta_{\max}\) with
\[
0\le \theta_{\max}<1,\qquad
0\le \theta_k\le \theta_{\max}\quad(k\ge 1).
\]
The approximation errors are summable and nonnegative:
\[
\sum_k \varepsilon_k<\infty,\qquad \varepsilon_k\ge 0.
\]
There is also a summability condition on the inertial increments:
\[
\sum_k \theta_{k+1}\|x_{k+1}-x_k\|^{2}<\infty.
\]
The zero set is assumed nonempty:
\[
S\neq\varnothing.
\]
Finally, consecutive differences tend to zero:
\[
\|x_{n+1}-x_n\|\to 0.
\]

The conclusion is that there exists \(x^*\in S\), i.e.
\[
0\in A(x^*)+B(x^*),
\]
such that \(x_k\) converges weakly to \(x^*\). In the Lean statement this is expressed by convergence of the image of \(x_k\) under `toWeakSpace`, the map from \(H\) to its copy with the weak topology. Thus the theorem asserts that the inertial proximal splitting scheme converges weakly to a solution of the monotone inclusion \(0\in A(x)+B(x)\).

## Lean proof
```lean
by
  -- ===== Extract parameters =====
  rcases h_delta with ⟨δ, lamUnder, hlamUnder_pos, hδ_pos, h_delta'⟩
  rcases h_theta with ⟨θmax, hθmax_nonneg, hθmax_lt_one, h_theta'⟩
  rcases hB_coco with ⟨hβ_pos, hB_coco'⟩
  have h_sum_max : IsMaximalMonotone (A + svEmbed B) :=
    maximalMonotone_add_svEmbed_of_lipschitz hA_max hβ_pos hB_max.1 hB_lipschitz
  have hβ_2pos : 0 < 2 * β := by linarith
  have hlam_pos : ∀ k, 1 ≤ k → 0 < lam k := by
    intro k hk; rcases h_delta' k hk with ⟨hl, _⟩; linarith
  have hlam_nonneg : ∀ k, 1 ≤ k → 0 ≤ lam k := by
    intro k hk; exact le_of_lt (hlam_pos k hk)
  have hθ_nonneg : ∀ k, 1 ≤ k → 0 ≤ θ k := by
    intro k hk; rcases h_theta' k hk with ⟨hl, _⟩; exact hl
  have hθ_bound : ∀ k, 1 ≤ k → θ k ≤ θmax := by
    intro k hk; rcases h_theta' k hk with ⟨_, hu⟩; exact hu
  -- η_k = 1 - λ_k/(2β) > 0
  set η : ℕ → ℝ := fun k => 1 - lam k / (2 * β) with hη_def
  have hη_lower : ∀ k, 1 ≤ k → δ / (2 * β) ≤ η k :=
    eta_lower_bound hβ_pos (fun k hk => (h_delta' k hk).2) hη_def
  have hη_pos : ∀ k, 1 ≤ k → 0 < η k :=
    eta_positive_of_lower hβ_pos hδ_pos hη_lower
  have hη_nonneg : ∀ k, 1 ≤ k → 0 ≤ η k := by
    intro k hk; exact le_of_lt (hη_pos k hk)
  have hη_le_one : ∀ k, 1 ≤ k → η k ≤ 1 :=
    eta_le_one hβ_pos hlam_nonneg hη_def
  have h_theta_eta_sum_le_two : ∀ k, 1 ≤ k → θ k + η k ≤ 2 := by
    intro k hk
    have hθ := hθ_bound k hk
    have hη := hη_le_one k hk
    linarith
  -- ===== φ function (for use across proof blocks) =====
  set phi : H → ℕ → ℝ := fun z k => (1/2 : ℝ) * ‖z - x k‖ ^ 2 with hphi_def
  -- ===== Unpack algorithm membership =====
  have h_alg_unpack : ∀ k, 1 ≤ k → ∃ a_k ∈ enlargement A (ε k) (x (k + 1)),
      x (k + 1) - y k + lam k • B (x k) = -lam k • a_k :=
    splitting_algorithm_unpack x y lam ε h_alg
  -- ===== S = (A + svEmbed B)⁻¹(0) =====
  set S : Set H := (A + svEmbed B).zeros with hS_def
  have hS_nonempty' : S.Nonempty := by
    rcases hS_nonempty with ⟨z, hz⟩; exact ⟨z, hz⟩
  -- Representation: z ∈ S iff ∃ a ∈ A z, a = -B z
  have hS_repr : ∀ z ∈ S, ∃ az ∈ A z, az = -B z := by
    exact zeros_sum_svEmbed_repr hS_def
  -- ===== KEY INEQUALITY (2.13) for any z ∈ S =====
  have h_key_ineq : ∀ z ∈ S, ∀ k, 1 ≤ k →
      phi z (k + 1) - phi z k - θ k * (phi z k - phi z (k - 1)) ≤
      -(1 / 2) * η k *
        ‖x (k + 1) - x k - (θ k / η k) • (x k - x (k - 1))‖ ^ 2 +
      (θ k / η k) * ‖x k - x (k - 1)‖ ^ 2 + lam k * ε k :=
    splitting_key_ineq x y θ lam ε η phi S hy h_alg_unpack hB_coco' hS_repr
      hβ_pos hlam_nonneg hη_pos h_theta_eta_sum_le_two hθ_nonneg hη_def
      (by
        intro z k
        rw [hphi_def])
  -- ===== Sigma summability (extracted for reuse) =====
  set σ_sum : ℕ → ℝ := fun k => (θ k / η k) * ‖x k - x (k - 1)‖ ^ 2 + lam k * ε k
  have h_sigma_summable : Summable σ_sum := by
    simpa [σ_sum] using
      sigma_sum_summable hβ_pos hδ_pos x θ lam ε η hη_lower hη_pos hlam_nonneg
        (fun k hk => by
          rcases h_delta' k hk with ⟨_, hu⟩
          linarith)
        hθ_nonneg h_eps_sum h_eps_pos h_summable
  have h_sigma_tendsto_zero : Tendsto σ_sum atTop (𝓝 0) :=
    h_sigma_summable.tendsto_atTop_zero
  -- ===== Opial's Lemma application =====
  have h_dist_exists : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - z‖) atTop (𝓝 l) :=
    distance_to_solution_tendsto x θ lam ε η phi S hβ_pos hδ_pos hθmax_nonneg
      hθmax_lt_one hlam_nonneg
      (fun k hk => by
        rcases h_delta' k hk with ⟨_, hu⟩
        linarith)
      hθ_nonneg hθ_bound hη_lower hη_pos h_eps_sum h_eps_pos h_summable
      (by
        intro z k
        rw [hphi_def])
      h_key_ineq
  have h_cluster_in_S : ∀ (z : H),
      IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (x k)) (toWeakSpace ℝ H z) → z ∈ S :=
    cluster_points_in_solution_set x y θ lam ε S hS_def h_sum_max hA_max.1 hB_max.1 hy
      h_alg_unpack hlamUnder_pos hlam_pos (fun k hk => (h_delta' k hk).1)
      hθmax_nonneg hθ_nonneg hθ_bound h_eps_sum hB_lipschitz h_norm_diff_tendsto
  -- Opial's Lemma: hS_nonempty' gives nonempty S, h_dist_exists gives norm convergence,
  -- h_cluster_in_S gives that weak cluster points belong to S
  -- Therefore: {x_k} converges weakly to some point in S
  exact opial_lemma hS_nonempty' x h_dist_exists h_cluster_in_S
```

## Proof explanation
The proof proceeds by extracting the numerical parameters, proving several uniform bounds on the parameters, constructing the standard energy function, applying the key inequality for splitting methods, and then applying Opial’s lemma.

First, the proof destructs the existential hypotheses. From
\[
\exists \delta\,\exists \lambda_{\text{under}},\quad
0<\lambda_{\text{under}}\land 0<\delta\land
\forall k\ge1,\ \lambda_{\text{under}}\le\lambda_k\le2\beta-\delta,
\]
it obtains \(\delta\), \(\lambda_{\text{under}}\), the positivity facts \(0<\lambda_{\text{under}}\) and \(0<\delta\), and the pointwise bounds
\[
\lambda_{\text{under}}\le\lambda_k,\qquad
\lambda_k\le2\beta-\delta
\]
for \(k\ge1\). From the hypothesis on \(\theta\) it obtains \(\theta_{\max}\), the inequalities \(0\le\theta_{\max}<1\), and
\[
0\le\theta_k\le\theta_{\max}\qquad(k\ge1).
\]
From `hB_coco` it obtains \(0<\beta\) and the cocoercivity inequality, which is later passed to the key estimate.

The proof then derives \(0<2\beta\) by `linarith` from \(0<\beta\). This is a linear arithmetic consequence used to justify denominators such as \(2\beta\).

Next, the proof establishes that the sum \(A+\operatorname{svEmbed}B\) is maximal monotone. It invokes `maximalMonotone_add_svEmbed_of_lipschitz`, whose mathematical content is: if \(A\) is maximal monotone, if \(\beta>0\), if \(\operatorname{svEmbed}B\) is monotone, and if \(B\) is Lipschitz with constant \(1/\beta\), then the sum \(A+\operatorname{svEmbed}B\) is maximal monotone. In the proof, the monotonicity of \(\operatorname{svEmbed}B\) is the first component `hB_max.1` of the maximal monotonicity of \(\operatorname{svEmbed}B\). Thus `h_sum_max` records that
\[
A+\operatorname{svEmbed}B
\]
is maximal monotone. This fact is used later to know that weak sequential cluster points of the algorithm belong to the solution set.

The proof then records lower and upper bounds for \(\lambda\). Since \(\lambda_{\text{under}}\le\lambda_k\) and \(\lambda_{\text{under}}>0\), it gets
\[
0<\lambda_k\qquad(k\ge1)
\]
by `linarith`; converting strict positivity to nonnegativity gives
\[
0\le\lambda_k\qquad(k\ge1).
\]
Similarly, from the bounds on \(\theta\) it records
\[
0\le\theta_k,\qquad
\theta_k\le\theta_{\max}\qquad(k\ge1).
\]

The auxiliary sequence
\[
\eta_k=1-\frac{\lambda_k}{2\beta}
\]
is then introduced. The proof establishes three properties of \(\eta\). First, using `eta_lower_bound`, whose content is that if \(\beta>0\), \(\lambda_k\le2\beta-\delta\), and \(\eta_k=1-\lambda_k/(2\beta)\), then
\[
\frac{\delta}{2\beta}\le\eta_k\qquad(k\ge1),
\]
it obtains the lower bound
\[
\frac{\delta}{2\beta}\le\eta_k.
\]
Indeed,
\[
1-\frac{\lambda_k}{2\beta}
\ge 1-\frac{2\beta-\delta}{2\beta}
=\frac{\delta}{2\beta}.
\]
Second, using `eta_positive_of_lower`, whose content is that if \(\beta>0\), \(\delta>0\), and \(\eta_k\ge\delta/(2\beta)\) for \(k\ge1\), then \(\eta_k>0\), it obtains
\[
0<\eta_k\qquad(k\ge1).
\]
Third, using `eta_le_one`, whose content is that if \(\beta>0\), \(\lambda_k\ge0\), and \(\eta_k=1-\lambda_k/(2\beta)\), then \(\eta_k\le1\), it obtains
\[
\eta_k\le1\qquad(k\ge1).
\]
The proof also records \(\eta_k\ge0\) from \(\eta_k>0\).

From these bounds, the proof derives
\[
\theta_k+\eta_k\le2\qquad(k\ge1).
\]
The reasoning is: \(\theta_k\le\theta_{\max}<1\) and \(\eta_k\le1\), so \(\theta_k+\eta_k<2\), hence certainly \(\theta_k+\eta_k\le2\). The tactic `linarith` combines the relevant inequalities.

The energy function is then defined by
\[
\phi(z,k)=\frac12\|z-x_k\|^{2}.
\]
This is the squared-distance or Fejér energy measuring how far the current iterate is from a candidate solution \(z\).

The algorithm inclusion is unpacked using `splitting_algorithm_unpack`. The mathematical content of that lemma is: if for every \(k\ge1\),
\[
0\in \lambda_k\,\operatorname{enl}_{A}^{\varepsilon_k}(x_{k+1})
+\{x_{k+1}-y_k\}+\lambda_k\{B(x_k)\},
\]
then for every \(k\ge1\) there exists
\[
a_k\in \operatorname{enl}_{A}^{\varepsilon_k}(x_{k+1})
\]
such that
\[
x_{k+1}-y_k+\lambda_k B(x_k)=-\lambda_k a_k.
\]
This simply rewrites the membership in a sum of sets: the element \(x_{k+1}-y_k+\lambda_k B(x_k)\) must equal \(-\lambda_k a_k\) for some \(a_k\) in the enlargement.

The solution set is named
\[
S=(A+\operatorname{svEmbed}B).\text{zeros}.
\]
The nonemptiness hypothesis is repackaged as \(S\neq\varnothing\). The proof then uses `zeros_sum_svEmbed_repr`, whose content is: if \(S\) is the zero set of \(A+\operatorname{svEmbed}B\), then for every \(z\in S\) there exists
\[
a_z\in A(z)
\]
such that
\[
a_z=-B(z).
\]
Indeed, \(z\in S\) means \(0\in A(z)+B(z)\), so some \(a_z\in A(z)\) satisfies \(a_z+B(z)=0\). This representation is one of the hypotheses needed for the key inequality.

The key estimate is then produced by `splitting_key_ineq`. Specialized to the current notation, it says: under the inertial relation for \(y_k\), the unpacked algorithm inclusion, the cocoercivity estimate for \(B\), the representation of points of \(S\), the positivity of \(\beta\), the nonnegativity of \(\lambda_k\), the positivity of \(\eta_k\), the inequality \(\theta_k+\eta_k\le2\), the nonnegativity of \(\theta_k\), the definition of \(\eta\), and the definition of \(\phi\), one has for every \(z\in S\) and every \(k\ge1\)
\[
\begin{aligned}
&\phi(z,k+1)-\phi(z,k)-\theta_k\bigl(\phi(z,k)-\phi(z,k-1)\bigr)\\
&\qquad\le
-\frac12\eta_k
\left\|
x_{k+1}-x_k-\frac{\theta_k}{\eta_k}(x_k-x_{k-1})
\right\|^{2}
+\frac{\theta_k}{\eta_k}\|x_k-x_{k-1}\|^{2}
+\lambda_k\varepsilon_k.
\end{aligned}
\]
This is the central energy inequality. It controls the difference between successive squared distances and the inertial correction by a negative square term plus an error term. The proof supplies the required definition of \(\phi\) by rewriting with `rw [hphi_def]`.

Next, the proof defines
\[
\sigma_k=\frac{\theta_k}{\eta_k}\|x_k-x_{k-1}\|^{2}+\lambda_k\varepsilon_k.
\]
It proves that \(\sigma\) is summable using `sigma_sum_summable`. The mathematical content of that lemma is: if \(\beta>0\), \(\delta>0\), \(\eta_k\ge\delta/(2\beta)\), \(\eta_k>0\), \(\lambda_k\ge0\), \(\lambda_k\le2\beta\), \(\theta_k\ge0\), \(\varepsilon\) is summable and nonnegative, and
\[
\sum_k \theta_{k+1}\|x_{k+1}-x_k\|^{2}<\infty,
\]
then
\[
\sum_k\left(
\frac{\theta_k}{\eta_k}\|x_k-x_{k-1}\|^{2}
+\lambda_k\varepsilon_k
\right)<\infty.
\]
In the proof, the hypothesis \(\lambda_k\le2\beta\) is obtained from \(\lambda_k\le2\beta-\delta\) and \(\delta>0\) by `linarith`. The command `simpa [σ_sum]` unfolds the local definition of \(\sigma\) so that the lemma applies exactly. The summability of \(\sigma\) implies
\[
\sigma_k\to0,
\]
recorded as `h_sigma_tendsto_zero`. This is a standard consequence of convergence of a series, and here it expresses that the inertial error plus approximation error tends to zero. In the displayed final argument this particular consequence is not used directly, but it is part of the quantitative analysis.

The proof then applies `distance_to_solution_tendsto`. Its mathematical content is: under the hypotheses \(\beta>0\), \(\delta>0\), \(0\le\theta_{\max}<1\), \(\lambda_k\ge0\), \(\lambda_k\le2\beta\), \(0\le\theta_k\le\theta_{\max}\), \(\eta_k\ge\delta/(2\beta)\), \(\eta_k>0\), \(\varepsilon\) summable and nonnegative, the weighted-increment summability, the definition \(\phi(z,k)=\frac12\|z-x_k\|^{2}\), and the key inequality, one has for every \(z\in S\)
\[
\exists l\in\mathbb R,\qquad
\|x_n-z\|\to l.
\]
In other words, the distance from the iterates to every element of the solution set converges to a finite limit. This is exactly the first condition required by Opial’s lemma. The proof supplies the needed step-size inequality \(\lambda_k\le2\beta\) by `linarith`, and supplies the definition of \(\phi\) by rewriting with `hphi_def`.

Next, the proof applies `cluster_points_in_solution_set`. Its content is: if \(S\) is the zero set of \(A+\operatorname{svEmbed}B\), if \(A+\operatorname{svEmbed}B\) is maximal monotone, if \(A\) and \(\operatorname{svEmbed}B\) are monotone, if the inertial relation holds, if the algorithm inclusion has been unpacked to the existence of \(a_k\in \operatorname{enl}_{A}^{\varepsilon_k}(x_{k+1})\) satisfying
\[
x_{k+1}-y_k+\lambda_k B(x_k)=-\lambda_k a_k,
\]
if \(\lambda_{\text{under}}>0\), if \(\lambda_k>0\) and \(\lambda_k\ge\lambda_{\text{under}}\), if \(\theta_{\max}\ge0\), if \(\theta_k\ge0\) and \(\theta_k\le\theta_{\max}\), if \(\varepsilon\) is summable, if \(B\) is Lipschitz with constant \(1/\beta\), and if
\[
\|x_{n+1}-x_n\|\to0,
\]
then every weak sequential cluster point of the sequence \(x_k\) lies in \(S\). Formally, for every \(z\in H\),
\[
\text{IsSequentialClusterPt}
\bigl((\operatorname{toWeakSpace}x_k)_k,\operatorname{toWeakSpace}z\bigr)
\Longrightarrow z\in S.
\]
The proof supplies exactly these hypotheses from the previously established facts: \(h_{\text{sum\_max}}\), the monotonicity components of \(A\) and \(\operatorname{svEmbed}B\), the unpacked algorithm, the lower bounds on \(\lambda\), the bounds on \(\theta\), the summability of \(\varepsilon\), the Lipschitz condition for \(B\), and the convergence to zero of consecutive differences. Thus it obtains
\[
h_{\text{cluster\_in\_S}}:
\forall z,\quad
\text{IsSequentialClusterPt}
\bigl((\operatorname{toWeakSpace}x_k)_k,\operatorname{toWeakSpace}z\bigr)
\Rightarrow z\in S.
\]

Finally, the proof invokes Opial’s lemma. The mathematical content of `opial_lemma` is: if \(C\subseteq H\) is nonempty, if for every \(z\in C\) the sequence \(\|x_n-z\|\) converges in \(\mathbb R\), and if every weak sequential cluster point of \(x_n\) belongs to \(C\), then there exists \(z\in C\) such that \(x_n\) converges weakly to \(z\). The proof applies this with \(C=S\). The nonemptiness condition is \(hS_{\text{nonempty}}'\), the distance convergence condition is `h_dist_exists`, and the cluster-point condition is `h_cluster_in_S`. The command `exact opial_lemma hS_nonempty' x h_dist_exists h_cluster_in_S` therefore produces
\[
\exists x^*\in S,\qquad
x_k\rightharpoonup x^*
\]
weakly. Since
\[
S=(A+\operatorname{svEmbed}B).\text{zeros},
\]
this gives
\[
x^*\in (A+\operatorname{svEmbed}B).\text{zeros},
\]
equivalently \(0\in A(x^*)+B(x^*)\), together with the asserted weak convergence. This is exactly the conclusion of the theorem.

