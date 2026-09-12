## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_thm_2.lean`

## Lean statement
```lean
theorem omega_limit_properties {N : Type*} [NormedAddCommGroup N]
    [InnerProductSpace ℝ N] [CompleteSpace N] [FiniteDimensional ℝ N] [ProperSpace N]
    (Φ : N → ℝ) (gradΦ : N → N)
    (_hΦ : ContDiff ℝ 1 Φ) (_hgradΦ : ∀ u, HasFDerivAt Φ (innerSL ℝ (gradΦ u)) u)
    (hgrad_cont : Continuous gradΦ)
    (x : Set.Ici (0 : ℝ) → N)
    (hcontinuous_flow : ∃ φ : ℝ → N → N, Continuous (Function.uncurry φ) ∧ ∃ x₀ : N,
      ∀ t : Set.Ici (0 : ℝ), x t = φ (t : ℝ) x₀)
    (hbounded : Bornology.IsBounded (Set.range x))
    (velocity : Set.Ici (0 : ℝ) → N)
    (_hvelocity : Tendsto velocity atTop (nhds 0))
    (hgradient : Tendsto (fun t : Set.Ici (0 : ℝ) => gradΦ (x t)) atTop (nhds 0)) :
    (omegaLimit x).Nonempty ∧ IsCompact (omegaLimit x) ∧ IsConnected (omegaLimit x) ∧
    Tendsto (fun t : Set.Ici (0 : ℝ) => Metric.infDist (x t) (omegaLimit x)) atTop (nhds 0) ∧
      ∀ z ∈ omegaLimit x, gradΦ z = 0
```

## Statement explanation
The theorem concerns the \(\omega\)-limit set of a trajectory \(x\) in a finite-dimensional real inner product space \(N\). Here \(N\) is a normed additive commutative group, an inner product space over \(\mathbb R\), complete, finite-dimensional, and proper, so closed bounded subsets are compact.

The data are:

- a function \(\Phi : N \to \mathbb R\), a gradient map \(\operatorname{grad}\Phi : N \to N\), with \(\Phi\) class \(C^1\), the Fréchet derivative of \(\Phi\) at \(u\) given by
  \[
  v \mapsto \langle \operatorname{grad}\Phi(u), v\rangle,
  \]
  and \(\operatorname{grad}\Phi\) continuous;
- a trajectory \(x : [0,\infty) \to N\), meaning \(x\) is a function on the subtype of nonnegative reals;
- \(x\) is realized by a continuous flow: there is a continuous \(\phi : \mathbb R \to N \to N\) and an initial point \(x_0\) such that
  \[
  x(t)=\phi(t,x_0)
  \]
  for every \(t\ge 0\);
- the image \(\operatorname{range} x\) is bounded;
- there is a velocity map \(\operatorname{velocity} : [0,\infty)\to N\) tending to \(0\) at infinity, though this hypothesis is not used in the proof;
- the gradient along the trajectory tends to zero:
  \[
  \operatorname{grad}\Phi(x(t)) \to 0
  \quad\text{as } t\to\infty.
  \]

The \(\omega\)-limit set is defined as the set of all limit points of \(x\) along sequences of times tending to infinity:
\[
\omega(x)
=
\left\{
a\in N:
\exists (t_n)_{n\in\mathbb N}\subset [0,\infty),\
t_n\to\infty,\
x(t_n)\to a
\right\}.
\]

The conclusion is the conjunction of five assertions:

\[
\omega(x)\ne\varnothing,
\]
\[
\omega(x)\text{ is compact},
\]
\[
\omega(x)\text{ is connected},
\]
\[
\operatorname{dist}(x(t),\omega(x))\to 0
\quad\text{as } t\to\infty,
\]
and
\[
\forall z\in \omega(x),\qquad \operatorname{grad}\Phi(z)=0.
\]

Thus, mathematically, the theorem says that a bounded continuous trajectory whose gradient along the trajectory tends to zero has a nonempty compact connected \(\omega\)-limit set, the trajectory approaches this limit set in distance, and every point of the limit set is a critical point of \(\Phi\). The differentiability assumptions on \(\Phi\), the exact gradient identity, and the velocity convergence are part of the statement, but the given proof only uses continuity of the gradient and the convergence \(\operatorname{grad}\Phi(x(t))\to 0\).

## Lean proof
```lean
by
  rcases hcontinuous_flow with ⟨φ, hφcont, x₀, hx⟩
  have hxcont : Continuous x := by
    have hi : Continuous (fun t : Set.Ici (0 : ℝ) => ((t : ℝ), x₀)) :=
      continuous_subtype_val.prodMk continuous_const
    rw [show x = fun t : Set.Ici (0 : ℝ) => φ (t : ℝ) x₀ from funext hx]
    exact hφcont.comp hi
  let τ : ℕ → Set.Ici (0 : ℝ) := fun n =>
    ⟨(n : ℝ), by change (0 : ℝ) ≤ (n : ℝ); positivity⟩
  let K : ℕ → Set N := fun n => closure (x '' Set.Ici (τ n))
  have hKn : ∀ n : ℕ, (K n).Nonempty := by
    intro n
    refine ⟨x (τ n), ?_⟩
    apply subset_closure
    refine ⟨τ n, ?_, rfl⟩
    change τ n ≤ τ n
    exact le_rfl
  have hKsub : ∀ n : ℕ, K n ⊆ closure (Set.range x) := by
    intro n
    apply closure_mono
    rintro y ⟨t, ht, hxy⟩
    exact ⟨t, hxy⟩
  have hKcompact : ∀ n : ℕ, IsCompact (K n) := by
    intro n
    exact (hbounded.isCompact_closure).of_isClosed_subset isClosed_closure (hKsub n)
  have hKstep : ∀ n : ℕ, K (n + 1) ⊆ K n := by
    intro n
    apply closure_mono
    rintro y ⟨t, ht, hxy⟩
    refine ⟨t, ?_, hxy⟩
    change (τ n : ℝ) ≤ (t : ℝ)
    calc
      (τ n : ℝ) = (n : ℝ) := rfl
      _ ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
      _ = (τ (n + 1) : ℝ) := rfl
      _ ≤ (t : ℝ) := ht
  have hKpre : ∀ n : ℕ, IsPreconnected (K n) := by
    intro n
    change IsPreconnected (closure (x '' Set.Ici (τ n)))
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    let g : ℝ → N := fun r =>
      x ⟨max r n, by change (0 : ℝ) ≤ max r n; exact hn0.trans (le_max_right _ _)⟩
    have hgcont : Continuous g := by
      apply hxcont.comp
      exact (continuous_id.max continuous_const).subtype_mk _
    have himage : x '' Set.Ici (τ n) = Set.range g := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(t : ℝ), ?_⟩
        dsimp [g]
        congr 2
        apply max_eq_left
        simpa [τ] using ht
      · rintro ⟨r, rfl⟩
        refine ⟨⟨max r n, by change (0 : ℝ) ≤ max r n; exact hn0.trans (le_max_right _ _)⟩, ?_, rfl⟩
        change (τ n : ℝ) ≤ max r n
        change (n : ℝ) ≤ max r n
        exact le_max_right _ _
    rw [himage, ← Set.image_univ]
    exact (isPreconnected_univ.image g hgcont.continuousOn).closure
  have homega : omegaLimit x = ⋂ n : ℕ, K n := by
    simpa [K, τ] using omegaLimit_eq_iInter_nat_tailClosure x
  have hOmegaNonempty : (omegaLimit x).Nonempty := by
    rw [homega]
    exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKstep hKn
      (hKcompact 0) fun n => (hKcompact n).isClosed
  have hOmegaCompact : IsCompact (omegaLimit x) := by
    rw [homega]
    apply (hKcompact 0).of_isClosed_subset
    · exact isClosed_iInter fun n => (hKcompact n).isClosed
    · exact Set.iInter_subset _ 0
  have hOmegaPreconnected : IsPreconnected (omegaLimit x) := by
    rw [homega]
    exact nested_isPreconnected_iInter K hKstep hKcompact
      (fun n => (hKcompact n).isClosed) hKn hKpre
  have hDistOmega : Tendsto (fun t => Metric.infDist (x t) (omegaLimit x)) atTop (nhds 0) :=
    tendsto_infDist_omegaLimit_of_compact_closure x hbounded.isCompact_closure
  have hCritical : ∀ z ∈ omegaLimit x, gradΦ z = 0 := by
    rintro z ⟨t, ht, hxt⟩
    have ht' : Tendsto t atTop atTop := by
      refine tendsto_atTop.2 fun s => ?_
      filter_upwards [ht.eventually (eventually_ge_atTop (s : ℝ))] with n hn
      exact hn
    have h1 : Tendsto (fun n : ℕ => gradΦ (x (t n))) atTop (nhds 0) := by
      simpa [Function.comp_def] using hgradient.comp ht'
    have h2 : Tendsto (fun n : ℕ => gradΦ (x (t n))) atTop (nhds (gradΦ z)) := by
      simpa [Function.comp_def] using (hgrad_cont.tendsto z).comp hxt
    exact tendsto_nhds_unique h2 h1
  exact ⟨hOmegaNonempty, hOmegaCompact, ⟨hOmegaNonempty, hOmegaPreconnected⟩,
    hDistOmega, hCritical⟩
```

## Proof explanation
The proof begins by extracting the continuous flow data. From `hcontinuous_flow` it obtains a continuous map \(\phi:\mathbb R\to N\to N\), a point \(x_0\), and the equality
\[
x(t)=\phi(t,x_0)
\]
for all \(t\in[0,\infty)\). It then proves that \(x\) itself is continuous. The auxiliary map
\[
t\mapsto (t,x_0)
\]
is continuous because the first coordinate is the subtype inclusion \([0,\infty)\hookrightarrow \mathbb R\) and the second is constant. Composing this map with the continuous uncurried map \((s,u)\mapsto \phi(s,u)\) gives continuity of \(t\mapsto \phi(t,x_0)\). The command `rw` replaces \(x\) by this composite function using the equality `funext hx`, and `exact hφcont.comp hi` closes the continuity goal.

Next the proof defines
\[
\tau_n=\langle n,\ 0\le n\rangle\in [0,\infty),
\]
so that \(\tau_n\) is the nonnegative real number \(n\). It defines
\[
K_n=\overline{x\bigl([n,\infty)\bigr)},
\]
where more explicitly
\[
x\bigl([n,\infty)\bigr)=\{x(t): t\in[0,\infty),\ t\ge n\}.
\]
Thus \(K_n\) is the closure of the image of the tail of the trajectory starting at time \(n\).

The proof establishes several properties of the sequence \(K_n\). First, each \(K_n\) is nonempty: the point \(x(\tau_n)=x(n)\) lies in the tail image, hence in its closure. Second,
\[
K_n\subseteq \overline{\operatorname{range}x},
\]
because the tail image is contained in the full range of \(x\), and closure is monotone. Third, each \(K_n\) is compact. Indeed, \(\operatorname{range}x\) is bounded, so its closure is compact by properness of \(N\); the set \(K_n\) is closed and contained in this compact closure, hence compact. Fourth, the sequence is decreasing:
\[
K_{n+1}\subseteq K_n.
\]
This follows because any time \(t\ge n+1\) also satisfies \(t\ge n\), so the tail image at \(n+1\) is contained in the tail image at \(n\); taking closures preserves inclusion.

The proof then shows that each \(K_n\) is preconnected. It defines a continuous map
\[
g_n(r)=x(\max(r,n)).
\]
Here \(\max(r,n)\ge n\ge 0\), so \(g_n\) is well-defined on \([0,\infty)\). Continuity follows from continuity of \(x\), continuity of \(r\mapsto \max(r,n)\), and the fact that \(n\ge 0\). The image of \(g_n\) is exactly the tail image:
\[
x\bigl([n,\infty)\bigr)=g_n(\mathbb R).
\]
Indeed, if \(t\ge n\), then \(\max(t,n)=t\), giving \(x(t)=g_n(t)\); conversely every \(g_n(r)=x(\max(r,n))\) has time \(\max(r,n)\ge n\). Since \(\mathbb R\) is preconnected and continuous images of preconnected sets are preconnected, \(g_n(\mathbb R)\) is preconnected. The closure of a preconnected set is preconnected, so
\[
K_n=\overline{g_n(\mathbb R)}
\]
is preconnected.

The proof then identifies the \(\omega\)-limit set with the intersection of the tails. The cited result `omegaLimit_eq_iInter_nat_tailClosure` says that for a metric space and a trajectory \(x\),
\[
\omega(x)=\bigcap_{n\in\mathbb N}\overline{x\bigl([n,\infty)\bigr)}.
\]
Specialized to the present notation, this gives
\[
\omega(x)=\bigcap_{n\in\mathbb N} K_n.
\]
The mathematical content is that a point is an eventual limit point along times tending to infinity exactly when it belongs to the closure of every tail of the trajectory.

Using this identification, the proof proves nonemptiness. It invokes the compact finite-intersection principle for a decreasing sequence of nonempty compact closed sets: if \(K_{n+1}\subseteq K_n\), each \(K_n\) is nonempty, \(K_0\) is compact, and each \(K_n\) is closed, then
\[
\bigcap_{n\in\mathbb N}K_n\ne\varnothing.
\]
Applying this to the present \(K_n\) gives \((\omega(x)).\operatorname{Nonempty}\).

Compactness of \(\omega(x)\) is then obtained as follows. The intersection \(\bigcap_n K_n\) is closed because it is an intersection of closed sets. It is contained in \(K_0\), which is compact. A closed subset of a compact set is compact, so \(\omega(x)\) is compact.

Preconnectedness of \(\omega(x)\) uses the cited theorem `nested_isPreconnected_iInter`. That theorem says that in a Hausdorff normal space, if \(K_n\) is a decreasing sequence of nonempty compact closed preconnected sets, then
\[
\bigcap_{n\in\mathbb N}K_n
\]
is preconnected. The present \(K_n\) satisfy all these hypotheses: they are decreasing, compact, closed, nonempty, and preconnected. Therefore \(\omega(x)=\bigcap_n K_n\) is preconnected. Since \(\omega(x)\) is also nonempty, it is connected. In the final assembly, this is the pair \(\langle hOmegaNonempty,hOmegaPreconnected\rangle\) representing connectedness.

The distance convergence is supplied by the cited result `tendsto_infDist_omegaLimit_of_compact_closure`. It states that for a metric-space trajectory \(x\), if \(\overline{\operatorname{range}x}\) is compact, then
\[
\operatorname{infDist}(x(t),\omega(x))\to 0.
\]
In the proof, boundedness of \(\operatorname{range}x\) and properness of \(N\) give compactness of \(\overline{\operatorname{range}x}\), so the lemma yields
\[
\operatorname{dist}(x(t),\omega(x))\to 0.
\]

Finally the proof shows that every point of the \(\omega\)-limit set is critical. Let \(z\in\omega(x)\). By the definition of `omegaLimit`, there is a sequence
\[
t:\mathbb N\to[0,\infty)
\]
such that \(t_n\to\infty\) in \(\mathbb R\) and \(x(t_n)\to z\). The proof lifts the convergence \(t_n\to\infty\) to the subtype \([0,\infty)\): for every threshold \(s\ge 0\), eventually \(s\le t_n\), so \(t_n\to\infty\) in the order of the subtype. Composing the hypothesis
\[
\operatorname{grad}\Phi(x(t))\to 0
\]
with \(t_n\to\infty\) gives
\[
\operatorname{grad}\Phi(x(t_n))\to 0.
\]
On the other hand, continuity of \(\operatorname{grad}\Phi\) and \(x(t_n)\to z\) give
\[
\operatorname{grad}\Phi(x(t_n))\to \operatorname{grad}\Phi(z).
\]
Since limits in a Hausdorff space are unique, the two limits must be equal:
\[
\operatorname{grad}\Phi(z)=0.
\]
The proof uses `tendsto_nhds_unique h2 h1` to extract this equality.

The final `exact` assembles all five conclusions: nonemptiness, compactness, connectedness, distance convergence, and the critical-point property. The hypotheses `_hΦ`, `_hgradΦ`, and `_hvelocity` are not used in the given proof; the only gradient hypotheses used are continuity of `gradΦ` and the convergence of the gradient along the trajectory.

