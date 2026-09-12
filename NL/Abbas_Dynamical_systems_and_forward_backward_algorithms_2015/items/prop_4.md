## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/prop_4.lean`

## Lean statement
```lean
theorem relaxed_gradient_projection_asymptotics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (projection : H → H) (C S : Set H) (x : ℝ → H) (mu : ℝ)
    (hs : S = {z | z ∈ C ∧ ∀ y ∈ C, Psi z ≤ Psi y}) (hS : S.Nonempty)
    (hmu : 0 < mu)
    (hconvex : ConvexOn ℝ Set.univ Psi)
    (hgradient : ∀ z, HasGradientAt Psi (∇ Psi z) z)
    (hgrad_lipschitz_bounded : ∀ r : ℝ, ∃ L : ℝ, 0 ≤ L ∧
      LipschitzOnWith (Real.toNNReal L) (fun q ↦ ∇ Psi q) (Metric.closedBall (x 0) r))
    (hC : IsClosed C ∧ Convex ℝ C)
    (_hbelow : ∃ m : ℝ, ∀ y ∈ C, m ≤ Psi y)
    (hprojection_mem : ∀ q, projection q ∈ C)
    (hprojection_min_dist : ∀ q z, z ∈ C → ‖q - projection q‖ ≤ ‖q - z‖)
    (_hdynamics : ∀ t, deriv x t + x t - projection (x t - mu • ∇ Psi (x t)) = 0)
    (hclassical : ∀ t, 0 ≤ t →
      HasDerivAt x (projection (x t - mu • ∇ Psi (x t)) - x t) t)
    (hx0 : x 0 ∈ C) :
    (∃ z ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))) ∧
    (∀ t, 0 ≤ t → x t ∈ C) ∧ AntitoneOn (fun t ↦ Psi (x t)) (Set.Ici 0) ∧
    Tendsto (fun t ↦ Psi (x t)) atTop (nhds (sInf (Psi '' C))) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      mu * deriv (fun s ↦ Psi (x s)) t + ‖deriv x t‖ ^ 2 ≤ 0
```

## Statement explanation
The declaration `relaxed_gradient_projection_asymptotics` concerns a continuous-time relaxed gradient-projection trajectory in a real Hilbert space $H$. The data are a function $\Psi:H\to\mathbb R$, a nearest-point projection $\mathrm{projection}:H\to H$ onto a set $C\subseteq H$, a set $S\subseteq H$, a trajectory $x:\mathbb R\to H$, and a step size $\mu\in\mathbb R$.

The hypotheses are:

- $S=\{z\in C:\forall y\in C,\ \Psi(z)\le\Psi(y)\}$, so $S$ is exactly the set of minimizers of $\Psi$ over $C$.
- $S\ne\emptyset$.
- $\mu>0$.
- $\Psi$ is convex on all of $H$, i.e. $\mathrm{ConvexOn}\mathbb R\mathrm{Set.univ}\Psi$.
- $\Psi$ has a gradient everywhere: for every $z$, $\mathrm{HasGradientAt}\Psi(\nabla\Psi(z))z$. In a Hilbert space this means that the Fréchet derivative of $\Psi$ at $z$ is represented by the vector $\nabla\Psi(z)$.
- The gradient map $q\mapsto\nabla\Psi(q)$ is locally Lipschitz on closed balls centered at $x(0)$: for every radius $r$, there is $L\ge0$ such that $q\mapsto\nabla\Psi(q)$ is Lipschitz with constant $L$ on $\mathrm{Metric.closedBall}(x(0),r)$.
- $C$ is closed and convex.
- $\Psi$ is bounded below on $C$: there is $m\in\mathbb R$ with $m\le\Psi(y)$ for all $y\in C$.
- The map $\mathrm{projection}$ maps into $C$, and for every $q$ and every $z\in C$,

  $$
  \|q-\mathrm{projection}(q)\|\le\|q-z\|.
  $$

  Thus $\mathrm{projection}(q)$ is a nearest point of $C$ to $q$.
- The dynamics are relaxed gradient-projection dynamics:

  $$
  \mathrm{deriv}x(t)+x(t)-\mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)=0
  $$

  for every $t$, equivalently

  $$
  \mathrm{deriv}x(t)
  =\mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)-x(t).
  $$

- On nonnegative times this derivative is classical:

  $$
  \forall t\ge0,\quad
  \mathrm{HasDerivAt}x\left(\mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)-x(t)\right)t.
  $$

- The initial point lies in the constraint set: $x(0)\in C$.

The conclusion is the conjunction of five assertions:

1. There exists $z\in S$ such that $x(t)$ converges weakly to $z$ as $t\to\infty$, expressed as

   $$
   \mathrm{toWeakSpace}_{\mathbb R,H}(x(t))
   \longrightarrow
   \mathrm{toWeakSpace}_{\mathbb R,H}(z).
   $$

2. The trajectory remains feasible:

   $$
   \forall t\ge0,\quad x(t)\in C.
   $$

3. The objective value along the trajectory is nonincreasing on $[0,\infty)$:

   $$
   \mathrm{AntitoneOn}(t\mapsto\Psi(x(t)))([0,\infty)).
   $$

4. The objective values converge to the infimum of $\Psi$ over $C$:

   $$
   \Psi(x(t))\longrightarrow \mathrm{sInf}(\Psi''C)
   \qquad (t\to\infty).
   $$

5. Almost everywhere with respect to Lebesgue measure restricted to $[0,\infty)$,

   $$
   \mu\,\mathrm{deriv}(t\mapsto\Psi(x(t)))(t)
   +\|\mathrm{deriv}x(t)\|^2\le0.
   $$

In ordinary language: under convexity of $\Psi$, local Lipschitz continuity of its gradient, closed convexity of $C$, and the relaxed projection-gradient ODE, the trajectory stays in $C$, decreases the objective monotonically, satisfies a differential energy-dissipation inequality almost everywhere, converges in objective value to the minimal value of $\Psi$ on $C$, and converges weakly to a minimizer in $S$.

## Lean proof
```lean
by
  have hprojection_canonical : ∀ q : H, projection q = projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2) q :=
    supplied_projection_eq_canonical C projection hC hprojection_mem hprojection_min_dist
  have hcanonical_nonexpansive := canonical_projection_nonexpansive C hC
    (show C.Nonempty from ⟨projection 0, hprojection_mem 0⟩)
  have hpointwise (t : ℝ) (ht : 0 ≤ t) (hxtC : x t ∈ C) :
      mu * deriv (fun s ↦ Psi (x s)) t + ‖deriv x t‖ ^ 2 ≤ 0 := by
    have h := projection_gradient_objective_dissipation Psi C projection mu x t hxtC hmu hconvex
      hgradient hC hprojection_mem hprojection_min_dist (hclassical t ht)
    simpa only [(hclassical t ht).deriv] using h
  let P : H → H := projectionPoint C
    (isChebyshev_of_nonempty_isClosed_convex ⟨projection 0, hprojection_mem 0⟩ hC.1 hC.2)
  have hPcont : Continuous P := by
    simpa [P] using canonical_projection_continuous C ⟨projection 0, hprojection_mem 0⟩ hC
  have hgradcont : Continuous (fun q : H => ∇ Psi q) :=
    gradient_continuous_of_lipschitz_closedBalls Psi (x 0) hgrad_lipschitz_bounded
  have hforward (t : ℝ) (ht : 0 ≤ t) : x t ∈ C := by
    let p : ℝ → H := fun s => projection (x s - mu • ∇ Psi (x s))
    have hp : ContinuousOn p (Set.Icc 0 t) := by
      intro s hs
      have hxcont : ContinuousAt x s := (hclassical s hs.1).continuousAt
      have hgradcont' : ContinuousAt (fun u : ℝ => ∇ Psi (x u)) s :=
        hgradcont.continuousAt.comp hxcont
      have harg : ContinuousAt (fun u : ℝ => x u - mu • ∇ Psi (x u)) s :=
        hxcont.sub (continuousAt_const.smul hgradcont')
      change ContinuousWithinAt (fun u : ℝ => projection (x u - mu • ∇ Psi (x u)))
        (Set.Icc 0 t) s
      have hprojfun : (fun u : ℝ => projection (x u - mu • ∇ Psi (x u))) =
          (fun u : ℝ => P (x u - mu • ∇ Psi (x u))) := by
        funext u
        exact hprojection_canonical _
      rw [hprojfun]
      exact (hPcont.continuousAt.comp harg).continuousWithinAt
    have hformula := relaxed_projection_variation_of_constants t x p ht hp
      (fun s hs => by simpa [p] using hclassical s hs.1)
    exact relaxed_projection_variation_mem_closed_convex C x p t ht hx0 hC hp
      (fun s _ => hprojection_mem _) hformula
  have hPsiDeriv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt (fun s => Psi (x s))
      (inner ℝ (∇ Psi (x t)) (projection (x t - mu • ∇ Psi (x t)) - x t)) t := by
    simpa using ((hgradient (x t)).hasFDerivAt.comp t
      (hclassical t ht).hasFDerivAt).hasDerivAt
  have hanti : AntitoneOn (fun t => Psi (x t)) (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hPsiDeriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hPsiDeriv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := hpointwise t (interior_subset ht) (hforward t (interior_subset ht))
      have hnorm : 0 ≤ ‖deriv x t‖ ^ 2 := sq_nonneg _
      nlinarith [hmu]
  have haediss : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      mu * deriv (fun s ↦ Psi (x s)) t + ‖deriv x t‖ ^ 2 ≤ 0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    exact hpointwise t ht (hforward t ht)
  obtain ⟨z0, hz0⟩ := hS
  have hz0' : z0 ∈ C ∧ ∀ y ∈ C, Psi z0 ≤ Psi y := by
    rw [hs] at hz0
    exact hz0
  have hInf : sInf (Psi '' C) = Psi z0 := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨Psi z0, ⟨z0, hz0'.1, rfl⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hz0'.2 y hy
    · intro w hw
      exact ⟨Psi z0, ⟨z0, hz0'.1, rfl⟩, hw⟩
  let G : ℝ → ℝ := fun t => Psi (x t) - Psi z0
  have hGnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ G t := by
    exact sub_nonneg.mpr (hz0'.2 (x t) (hforward t ht))
  let E : ℝ → ℝ := fun t => (1 / 2) * ‖x t - z0‖ ^ 2 + mu * G t
  have hEhas (t : ℝ) (ht : 0 ≤ t) : HasDerivAt E
      (inner ℝ (projection (x t - mu • ∇ Psi (x t)) - x t) (x t - z0) +
        mu * inner ℝ (∇ Psi (x t))
          (projection (x t - mu • ∇ Psi (x t)) - x t)) t := by
    let F : H := projection (x t - mu • ∇ Psi (x t)) - x t
    have hdistance : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z0‖ ^ 2)
        ((1 / 2 : ℝ) * (2 * inner ℝ (x t - z0) F)) t := by
      simpa [F] using ((hclassical t ht).sub_const z0).norm_sq.const_mul (1 / 2 : ℝ)
    have hPsi : HasDerivAt (fun s ↦ Psi (x s)) (inner ℝ (∇ Psi (x t)) F) t := by
      simpa [F] using ((hgradient (x t)).hasFDerivAt.comp t
        (hclassical t ht).hasFDerivAt).hasDerivAt
    have hsum := hdistance.add ((hPsi.sub_const (Psi z0)).const_mul mu)
    simpa [E, G, F, real_inner_comm] using hsum
  have hEderiv (t : ℝ) (ht : 0 ≤ t) :
      deriv E t + ‖deriv x t‖ ^ 2 + mu * G t ≤ 0 := by
    have h := projection_gradient_energy_deriv Psi C projection mu x z0 t hz0'.1 hmu hconvex
      (fun q ↦ (hgradient q).differentiableAt) hC hprojection_mem hprojection_min_dist
      (hclassical t ht)
    rw [(hclassical t ht).deriv]
    change deriv (fun s ↦ (1 / 2) * ‖x s - z0‖ ^ 2 +
      mu * (Psi (x s) - Psi z0)) t +
        ‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 +
          mu * (Psi (x t) - Psi z0) ≤ 0
    nlinarith [hz0'.2 (x t) (hforward t ht)]
  have hEanti : AntitoneOn E (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hEhas t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hEhas t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h := hEderiv t (interior_subset ht)
      nlinarith [sq_nonneg ‖deriv x t‖, mul_nonneg hmu.le
        (hGnonneg t (interior_subset ht))]
  have hEnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ E t := by
    dsimp [E]
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg hmu.le (hGnonneg t ht))
  obtain ⟨einf, hElim⟩ := tendsto_of_antitone_nonneg_on_Ici_local E hEanti hEnonneg
  have hPsiCont : Continuous Psi := continuous_iff_continuousAt.mpr fun q =>
    (hgradient q).continuousAt
  let F : ℝ → H := fun t => projection (x t - mu • ∇ Psi (x t)) - x t
  let E' : ℝ → ℝ := fun t =>
    inner ℝ (F t) (x t - z0) + mu * inner ℝ (∇ Psi (x t)) (F t)
  have hxcontOn (T : ℝ) : ContinuousOn x (Set.Icc 0 T) := by
    intro t ht
    exact (hclassical t ht.1).continuousAt.continuousWithinAt
  have hFcontOn (T : ℝ) : ContinuousOn F (Set.Icc 0 T) := by
    have hxcont := hxcontOn T
    have hgradx : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) :=
      hgradcont.continuousOn.comp hxcont (Set.mapsTo_univ x _)
    have harg : ContinuousOn (fun t => x t - mu • ∇ Psi (x t)) (Set.Icc 0 T) :=
      hxcont.sub (continuousOn_const.smul hgradx)
    have hParg : ContinuousOn (fun t => P (x t - mu • ∇ Psi (x t)))
        (Set.Icc 0 T) := hPcont.continuousOn.comp harg (Set.mapsTo_univ _ _)
    apply (hParg.sub hxcont).congr
    intro t _
    simp only [F]
    rw [hprojection_canonical]
  have hE'contOn (T : ℝ) : ContinuousOn E' (Set.Icc 0 T) := by
    have hxcont := hxcontOn T
    have hFc := hFcontOn T
    have hgradx : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) :=
      hgradcont.continuousOn.comp hxcont (Set.mapsTo_univ x _)
    exact ((hFc.inner (hxcont.sub continuousOn_const)).add
      (continuousOn_const.mul (hgradx.inner hFc))).congr fun _ _ => rfl
  have hGcontOn (T : ℝ) : ContinuousOn G (Set.Icc 0 T) := by
    exact ((hPsiCont.continuousOn.comp (hxcontOn T) (Set.mapsTo_univ x _)).sub
      continuousOn_const).congr fun _ _ => rfl
  have hfinite (T : ℝ) (hT : 0 ≤ T) :
      ∫ t in 0..T, mu * G t ≤ E 0 := by
    apply energy_dissipation_interval_bound_local hT
    · intro t ht
      simpa [E'] using hEhas t ht.1
    · exact hE'contOn T
    · exact continuousOn_const.mul (hGcontOn T)
    · intro t ht
      have h := hEderiv t ht.1
      rw [(hEhas t ht.1).deriv, (hclassical t ht.1).deriv] at h
      change E' t + mu * G t ≤ 0
      dsimp [E', F]
      nlinarith [sq_nonneg ‖projection (x t - mu • ∇ Psi (x t)) - x t‖]
    · exact hEnonneg T hT
  have hGanti : AntitoneOn G (Set.Ici 0) := by
    intro s hs t ht hst
    exact sub_le_sub_right (hanti hs ht hst) _
  have hGrate (T : ℝ) (hT : 0 < T) : G T ≤ E 0 / (mu * T) := by
    have hconstInt : ∫ _ in (0 : ℝ)..T, mu * G T = T * (mu * G T) := by
      simp
      ring
    have hmonoInt : (∫ _ in (0 : ℝ)..T, mu * G T) ≤ ∫ t in 0..T, mu * G t := by
      apply intervalIntegral.integral_mono_on hT.le
      · exact intervalIntegrable_const
      · exact (continuousOn_const.mul (hGcontOn T)).intervalIntegrable_of_Icc hT.le
      · intro t ht
        exact mul_le_mul_of_nonneg_left
          (hGanti (Set.mem_Ici.mpr ht.1) (Set.mem_Ici.mpr hT.le) ht.2) hmu.le
    have hbound : T * (mu * G T) ≤ E 0 := by
      rw [← hconstInt]
      exact hmonoInt.trans (hfinite T hT.le)
    apply (le_div_iff₀ (mul_pos hmu hT)).2
    nlinarith
  have hGlim : Tendsto G atTop (nhds 0) := by
    have hupper : Tendsto (fun T : ℝ => E 0 / (mu * T)) atTop (nhds 0) := by
      simpa [div_div] using
        (tendsto_const_nhds.div_atTop Filter.tendsto_id :
          Tendsto (fun T : ℝ => (E 0 / mu) / T) atTop (nhds 0))
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact hGnonneg T hT
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact hGrate T hT
    · exact hupper
  have hobjlim : Tendsto (fun t => Psi (x t)) atTop (nhds (Psi z0)) := by
    simpa [G] using hGlim.add_const (Psi z0)
  have hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds l) := by
    intro z hz
    have hz' : z ∈ C ∧ ∀ y ∈ C, Psi z ≤ Psi y := by
      rw [hs] at hz
      exact hz
    have hzval : Psi z = Psi z0 := le_antisymm (hz'.2 z0 hz0'.1) (hz0'.2 z hz'.1)
    let Ez : ℝ → ℝ := fun t => (1 / 2) * ‖x t - z‖ ^ 2 + mu * G t
    have hEzhas (t : ℝ) (ht : 0 ≤ t) : HasDerivAt Ez
        (inner ℝ (F t) (x t - z) + mu * inner ℝ (∇ Psi (x t)) (F t)) t := by
      have hdistance := ((hclassical t ht).sub_const z).norm_sq.const_mul (1 / 2 : ℝ)
      have hpsi := hPsiDeriv t ht
      simpa [Ez, G, F, real_inner_comm] using
        hdistance.add ((hpsi.sub_const (Psi z0)).const_mul mu)
    have hEzderiv (t : ℝ) (ht : 0 ≤ t) : deriv Ez t ≤ 0 := by
      have h := projection_gradient_energy_deriv Psi C projection mu x z t hz'.1 hmu hconvex
        (fun q ↦ (hgradient q).differentiableAt) hC hprojection_mem
        hprojection_min_dist (hclassical t ht)
      have hfun : Ez = fun s => (1 / 2) * ‖x s - z‖ ^ 2 +
          mu * (Psi (x s) - Psi z) := by
        funext s
        simp [Ez, G, hzval]
      rw [← hfun, (hEzhas t ht).deriv] at h
      rw [(hEzhas t ht).deriv]
      dsimp [F] at h ⊢
      calc
        inner ℝ (projection (x t - mu • ∇ Psi (x t)) - x t) (x t - z) +
            mu * inner ℝ (∇ Psi (x t))
              (projection (x t - mu • ∇ Psi (x t)) - x t) ≤
            _ + ‖projection (x t - mu • ∇ Psi (x t)) - x t‖ ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
        _ ≤ mu * (Psi z - Psi (x t)) := h
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmu.le
          (sub_nonpos.mpr (hz'.2 (x t) (hforward t ht)))
    have hEzanti : AntitoneOn Ez (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro t ht
        exact (hEzhas t ht).continuousAt.continuousWithinAt
      · intro t ht
        exact (hEzhas t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        exact hEzderiv t (interior_subset ht)
    have hEznonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Ez t := by
      exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg hmu.le (hGnonneg t ht))
    obtain ⟨l, hEzlim⟩ := tendsto_of_antitone_nonneg_on_Ici_local Ez hEzanti hEznonneg
    have hsq : Tendsto (fun t => ‖x t - z‖ ^ 2) atTop (nhds (2 * l)) := by
      convert (hEzlim.sub (hGlim.const_mul mu)).const_mul 2 using 1
      · ext t
        simp [Ez]
      · ring_nf
    refine ⟨Real.sqrt (2 * l), ?_⟩
    have hsqrt := Real.continuous_sqrt.tendsto (2 * l) |>.comp hsq
    convert hsqrt using 1
    ext t
    simp
  have hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
        (nhds (toWeakSpace ℝ H z))) → z ∈ S := by
    rintro z ⟨u, huTop, huWeak⟩
    have huNonneg : ∀ᶠ n in atTop, 0 ≤ u n := (tendsto_atTop.1 huTop) 0
    have hCweak : IsClosed (toWeakSpace ℝ H '' C) :=
      (isClosed_iff_weak_image_isClosed_of_convex hC.2).1 hC.1
    have hzWeakC : toWeakSpace ℝ H z ∈ toWeakSpace ℝ H '' C :=
      hCweak.mem_of_tendsto huWeak (huNonneg.mono fun n hn =>
        ⟨x (u n), hforward (u n) hn, rfl⟩)
    have hzC : z ∈ C := by
      rcases hzWeakC with ⟨y, hyC, hyz⟩
      have : y = z := (toWeakSpace ℝ H).injective hyz
      simpa [this] using hyC
    have hzPsi : Psi z ≤ Psi z0 := by
      by_contra hnot
      have hlt : Psi z0 < Psi z := lt_of_not_ge hnot
      let eps : ℝ := (Psi z - Psi z0) / 2
      have heps : 0 < eps := by dsimp [eps]; linarith
      let L : Set H := {y | Psi y ≤ Psi z0 + eps}
      have hLclosed : IsClosed L := by
        exact isClosed_Iic.preimage hPsiCont
      have hLconvex : Convex ℝ L := by
        intro a ha b hb α β hα hβ hab
        dsimp [L] at ha hb ⊢
        have hcv := hconvex.2 (Set.mem_univ a) (Set.mem_univ b) hα hβ hab
        change Psi (α • a + β • b) ≤ α * Psi a + β * Psi b at hcv
        calc
          Psi (α • a + β • b) ≤ α * Psi a + β * Psi b := hcv
          _ ≤ α * (Psi z0 + eps) + β * (Psi z0 + eps) :=
            add_le_add (mul_le_mul_of_nonneg_left ha hα)
              (mul_le_mul_of_nonneg_left hb hβ)
          _ = Psi z0 + eps := by rw [← add_mul, hab, one_mul]
      have hLweak : IsClosed (toWeakSpace ℝ H '' L) :=
        (isClosed_iff_weak_image_isClosed_of_convex hLconvex).1 hLclosed
      have hvalues : Tendsto (fun n => Psi (x (u n))) atTop (nhds (Psi z0)) :=
        hobjlim.comp huTop
      have hevent : ∀ᶠ n in atTop, x (u n) ∈ L := by
        filter_upwards [(tendsto_order.1 hvalues).2 _ (lt_add_of_pos_right _ heps)] with n hn
        exact hn.le
      have hzLweak : toWeakSpace ℝ H z ∈ toWeakSpace ℝ H '' L :=
        hLweak.mem_of_tendsto huWeak (hevent.mono fun n hn => ⟨x (u n), hn, rfl⟩)
      rcases hzLweak with ⟨y, hyL, hyz⟩
      have hyz' : y = z := (toWeakSpace ℝ H).injective hyz
      dsimp [L] at hyL
      rw [hyz'] at hyL
      dsimp [eps] at hyL
      linarith
    rw [hs]
    exact ⟨hzC, fun y hy => hzPsi.trans (hz0'.2 y hy)⟩
  obtain ⟨z, hzS, hweak⟩ := opial_trajectory_lemma S x ⟨z0, hz0⟩ hdist hcluster
  exact ⟨⟨z, hzS, hweak⟩, hforward, hanti, by simpa [hInf] using hobjlim, haediss⟩
```

## Proof explanation
The proof proceeds through several layers: identifying the supplied projection with the canonical metric projection, proving forward invariance and monotonicity, proving convergence of the objective values, establishing distance limits, and finally applying Opial’s weak convergence lemma.

1. Identifying the projection with the canonical one.  
   The theorem `supplied_projection_eq_canonical` is used first. Its content is that if $C$ is closed and convex, and a map $\mathrm{projection}:H\to H$ satisfies

   $$
   \mathrm{projection}(q)\in C,
   \qquad
   \|q-\mathrm{projection}(q)\|\le\|q-z\|\quad(z\in C),
   $$

   then $\mathrm{projection}$ agrees with the canonical metric projection $P_C$ on $C$. The canonical projection is constructed using `isChebyshev_of_nonempty_isClosed_convex`, which says that a nonempty closed convex subset of a Hilbert space is Chebyshev, so every point has a unique nearest point. Nonemptiness of $C$ is obtained from $\mathrm{projection}(0)\in C$. Thus the proof obtains

   $$
   \mathrm{projection}(q)=P_C(q)
   $$

   for every $q$. The fact `canonical_projection_nonexpansive` is also recorded: the canonical projection is nonexpansive,

   $$
   \|P_C(q)-P_C(r)\|\le\|q-r\|.
   $$

   This fact is not used later in the visible proof.

2. Pointwise energy dissipation.  
   For $t\ge0$ and $x(t)\in C$, the proof applies `projection_gradient_objective_dissipation`. Its hypotheses are exactly the current ones: $\mu>0$, convexity of $\Psi$, existence of gradients, closed convexity of $C$, the projection-membership and nearest-point properties, and the derivative formula

   $$
   x'(t)=\mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)-x(t).
   $$

   It concludes

   $$
   \mu\,\mathrm{deriv}(\Psi\circ x)(t)
   +\left\|\mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)-x(t)\right\|^2
   \le0.
   $$

   Using `simpa` together with `(hclassical t ht).deriv`, which identifies the projection increment with $\mathrm{deriv}x(t)$, the proof rewrites this as

   $$
   \mu\,\mathrm{deriv}(\Psi\circ x)(t)+\|\mathrm{deriv}x(t)\|^2\le0.
   $$

   This is the pointwise dissipation inequality `hpointwise`.

3. Continuity of the canonical projection and the gradient.  
   The theorem `canonical_projection_continuous` gives continuity of $P_C$. The theorem `gradient_continuous_of_lipschitz_closedBalls` gives continuity of $q\mapsto\nabla\Psi(q)$: local Lipschitz estimates on every closed ball centered at $x(0)$ imply ordinary continuity everywhere. These continuity facts are used later to prove continuity of the projected gradient vector field and of various energy functions.

4. Forward invariance of $C$.  
   Fix $t\ge0$. Define

   $$
   p(s)=\mathrm{projection}\!\left(x(s)-\mu\nabla\Psi(x(s))\right).
   $$

   First the proof shows $p$ is continuous on $[0,t]$. The trajectory $x$ is continuous at each $s\in[0,t]$ because its derivative exists there. The gradient along the trajectory is continuous by composing the continuous gradient map with $x$. Hence the argument $s\mapsto x(s)-\mu\nabla\Psi(x(s))$ is continuous, and replacing $\mathrm{projection}$ by $P_C$ shows $p$ is continuous.

   Then `relaxed_projection_variation_of_constants` is applied. It says that if $p$ is continuous on $[0,t]$, $t\ge0$, and

   $$
   x'(s)=p(s)-x(s)\qquad(s\in[0,t]),
   $$

   then the variation-of-constants formula holds:

   $$
   x(t)=e^{-t}x(0)+\int_0^t e^{-(t-s)}p(s)\,ds.
   $$

   Here the derivative condition follows from `hclassical`.

   Finally `relaxed_projection_variation_mem_closed_convex` is applied with $x(0)\in C$, $p(s)\in C$, and the formula above. It states that if $C$ is closed and convex, $x(0)\in C$, $p$ is continuous and $p(s)\in C$ on $[0,t]$, and the variation-of-constants formula holds, then $x(t)\in C$. Mathematically, the right-hand side is an integral convex combination of points of $C$, because

   $$
   e^{-t}+\int_0^t e^{-(t-s)}\,ds=1.
   $$

   A closed convex set is closed under such averaged integrals. Hence the proof obtains `hforward`:

   $$
   \forall t\ge0,\quad x(t)\in C.
   $$

5. Derivative of the objective and monotonicity.  
   The proof computes, for $t\ge0$,

   $$
   \mathrm{deriv}(\Psi\circ x)(t)
   =\left\langle \nabla\Psi(x(t)),
   \mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)-x(t)\right\rangle.
   $$

   This is the chain rule using `HasGradientAt`: the derivative of $\Psi$ at $x(t)$ is the inner product with $\nabla\Psi(x(t))$, and the derivative of $x$ is the projection increment.

   Then `antitoneOn_of_deriv_nonpos` is applied on the convex interval $[0,\infty)$. Its content is: if a function is continuous on a convex interval and differentiable on its interior with nonpositive derivative there, then the function is antitone on the interval. For $t>0$, the pointwise dissipation inequality gives

   $$
   \mu\,\mathrm{deriv}(\Psi\circ x)(t)+\|\mathrm{deriv}x(t)\|^2\le0.
   $$

   Since $\mu>0$ and $\|\mathrm{deriv}x(t)\|^2\ge0$, `nlinarith` deduces

   $$
   \mathrm{deriv}(\Psi\circ x)(t)\le0.
   $$

   Hence $t\mapsto\Psi(x(t))$ is antitone on $[0,\infty)$. This is the third conclusion.

6. Almost-everywhere dissipation inequality.  
   The proof uses `MeasureTheory.ae_restrict_mem measurableSet_Ici` to handle almost-everywhere statements on $[0,\infty)$. For almost every $t$ in $[0,\infty)$, feasibility $x(t)\in C$ gives the pointwise inequality

   $$
   \mu\,\mathrm{deriv}(\Psi\circ x)(t)+\|\mathrm{deriv}x(t)\|^2\le0.
   $$

   This proves the fifth conclusion.

7. The minimizer $z_0$ and the infimum.  
   The proof chooses $z_0\in S$. From the definition of $S$, $z_0\in C$ and

   $$
   \Psi(z_0)\le\Psi(y)\qquad(y\in C).
   $$

   Thus $z_0$ is a minimizer over $C$. The lemma `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` is then used to show

   $$
   \mathrm{sInf}(\Psi''C)=\Psi(z_0).
   $$

   Indeed, $\Psi''C$ is nonempty because $z_0\in C$, every element of it is at least $\Psi(z_0)$, and any number larger than $\Psi(z_0)$ is already above the element $\Psi(z_0)$.

8. A Lyapunov energy for the distance to $z_0$.  
   Define

   $$
   G(t)=\Psi(x(t))-\Psi(z_0).
   $$

   Since $x(t)\in C$ and $z_0$ minimizes over $C$, one has $G(t)\ge0$ for $t\ge0$. Define the energy

   $$
   E(t)=\frac12\|x(t)-z_0\|^2+\mu G(t).
   $$

   The proof computes its derivative:

   $$
   E'(t)
   =\langle F(t),x(t)-z_0\rangle
   +\mu\langle \nabla\Psi(x(t)),F(t)\rangle,
   $$

   where

   $$
   F(t)=\mathrm{projection}\!\left(x(t)-\mu\nabla\Psi(x(t))\right)-x(t).
   $$

   This uses the derivative of $\frac12\|x(t)-z_0\|^2$ and the chain rule for $\Psi\circ x$.

   Then `projection_gradient_energy_deriv` is applied with $c=z_0$. It states

   $$
   \mathrm{deriv}\!\left(\frac12\|x(s)-z_0\|^2
   +\mu(\Psi(x(s))-\Psi(z_0))\right)(t)
   +\|F(t)\|^2
   \le
   \mu(\Psi(z_0)-\Psi(x(t))).
   $$

   Since $F(t)=\mathrm{deriv}x(t)$, this becomes

   $$
   E'(t)+\|\mathrm{deriv}x(t)\|^2+\mu G(t)\le0.
   $$

   The proof then uses `antitoneOn_of_deriv_nonpos` to show $E$ is antitone on $[0,\infty)$. The derivative is nonpositive because

   $$
   E'(t)+\|\mathrm{deriv}x(t)\|^2+\mu G(t)\le0,
   $$

   and both $\|\mathrm{deriv}x(t)\|^2$ and $\mu G(t)$ are nonnegative. Also $E(t)\ge0$ for all $t\ge0$. Hence `tendsto_of_antitone_nonneg_on_Ici_local E` gives the existence of a limit of $E(t)$ as $t\to\infty$. This limit is recorded but not used directly later.

9. Convergence of $G$ and of the objective.  
   The proof next proves the integral bound

   $$
   \int_0^T \mu G(t)\,dt\le E(0)
   $$

   for every $T\ge0$. It applies `energy_dissipation_interval_bound_local` with $a=0$, $D(t)=\mu G(t)$, and $E'$ the derivative of $E$. The lemma says that if $E$ has derivative $E'$ on $[0,T]$, $E'$ and $D$ are continuous, $E'(t)+D(t)\le0$ on $[0,T]$, and $E(T)\ge0$, then

   $$
   \int_0^T D(t)\,dt\le E(0).
   $$

   All hypotheses are supplied using the previously computed derivative and continuity facts.

   Since $G$ is antitone, for $0\le t\le T$ one has $G(T)\le G(t)$. Multiplying by $\mu>0$ and integrating gives

   $$
   T\mu G(T)
   =\int_0^T \mu G(T)\,dt
   \le\int_0^T \mu G(t)\,dt
   \le E(0).
   $$

   The proof uses `intervalIntegral.integral_mono_on` for the comparison of integrals. Dividing by $\mu T>0$ yields

   $$
   G(T)\le \frac{E(0)}{\mu T}.
   $$

   Since $G(T)\ge0$ and $E(0)/(\mu T)\to0$ as $T\to\infty$, `squeeze_zero'` gives

   $$
   G(t)\longrightarrow0.
   $$

   Therefore

   $$
   \Psi(x(t))=G(t)+\Psi(z_0)\longrightarrow\Psi(z_0).
   $$

   Using

   $$
   \Psi(z_0)=\mathrm{sInf}(\Psi''C),
   $$

   this proves the fourth conclusion, namely convergence of the objective values to the infimum over $C$.

10. Distance limits for points of $S$.  
    For an arbitrary $z\in S$, one has $z\in C$ and $\Psi(z)\le\Psi(y)$ for all $y\in C$. Since $z_0$ is also a minimizer, $\Psi(z)=\Psi(z_0)$. The proof defines

    $$
    E_z(t)=\frac12\|x(t)-z\|^2+\mu G(t).
    $$

    Its derivative is computed just as for $E$. Applying `projection_gradient_energy_deriv` with $c=z$ gives

    $$
    E_z'(t)+\|F(t)\|^2\le \mu(\Psi(z)-\Psi(x(t))).
    $$

    Because $x(t)\in C$ and $z$ minimizes over $C$, the right-hand side is nonpositive. Hence $E_z'(t)\le0$. Thus $E_z$ is antitone and nonnegative on $[0,\infty)$, so `tendsto_of_antitone_nonneg_on_Ici_local` gives a limit $l$ of $E_z(t)$ as $t\to\infty$.

    Since $G(t)\to0$, one obtains

    $$
    \frac12\|x(t)-z\|^2=E_z(t)-\mu G(t)\longrightarrow l.
    $$

    Therefore

    $$
    \|x(t)-z\|^2\longrightarrow 2l.
    $$

    By continuity of the square root, `Real.continuous_sqrt` gives

    $$
    \|x(t)-z\|\longrightarrow \sqrt{2l}.
    $$

    This verifies, for every $z\in S$, the distance-limit hypothesis needed for Opial’s lemma.

11. Weak cluster points lie in $S$.  
    The proof then shows that every weak sequential cluster point of $x(t)$ belongs to $S$. Suppose $u_n\to\infty$ and

    $$
    \mathrm{toWeakSpace}_{\mathbb R,H}(x(u_n))
    \longrightarrow
    \mathrm{toWeakSpace}_{\mathbb R,H}(z).
    $$

    First, since eventually $u_n\ge0$, feasibility gives $x(u_n)\in C$. The theorem `isClosed_iff_weak_image_isClosed_of_convex` states that for a convex set, norm-closedness is equivalent to weak-closedness of its image under `toWeakSpace`. Because $C$ is closed and convex, its weak image is closed. Hence the weak limit $z$ lies in the weak image of $C$, and injectivity of `toWeakSpace` gives $z\in C$.

    Next the proof shows $\Psi(z)\le\Psi(z_0)$. Suppose not. Then $\Psi(z_0)<\Psi(z)$. Let

    $$
    \varepsilon=\frac{\Psi(z)-\Psi(z_0)}2>0
    $$

    and define the sublevel set

    $$
    L=\{y:\Psi(y)\le\Psi(z_0)+\varepsilon\}.
    $$

    Since $\Psi$ is continuous, $L$ is closed. Since $\Psi$ is convex, $L$ is convex: if $a,b\in L$ and $y=\alpha a+\beta b$ with $\alpha,\beta\ge0$, $\alpha+\beta=1$, then

    $$
    \Psi(y)\le \alpha\Psi(a)+\beta\Psi(b)
    \le \Psi(z_0)+\varepsilon.
    $$

    Thus $L$ is closed and convex, so its weak image is closed by the same closedness theorem. Since $\Psi(x(u_n))\to\Psi(z_0)$, eventually $x(u_n)\in L$. Therefore the weak limit $z$ belongs to the weak image of $L$, hence to $L$, giving

    $$
    \Psi(z)\le \Psi(z_0)+\varepsilon<\Psi(z),
    $$

    a contradiction. Hence $\Psi(z)\le\Psi(z_0)$. Since $z_0$ minimizes over $C$, this implies $\Psi(z)\le\Psi(y)$ for all $y\in C$. Together with $z\in C$, this gives $z\in S$.

12. Applying Opial’s trajectory lemma.  
    The theorem `opial_trajectory_lemma` is now applied to $S$ and $x$. Its hypotheses are: $S\ne\emptyset$; for every $z\in S$, the distance $\|x(t)-z\|$ has a limit as $t\to\infty$; and every weak sequential cluster point of $x(t)$ belongs to $S$. Its conclusion is that there exists $z\in S$ such that

    $$
    \mathrm{toWeakSpace}_{\mathbb R,H}(x(t))
    \longrightarrow
    \mathrm{toWeakSpace}_{\mathbb R,H}(z).
    $$

    This is exactly the first conclusion of the theorem.

13. Assembling the final conjunction.  
    The final `exact` packages the five conclusions: the weak convergence to some $z\in S$, the forward invariance $x(t)\in C$ for $t\ge0$, the antitonicity of $t\mapsto\Psi(x(t))$, the convergence of $\Psi(x(t))$ to $\mathrm{sInf}(\Psi''C)$ obtained from the limit to $\Psi(z_0)$ and the identity $\mathrm{sInf}(\Psi''C)=\Psi(z_0)$, and the almost-everywhere dissipation inequality.

The proof does not invoke the hypotheses named `_hbelow` or `_hdynamics` in the displayed proof text; the derivative information used throughout comes from `hclassical`. It also records `hcanonical_nonexpansive` and a limit of $E$, but the subsequent argument does not refer to them directly.

