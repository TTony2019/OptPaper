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
The theorem is about a continuous-time relaxed gradient-projection dynamical system in a real Hilbert space \(H\).

- \(H\) is a complete real inner product space, so it is a real Hilbert space.
- \(\Psi:H\to\mathbb R\) is the objective function.
- \(\operatorname{projection}:H\to H\) is the given projection map onto a set \(C\subseteq H\).
- \(S\subseteq H\) is defined by
  \[
  S=\{z\in C:\forall y\in C,\ \Psi(z)\le \Psi(y)\},
  \]
  so \(S\) is the set of minimizers of \(\Psi\) on \(C\).
- \(x:\mathbb R\to H\) is the trajectory.
- \(\mu\) is a positive step-size parameter.
- The hypotheses include:
  - \(C\) is nonempty through the minimizer set \(S\), and \(C\) is closed and convex.
  - \(\Psi\) is convex on all of \(H\).
  - \(\Psi\) has a gradient \(\nabla \Psi(z)\) at every \(z\).
  - The gradient is Lipschitz on every closed ball centered at \(x(0)\).
  - \(\operatorname{projection}\) maps every point into \(C\) and is the metric projection onto \(C\):
    \[
    \|\ q-\operatorname{projection}(q)\|\le \|q-z\|
    \]
    for every \(z\in C\).
  - The trajectory satisfies the relaxed projection-gradient dynamics: for \(t\ge 0\),
    \[
    x'(t)=\operatorname{projection}(x(t)-\mu\,\nabla\Psi(x(t)))-x(t).
    \]
    This is encoded both by an algebraic derivative equation and by a differentiability assumption.
  - The initial point satisfies \(x(0)\in C\).

The conclusion has five parts:

1. There exists \(z\in S\) such that \(x(t)\to z\) weakly as \(t\to\infty\), written as
   \[
   \operatorname{toWeakSpace}_{\mathbb R}^H(x(t))\to
   \operatorname{toWeakSpace}_{\mathbb R}^H(z).
   \]
2. The trajectory remains in \(C\) for all \(t\ge 0\).
3. The function \(t\mapsto \Psi(x(t))\) is nonincreasing on \([0,\infty)\).
4. The objective values converge to the infimum of \(\Psi\) over \(C\):
   \[
   \Psi(x(t))\to \inf_{y\in C}\Psi(y).
   \]
5. Almost everywhere on \([0,\infty)\), with respect to Lebesgue measure restricted to \([0,\infty)\), the dissipation inequality holds:
   \[
   \mu\,\frac{d}{dt}\Psi(x(t))+\|x'(t)\|^2\le 0.
   \]

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
The proof is a long combination of convex analysis, projection-gradient dissipation inequalities, Lyapunov energy arguments, and an Opial lemma for weak convergence.

First, the proof replaces the given projection map with the canonical metric projection point onto \(C\). Using the supplied lemma `supplied_projection_eq_canonical`, it proves that for every \(q\),
\[
\operatorname{projection}(q)=\operatorname{projectionPoint}_C(q).
\]
This makes it possible to use standard facts about the canonical projection onto a closed convex set, such as continuity and nonexpansiveness.

Next, it proves the pointwise dissipation inequality: for every \(t\ge 0\) with \(x(t)\in C\),
\[
\mu\,\frac{d}{dt}\Psi(x(t))+\|x'(t)\|^2\le 0.
\]
This follows from the lemma `projection_gradient_objective_dissipation`, using convexity of \(\Psi\), the metric projection property, and the derivative formula for \(x\). The command `simpa only [(hclassical t ht).deriv]` is used to replace the derivative \(x'(t)\) by the expression
\[
\operatorname{projection}(x(t)-\mu\nabla\Psi(x(t)))-x(t).
\]

The proof then shows that the trajectory remains in \(C\). Let
\[
p(s)=\operatorname{projection}\bigl(x(s)-\mu\nabla\Psi(x(s))\bigr).
\]
The map \(p\) is continuous on finite intervals because \(x\) is differentiable, the gradient is continuous, and the canonical projection is continuous. The proof uses `relaxed_projection_variation_of_constants` to express the solution of the differential equation
\[
x'(s)+x(s)=p(s)
\]
and then applies `relaxed_projection_variation_mem_closed_convex` to conclude \(x(t)\in C\) for all \(t\ge 0\). The initial condition \(x(0)\in C\) is essential here.

Using the chain rule and the gradient property, the proof shows that
\[
\frac{d}{dt}\Psi(x(t))
=
\left\langle \nabla\Psi(x(t)),\,
\operatorname{projection}(x(t)-\mu\nabla\Psi(x(t)))-x(t)
\right\rangle.
\]
Then it proves that \(t\mapsto \Psi(x(t))\) is antitone on \([0,\infty)\) by applying `antitoneOn_of_deriv_nonpos`. The derivative is nonpositive because from the pointwise dissipation inequality,
\[
\mu\frac{d}{dt}\Psi(x(t))+\|x'(t)\|^2\le 0,
\]
and since \(\mu>0\) and \(\|x'(t)\|^2\ge 0\), it follows that
\[
\frac{d}{dt}\Psi(x(t))\le 0.
\]
The proof also obtains the almost-everywhere dissipation inequality by restricting to \([0,\infty)\) and using `filter_upwards` with the fact that \([0,\infty)\) is almost all of the restricted measure.

Let \(z_0\in S\). Then \(z_0\in C\) and \(z_0\) minimizes \(\Psi\) on \(C\). The proof shows
\[
\inf_{y\in C}\Psi(y)=\Psi(z_0)
\]
using `csInf_eq_of_forall_ge_of_forall_gt_exists_lt`: every value in \(\Psi(C)\) is at least \(\Psi(z_0)\), and \(\Psi(z_0)\) itself realizes the infimum.

Define the shifted objective
\[
G(t)=\Psi(x(t))-\Psi(z_0)
\]
and the Lyapunov energy
\[
E(t)=\frac12\|x(t)-z_0\|^2+\mu G(t).
\]
Since \(z_0\) minimizes \(\Psi\) on \(C\), one has \(G(t)\ge 0\) for \(t\ge 0\).

The proof computes the derivative of \(E\). With
\[
F(t)=\operatorname{projection}(x(t)-\mu\nabla\Psi(x(t)))-x(t),
\]
it shows that
\[
E'(t)
=
\langle F(t),x(t)-z_0\rangle
+
\mu\langle \nabla\Psi(x(t)),F(t)\rangle.
\]
Using the lemma `projection_gradient_energy_deriv`, it obtains the energy dissipation inequality
\[
E'(t)+\|x'(t)\|^2+\mu G(t)\le 0.
\]
Since the last two nonnegative terms are nonnegative, this implies \(E'(t)\le 0\), so \(E\) is nonincreasing on \([0,\infty)\). Since \(E\) is also nonnegative, it has a finite limit at infinity by `tendsto_of_antitone_nonneg_on_Ici_local`.

The proof then establishes an integral bound:
\[
\int_0^T \mu G(t)\,dt \le E(0)
\]
for all \(T\ge 0\). This uses the finite-interval dissipation lemma `energy_dissipation_interval_bound_local`. Because \(G\) is nonincreasing, \(G(t)\le G(0)\)? Actually, since \(G\) is nonincreasing, for \(t\le T\),
\[
G(T)\le G(t).
\]
Therefore,
\[
T\mu G(T)\le \int_0^T \mu G(t)\,dt\le E(0),
\]
so
\[
G(T)\le \frac{E(0)}{\mu T}.
\]
Letting \(T\to\infty\), the squeeze theorem gives \(G(T)\to 0\). Hence
\[
\Psi(x(t))\to \Psi(z_0)=\inf_{y\in C}\Psi(y).
\]
In Lean, this is done using `squeeze_zero'` and the fact that
\[
\frac{E(0)}{\mu T}\to 0.
\]

To obtain weak convergence, the proof uses the Opial lemma. It first proves that for every \(z\in S\), the distance \(\|x(t)-z\|\) has a limit as \(t\to\infty\). For such \(z\), one has \(\Psi(z)=\Psi(z_0)\). Define
\[
E_z(t)=\frac12\|x(t)-z\|^2+\mu G(t).
\]
The same energy estimate shows that \(E_z\) is nonincreasing and nonnegative, hence converges. Since \(G(t)\to 0\), the squared distance
\[
\|x(t)-z\|^2
\]
also converges, and therefore \(\|x(t)-z\|\) converges.

It remains to show that every weak cluster point of the trajectory is a minimizer in \(S\). Suppose
\[
x(u_n)\rightharpoonup z
\]
weakly along times \(u_n\to\infty\). Since \(C\) is closed and convex, its weak image is weakly closed, and because \(x(u_n)\in C\), the weak limit satisfies \(z\in C\).

To prove optimality, suppose toward contradiction that \(\Psi(z_0)<\Psi(z)\). Let
\[
\varepsilon=\frac{\Psi(z)-\Psi(z_0)}{2},
\]
and define the sublevel set
\[
L=\{y\in H:\Psi(y)\le \Psi(z_0)+\varepsilon\}.
\]
Because \(\Psi\) is convex and continuous, \(L\) is closed and convex, so its weak image is weakly closed. Since
\[
\Psi(x(u_n))\to \Psi(z_0)<\Psi(z_0)+\varepsilon,
\]
eventually \(x(u_n)\in L\). Hence the weak limit \(z\) must also lie in \(L\), so
\[
\Psi(z)\le \Psi(z_0)+\varepsilon
= \Psi(z_0)+\frac{\Psi(z)-\Psi(z_0)}{2}.
\]
This implies \(\Psi(z)\le \Psi(z_0)\), contradicting \(\Psi(z_0)<\Psi(z)\). Therefore \(\Psi(z)\le \Psi(z_0)\). Since \(z_0\) minimizes \(\Psi\) on \(C\), this gives \(\Psi(z)=\Psi(z_0)\), and hence \(z\in S\).

Finally, the lemma `opial_trajectory_lemma` combines the facts that \(S\) is nonempty, every point in \(S\) has a converging distance to the trajectory, and every weak cluster point lies in \(S\). It yields a single \(z\in S\) such that \(x(t)\to z\) weakly. The proof then assembles all five conclusions:
- weak convergence to \(z\in S\),
- feasibility \(x(t)\in C\) for all \(t\ge 0\),
- monotonicity of \(\Psi(x(t))\),
- convergence of \(\Psi(x(t))\) to the infimum on \(C\),
- the almost-everywhere dissipation inequality.

Important Lean commands used in the proof include:
- `have` for intermediate results,
- `rw` and `simpa` for rewriting and simplifying using definitions or derivatives,
- `exact` and `apply` for supplying proofs or applying lemmas,
- `nlinarith` for arithmetic and nonlinear inequality reasoning,
- `filter_upwards` for proving eventually or almost-everywhere properties,
- `antitoneOn_of_deriv_nonpos` for deducing monotonicity from derivative signs,
- `tendsto_of_antitone_nonneg_on_Ici_local` for convergence of monotone nonnegative functions,
- `squeeze_zero'` for the limit \(G(t)\to 0\),
- `opial_trajectory_lemma` for weak convergence.

