## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/thm_1.lean`

## Lean statement
```lean
theorem theorem1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) :
    Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds (sInf (Set.range Θ))) ∧
    (((Optimization.argminSet Θ).Nonempty ∧
        ((∃ q, Optimization.argminSet Θ = {q}) ∨
          (∃ phiReal : H → ℝ, (∀ x, phi x = (phiReal x : EReal)) ∧ Differentiable ℝ phiReal ∧
            (∃ gradPhi : H → H, (∀ x h, fderiv ℝ phiReal x h = inner ℝ (gradPhi x) h) ∧
              IsWeakToWeakSequentiallyContinuous gradPhi)) ∨
          IsWeakToWeakSequentiallyContinuous gradPsi ∨
          Convex ℝ (ERealFunction.epigraph fun x ↦ (psi x : EReal)))) →
      (∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
        (nhds (toWeakSpace ℝ H q)))) ∧
    (Optimization.argminSet Θ = ∅ → Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop Filter.atTop)
```

## Statement explanation
The declaration `theorem1` is stated for a real Hilbert space $H$, i.e. a complete real inner-product space. The data are two extended-real functions $\phi,\Theta:H\to\overline{\mathbb R}$ (Lean type `EReal`), a real-valued function $\psi:H\to\mathbb R$, a map $\mathrm{gradPsi}:H\to H$, real parameters $a,b,\lambda,L_\psi$, and two sequences $u,y:\mathbb N\to H$. The hypothesis `hH` has type `IFBHypothesis phi Θ psi gradPsi a b lam Lpsi` and packages the standing assumptions of the inertial forward-backward problem; the hypothesis `hIFB` has type `IsIFBTrajectory phi psi gradPsi a b lam u y` and says that $(u,y)$ is a trajectory of that method. In the proof the parts of `hH` that are used are that $a\gt 0$, $b\gt 0$, $\lambda\gt 0$, that $\phi$ and $\Theta$ have convex epigraphs, that $\Theta=\phi+\psi$, that $\psi$ is differentiable with gradient $\mathrm{gradPsi}$, and that $\phi$ is proper. The conclusion is a conjunction of three assertions.

First, the objective values converge to the infimum of the objective:

```math
\Theta(u_k)\longrightarrow \inf\{\Theta(x):x\in H\}
```

in $\overline{\mathbb R}$ as $k\to\infty$. Here $\inf$ is written `sInf (Set.range Θ)`.

Second, suppose that the minimizer set

```math
S=\mathrm{argmin}\Theta=\{x\in H:\forall y\in H,\ \Theta(x)\le \Theta(y)\}
```

is nonempty and that at least one of four structural alternatives holds:
- $S$ is a singleton;
- $\phi$ is actually real-valued, say $\phi(x)=(\phi_{\mathbb R}(x):\overline{\mathbb R})$, with $\phi_{\mathbb R}:H\to\mathbb R$ differentiable and admitting a gradient field $g:H\to H$ satisfying $D\phi_{\mathbb R}(x)h=\langle g(x),h\rangle$, and this $g$ is weak-to-weak sequentially continuous;
- the given map `gradPsi` is weak-to-weak sequentially continuous;
- the epigraph of the extended-real function $x\mapsto(\psi(x):\overline{\mathbb R})$,

```math
\{(x,\xi)\in H\times\mathbb R:(\psi(x):\overline{\mathbb R})\le \xi\},
```

  is convex.
Under these assumptions, the theorem asserts that there exists $q\in S$ such that

$$
u_k\rightharpoonup q
$$

weakly in $H$.

Third, if the minimizer set is empty, then

```math
\|u_k\|\longrightarrow +\infty.
```

## Lean proof
```lean
by
  rcases proposition6 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨hobjective, hcluster, hempty⟩
  refine ⟨hobjective, ?_, hempty⟩
  rintro ⟨hS, hcase⟩
  -- The imported Proposition 8 has a malformed exported type: its final
  -- proof-index argument of `liapunovF` was erased.  A local reconstruction
  -- is therefore needed before this common boundedness package is available.
  have hbounded : Bornology.IsBounded (Set.range u) := by
    exact (theorem1_proposition8_local phi Θ psi gradPsi u y a b lam Lpsi hH hIFB hS).1
  have hFlim : ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => liapunovF u y a b lam q (k + 1) (by omega))
        Filter.atTop (nhds l) :=
    (theorem1_proposition8_local phi Θ psi gradPsi u y a b lam Lpsi hH hIFB hS).2
  have hAlim : ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => theorem1AuxiliaryA u y a b lam q k)
        Filter.atTop (nhds l) := by
    intro q hq
    exact theorem1_auxiliaryA_tendsto phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
      hbounded hFlim hq
  rcases hcase with hsingle | hphi | hgrad | hpsi
  · rcases hsingle with ⟨q0, hsingle⟩
    have hunique : ∀ p q : H,
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) → p = q := by
      intro p q hp hq
      have hpS : p ∈ ({q0} : Set H) := by simpa [hsingle] using hcluster p hp
      have hqS : q ∈ ({q0} : Set H) := by simpa [hsingle] using hcluster q hq
      exact (Set.mem_singleton_iff.mp hpS).trans (Set.mem_singleton_iff.mp hqS).symm
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with ⟨q, hq⟩
    have hqcluster : IsSequentialClusterPt
        (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) :=
      ⟨id, strictMono_id, by simpa using hq⟩
    exact ⟨q, hcluster q hqcluster, hq⟩
  · rcases hphi with ⟨phiReal, hphi, hdiff, gradPhi, hgradPhi, hgradWeak⟩
    have hsubgradient_eq (x g : H) (hg : g ∈ subdifferential phi x) :
        g = gradPhi x := by
      have hmin : IsMinOn (fun z : H => phiReal z - inner ℝ g z) Set.univ x := by
        intro z hz
        change phiReal x - inner ℝ g x ≤ phiReal z - inner ℝ g z
        have hs := hg z
        rw [hphi x, hphi z] at hs
        have hsreal : inner ℝ (z - x) g + phiReal x ≤ phiReal z := by
          apply EReal.coe_le_coe_iff.mp
          simpa using hs
        rw [inner_sub_left] at hsreal
        rw [real_inner_comm z g, real_inner_comm x g]
        linarith
      have hx : HasFDerivAt phiReal (fderiv ℝ phiReal x) x := (hdiff x).hasFDerivAt
      have hinner : HasFDerivAt (fun z : H => inner ℝ g z) (innerSL ℝ g) x :=
        (innerSL ℝ g).hasFDerivAt
      have hzero := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero (hx.sub hinner)
      have hmaps : fderiv ℝ phiReal x = innerSL ℝ g := sub_eq_zero.mp hzero
      have hd := congrArg (fun L : H →L[ℝ] ℝ => L (gradPhi x - g)) hmaps
      change (fderiv ℝ phiReal x) (gradPhi x - g) =
        inner ℝ g (gradPhi x - g) at hd
      rw [hgradPhi x (gradPhi x - g)] at hd
      have hnorm : ‖g - gradPhi x‖ ^ 2 = 0 := by
        rw [norm_sub_rev, ← real_inner_self_eq_norm_sq (gradPhi x - g), inner_sub_left]
        exact sub_eq_zero.mpr hd
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
    have hvel := theorem1_velocity_tendsto_zero phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
    have hunique : ∀ p q : H,
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) → p = q := by
      intro p q hp hq
      rcases hp with ⟨t, htmono, ht⟩
      rcases hq with ⟨s, hsmono, hs⟩
      have hpS : p ∈ Optimization.argminSet Θ := hcluster p ⟨t, htmono, ht⟩
      have hqS : q ∈ Optimization.argminSet Θ := hcluster q ⟨s, hsmono, hs⟩
      rcases hAlim p hpS with ⟨lp, hlp⟩
      rcases hAlim q hqS with ⟨lq, hlq⟩
      have htTop : Filter.Tendsto t Filter.atTop Filter.atTop := htmono.tendsto_atTop
      have hsTop : Filter.Tendsto s Filter.atTop Filter.atTop := hsmono.tendsto_atTop
      have ht2 := theorem1_shift_two_weakly u t p hvel htTop (by simpa [Function.comp_def] using ht)
      have hs2 := theorem1_shift_two_weakly u s q hvel hsTop (by simpa [Function.comp_def] using hs)
      have hAtp := hlp.comp htTop
      have hAsp := hlp.comp hsTop
      have hAtq := hlq.comp htTop
      have hAsq := hlq.comp hsTop
      have hleft := ((hAtp.sub hAsp).sub hAtq).add hAsq
      have hgradt := hgradWeak (fun j => u (t j + 2)) p ht2
      have hgrads := hgradWeak (fun j => u (s j + 2)) q hs2
      have hzinner : Filter.Tendsto (fun j => inner ℝ
          (zSequence u y a b lam (t j + 2) (by omega) -
            zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds (inner ℝ (gradPhi p - gradPhi q) (p - q))) := by
        have hgradt' := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 hgradt (q - p)
        have hgrads' := (weakConvergence_iff_forall_tendsto_inner_right _ _).1 hgrads (q - p)
        have hinner := (hgradt'.sub hgrads').neg
        convert hinner using 1
        · ext j
          rw [← hsubgradient_eq (u (t j + 2))
              (-zSequence u y a b lam (t j + 2) (by omega))
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                (t j + 2) (by omega)),
            ← hsubgradient_eq (u (s j + 2))
              (-zSequence u y a b lam (s j + 2) (by omega))
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                (s j + 2) (by omega))]
          simp only [neg_sub_neg, inner_neg_left]
          simp only [inner_sub_left]
          ring
        · simp only [inner_sub_left, inner_sub_right]
          ring
      have hconv : ConvexOn ℝ Set.univ phiReal := by
        apply convexOn_of_convex_epigraph
        simpa [ERealFunction.epigraph, hphi] using hH.phi_convex
      have hsupport : ∀ x z : H,
          phiReal x - phiReal z ≤ inner ℝ (gradPhi x) (x - z) := by
        intro x z
        let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z x
        have hline : HasDerivAt line (x - z) 1 := by
          convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - z)).add_const z using 1 <;> simp
        have hc : ConvexOn ℝ Set.univ (phiReal ∘ line) := by
          simpa [line] using hconv.comp_affineMap line
        have hd : HasDerivAt (phiReal ∘ line) (inner ℝ (gradPhi x) (x - z)) 1 := by
          have hx : HasFDerivAt phiReal (fderiv ℝ phiReal x) (line 1) := by
            simpa [line] using (hdiff x).hasFDerivAt
          have hcomp := hx.comp_hasDerivAt 1 hline
          simpa [line, hgradPhi x, innerSL_apply_apply] using hcomp
        have hslope := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
          (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hd
        simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
          AffineMap.lineMap_apply_one] using hslope
      have hgrad_nonneg : 0 ≤ inner ℝ (gradPhi p - gradPhi q) (p - q) := by
        have hpq := hsupport p q
        have hqp := hsupport q p
        rw [show q - p = -(p - q) by abel, inner_neg_right] at hqp
        rw [inner_sub_left]
        linarith
      have hcoef : 0 < (a + b) / lam := div_pos (by linarith [hH.a_pos, hH.b_pos]) hH.step_pos
      have hzcoef : 0 < 1 / lam + b := by
        nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
      have hidentity : Filter.Tendsto (fun j =>
          ((a + b) / lam) * inner ℝ (u (t j + 1) - u (s j + 1)) (q - p) -
            (1 / lam + b) * inner ℝ
              (zSequence u y a b lam (t j + 2) (by omega) -
                zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds 0) := by
        convert hleft using 1
        · ext j
          exact (auxiliaryA_four_term u y a b lam p q (t j) (s j)).symm
        · simp
      have ht1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H p)) := by
        have ht' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j))) Filter.atTop
            (nhds (toWeakSpace ℝ H p)) := by simpa [Function.comp_def] using ht
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (t j + 1) - u (t j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp htTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (t j + 1) - u (t j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (ht' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have hs1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H q)) := by
        have hs' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j))) Filter.atTop
            (nhds (toWeakSpace ℝ H q)) := by simpa [Function.comp_def] using hs
        rw [weakConvergence_iff_forall_tendsto_inner_right] at hs' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (s j + 1) - u (s j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp hsTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (s j + 1) - u (s j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (hs' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have huinner : Filter.Tendsto (fun j =>
          inner ℝ (u (t j + 1) - u (s j + 1)) (q - p)) Filter.atTop
          (nhds (-‖p - q‖ ^ 2)) := by
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht1 hs1
        have hinner := ((ht1 (q - p)).sub (hs1 (q - p)))
        convert hinner using 1
        · ext j
          simp [inner_sub_left]
        · rw [← real_inner_self_eq_norm_sq (p - q)]
          simp only [inner_sub_left, inner_sub_right]
          ring_nf
      have hcombined :=
        (huinner.const_mul ((a + b) / lam)).sub
          (hzinner.const_mul (1 / lam + b))
      have heq : (0 : ℝ) = ((a + b) / lam) * (-‖p - q‖ ^ 2) -
          (1 / lam + b) * inner ℝ (gradPhi p - gradPhi q) (p - q) :=
        tendsto_nhds_unique hidentity hcombined
      have hnormzero : ‖p - q‖ = 0 := by
        have hfirst : 0 ≤ ((a + b) / lam) * ‖p - q‖ ^ 2 :=
          mul_nonneg hcoef.le (sq_nonneg _)
        have hsecond : 0 ≤ (1 / lam + b) * inner ℝ (gradPhi p - gradPhi q) (p - q) :=
          mul_nonneg hzcoef.le hgrad_nonneg
        have hz : ((a + b) / lam) * ‖p - q‖ ^ 2 = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left hcoef.ne' |> sq_eq_zero_iff.mp
      exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with ⟨q, hq⟩
    have hqcluster : IsSequentialClusterPt
        (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) :=
      ⟨id, strictMono_id, by simpa using hq⟩
    exact ⟨q, hcluster q hqcluster, hq⟩
  · have hvel := theorem1_velocity_tendsto_zero phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
    have hresidual_inner (q : H) (hq : q ∈ Optimization.argminSet Θ) :
        Filter.Tendsto (fun k : ℕ => inner ℝ
          (zSequence u y a b lam (k + 2) (by omega) - gradPsi (u (k + 2)))
          (u (k + 2) - q)) Filter.atTop (nhds 0) := by
      rcases hFlim q hq with ⟨l, hl⟩
      have hl' := theorem1_liapunov_shift_tendsto u y a b lam q l hl 1
      have hdiff := hl'.sub hl
      have hb : b ≠ 0 := ne_of_gt hH.b_pos
      have hscaled := hdiff.const_mul (1 / b)
      convert hscaled using 1
      · ext k
        have hinc := (theorem1_proposition3_local phi Θ psi gradPsi u y a b lam Lpsi q
          (k + 1) hH hIFB (by omega) hH.theta_convex).2.1
        calc
          inner ℝ
              (zSequence u y a b lam (k + 2) (by omega) - gradPsi (u (k + 2)))
              (u (k + 2) - q) =
              inner ℝ ((1 / lam - a) • velocity u (k + 2) (by omega) +
                (1 / lam + b) • zeta y (k + 2) (by omega)) (u (k + 2) - q) := by
                rw [theorem1_residual_vector phi psi gradPsi a b lam u y hIFB k]
          _ = (1 / b) * (liapunovF u y a b lam q (k + 1 + 1) (by omega) -
                liapunovF u y a b lam q (k + 1) (by omega)) := by
                rw [← hinc]
                field_simp [hb]
      · simp
    have hunique : ∀ p q : H,
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H p) →
        IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) → p = q := by
      intro p q hp hq
      rcases hp with ⟨t, htmono, ht⟩
      rcases hq with ⟨s, hsmono, hs⟩
      have hpS : p ∈ Optimization.argminSet Θ := hcluster p ⟨t, htmono, ht⟩
      have hqS : q ∈ Optimization.argminSet Θ := hcluster q ⟨s, hsmono, hs⟩
      rcases hAlim p hpS with ⟨lp, hlp⟩
      rcases hAlim q hqS with ⟨lq, hlq⟩
      have htTop : Filter.Tendsto t Filter.atTop Filter.atTop := htmono.tendsto_atTop
      have hsTop : Filter.Tendsto s Filter.atTop Filter.atTop := hsmono.tendsto_atTop
      have ht2 := theorem1_shift_two_weakly u t p hvel htTop
        (by simpa [Function.comp_def] using ht)
      have hs2 := theorem1_shift_two_weakly u s q hvel hsTop
        (by simpa [Function.comp_def] using hs)
      have hAtp := hlp.comp htTop
      have hAsp := hlp.comp hsTop
      have hAtq := hlq.comp htTop
      have hAsq := hlq.comp hsTop
      have hleft := ((hAtp.sub hAsp).sub hAtq).add hAsq
      have hidentity : Filter.Tendsto (fun j =>
          ((a + b) / lam) * inner ℝ (u (t j + 1) - u (s j + 1)) (q - p) -
            (1 / lam + b) * inner ℝ
              (zSequence u y a b lam (t j + 2) (by omega) -
                zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds 0) := by
        convert hleft using 1
        · ext j
          exact (auxiliaryA_four_term u y a b lam p q (t j) (s j)).symm
        · simp
      have ht1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H p)) := by
        have ht' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (t j))) Filter.atTop
            (nhds (toWeakSpace ℝ H p)) := by simpa [Function.comp_def] using ht
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (t j + 1) - u (t j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp htTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (t j + 1) - u (t j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (ht' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have hs1 : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j + 1))) Filter.atTop
          (nhds (toWeakSpace ℝ H q)) := by
        have hs' : Filter.Tendsto (fun j ↦ toWeakSpace ℝ H (u (s j))) Filter.atTop
            (nhds (toWeakSpace ℝ H q)) := by simpa [Function.comp_def] using hs
        rw [weakConvergence_iff_forall_tendsto_inner_right] at hs' ⊢
        intro v
        have hstep : Filter.Tendsto (fun j ↦ u (s j + 1) - u (s j))
            Filter.atTop (nhds 0) := by simpa using hvel.comp hsTop
        have hinner : Filter.Tendsto (fun j ↦ inner ℝ (u (s j + 1) - u (s j)) v)
            Filter.atTop (nhds 0) := by
          let f : H → ℝ := fun x ↦ inner ℝ x v
          have hf : Continuous f := continuous_inner.comp (continuous_id.prodMk continuous_const)
          simpa [f] using (hf.tendsto 0).comp hstep
        convert (hs' v).add hinner using 1 <;> simp [inner_add_left, sub_eq_add_neg]
      have huinner : Filter.Tendsto (fun j =>
          inner ℝ (u (t j + 1) - u (s j + 1)) (q - p)) Filter.atTop
          (nhds (-‖p - q‖ ^ 2)) := by
        rw [weakConvergence_iff_forall_tendsto_inner_right] at ht1 hs1
        have hinner := ((ht1 (q - p)).sub (hs1 (q - p)))
        convert hinner using 1
        · ext j
          simp [inner_sub_left]
        · rw [← real_inner_self_eq_norm_sq (p - q)]
          simp only [inner_sub_left, inner_sub_right]
          ring_nf
      have hrtp := (hresidual_inner p hpS).comp htTop
      have hrsp := (hresidual_inner p hpS).comp hsTop
      have hrtq := (hresidual_inner q hqS).comp htTop
      have hrsq := (hresidual_inner q hqS).comp hsTop
      have hresfour := ((hrtp.sub hrsp).sub hrtq).add hrsq
      have hgradt := hgrad (fun j => u (t j + 2)) p ht2
      have hgrads := hgrad (fun j => u (s j + 2)) q hs2
      have hgradinner : Filter.Tendsto (fun j => inner ℝ
          (gradPsi (u (t j + 2)) - gradPsi (u (s j + 2))) (q - p))
          Filter.atTop (nhds (inner ℝ (gradPsi p - gradPsi q) (q - p))) := by
        rw [weakConvergence_iff_forall_tendsto_inner_right] at hgradt hgrads
        convert (hgradt (q - p)).sub (hgrads (q - p)) using 1 <;>
          simp [inner_sub_left]
      have hzinner : Filter.Tendsto (fun j => inner ℝ
          (zSequence u y a b lam (t j + 2) (by omega) -
            zSequence u y a b lam (s j + 2) (by omega)) (q - p))
          Filter.atTop (nhds (inner ℝ (gradPsi p - gradPsi q) (q - p))) := by
        have hsum := hgradinner.add hresfour
        convert hsum using 1
        · ext j
          simp only [Function.comp_apply, inner_sub_left, inner_sub_right, Nat.add_comm]
          ring
        · simp
      have hcombined :=
        (huinner.const_mul ((a + b) / lam)).sub
          (hzinner.const_mul (1 / lam + b))
      have heq : (0 : ℝ) = ((a + b) / lam) * (-‖p - q‖ ^ 2) -
          (1 / lam + b) * inner ℝ (gradPsi p - gradPsi q) (q - p) :=
        tendsto_nhds_unique hidentity hcombined
      have hminimizer_subgradient (x : H) (hx : x ∈ Optimization.argminSet Θ) :
          -gradPsi x ∈ subdifferential phi x := by
        intro z
        by_cases hz_top : phi z = ⊤
        · rw [hz_top]
          exact le_top
        have hx_top : phi x ≠ ⊤ := by
          have hxdom := minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hx
          exact (ERealFunction.mem_dom_iff phi x).mp hxdom |>.ne
        have hx_bot : phi x ≠ ⊥ := hH.phi_proper.1 x
        have hz_bot : phi z ≠ ⊥ := hH.phi_proper.1 z
        let d : H := z - x
        let X : ℝ := (phi x).toReal
        let Z : ℝ := (phi z).toReal
        let P : ℝ → ℝ := fun t => psi (x + t • d)
        have hxE : phi x = (X : EReal) := by
          symm
          exact EReal.coe_toReal hx_top hx_bot
        have hzE : phi z = (Z : EReal) := by
          symm
          exact EReal.coe_toReal hz_top hz_bot
        have hchord : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            (phi (x + t • d)).toReal ≤ (1 - t) * X + t * Z := by
          intro t ht0 ht1
          have hxepi : (x, X) ∈ ERealFunction.epigraph phi := by
            rw [ERealFunction.mem_epigraph_iff, hxE]
          have hzepi : (z, Z) ∈ ERealFunction.epigraph phi := by
            rw [ERealFunction.mem_epigraph_iff, hzE]
          have hcomb := hH.phi_convex hxepi hzepi (by linarith) ht0 (by ring : (1 - t) + t = 1)
          change ((1 - t) • x + t • z, (1 - t) * X + t * Z) ∈
            ERealFunction.epigraph phi at hcomb
          rw [show (1 - t) • x + t • z = x + t • d by dsimp [d]; module,
            ERealFunction.mem_epigraph_iff] at hcomb
          have hpoint_top : phi (x + t • d) ≠ ⊤ := by
            intro htop
            rw [htop] at hcomb
            exact (EReal.coe_ne_top _ ) (top_unique hcomb)
          exact EReal.toReal_le_toReal hcomb (hH.phi_proper.1 _) (EReal.coe_ne_top _)
        have hquot : ∀ t : ℝ, 0 < t → t < 1 →
            -(P t - P 0) / t ≤ Z - X := by
          intro t ht ht1
          have hmin := (Optimization.mem_argminSet_iff Θ x).mp hx (x + t • d)
          have hpoint_top : phi (x + t • d) ≠ ⊤ := by
            have hxepi : (x, X) ∈ ERealFunction.epigraph phi := by
              rw [ERealFunction.mem_epigraph_iff, hxE]
            have hzepi : (z, Z) ∈ ERealFunction.epigraph phi := by
              rw [ERealFunction.mem_epigraph_iff, hzE]
            have hupper := hH.phi_convex hxepi hzepi (by linarith) ht.le
              (by ring : (1 - t) + t = 1)
            change ((1 - t) • x + t • z, (1 - t) * X + t * Z) ∈
              ERealFunction.epigraph phi at hupper
            rw [show (1 - t) • x + t • z = x + t • d by dsimp [d]; module,
              ERealFunction.mem_epigraph_iff] at hupper
            intro htop
            rw [htop] at hupper
            exact (EReal.coe_ne_top _) (top_unique hupper)
          have htheta_x : Θ x = ((X + P 0 : ℝ) : EReal) := by
            rw [hH.theta_eq, hxE]
            simp [P]
          have htheta_point : Θ (x + t • d) =
              (((phi (x + t • d)).toReal + P t : ℝ) : EReal) := by
            rw [hH.theta_eq]
            rw [← EReal.coe_toReal hpoint_top (hH.phi_proper.1 _)]
            simp [P]
          rw [htheta_x, htheta_point] at hmin
          have hreal := EReal.coe_le_coe_iff.mp hmin
          have hphi := hchord t ht.le ht1.le
          have htne : t ≠ 0 := ne_of_gt ht
          apply (div_le_iff₀ ht).2
          linarith [hphi]
        have hPderiv : HasDerivAt P (inner ℝ (gradPsi x) d) 0 := by
          exact hasDerivAt_line_restrict_local psi gradPsi x d hH.psi_differentiable
            hH.psi_gradient
        have hslope : Filter.Tendsto (fun t : ℝ => -(P t - P 0) / t)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (-inner ℝ (gradPsi x) d)) := by
          have ht := hPderiv.tendsto_slope_zero_right.neg
          convert ht using 1
          · ext t
            simp [slope, div_eq_mul_inv]
            ring
        have hevent : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
            -(P t - P 0) / t ≤ Z - X := by
          have hlt : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
          filter_upwards [self_mem_nhdsWithin, hlt] with t htpos htone
          exact hquot t htpos htone
        have hlim := le_of_tendsto hslope hevent
        rw [hxE, hzE]
        norm_cast
        dsimp [d, X, Z] at hlim ⊢
        have hreal : inner ℝ (z - x) (-gradPsi x) + (phi x).toReal ≤
            (phi z).toReal := by
          rw [inner_neg_right, real_inner_comm]
          linarith [hlim]
        simpa using (EReal.coe_le_coe_iff.mpr hreal)
      have hp_sub := hminimizer_subgradient p hpS
      have hq_sub := hminimizer_subgradient q hqS
      have hmono := (isMonotone_subdifferential phi hH.phi_proper)
        (-gradPsi p) hp_sub (-gradPsi q) hq_sub
      have hgrad_nonpos : inner ℝ (gradPsi p - gradPsi q) (q - p) ≥ 0 := by
        calc
          0 ≤ inner ℝ ((-gradPsi p) - (-gradPsi q)) (p - q) := hmono
          _ = inner ℝ (gradPsi p - gradPsi q) (q - p) := by
            simp only [inner_sub_left, inner_sub_right, inner_neg_left]
            ring
      have hcoef : 0 < (a + b) / lam :=
        div_pos (by linarith [hH.a_pos, hH.b_pos]) hH.step_pos
      have hzcoef : 0 < 1 / lam + b := by
        nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
      have hnormzero : ‖p - q‖ = 0 := by
        have hfirst : 0 ≤ ((a + b) / lam) * ‖p - q‖ ^ 2 :=
          mul_nonneg hcoef.le (sq_nonneg _)
        have hsecond : 0 ≤ (1 / lam + b) * inner ℝ (gradPsi p - gradPsi q) (q - p) :=
          mul_nonneg hzcoef.le hgrad_nonpos
        have hz : ((a + b) / lam) * ‖p - q‖ ^ 2 = 0 := by linarith
        exact (mul_eq_zero.mp hz).resolve_left hcoef.ne' |> sq_eq_zero_iff.mp
      exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
    rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint u).2
        ⟨hbounded, hunique⟩ with ⟨q, hq⟩
    have hqcluster : IsSequentialClusterPt
        (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) :=
      ⟨id, strictMono_id, by simpa using hq⟩
    exact ⟨q, hcluster q hqcluster, hq⟩
  · have hpsiConv : ConvexOn ℝ Set.univ psi := by
      apply convexOn_of_convex_epigraph
      simpa [ERealFunction.epigraph] using hpsi
    have hpsiSupport : ∀ x z : H,
        psi x - psi z ≤ inner ℝ (gradPsi x) (x - z) := by
      intro x z
      let line : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z x
      have hline : HasDerivAt line (x - z) 1 := by
        convert ((hasDerivAt_id (𝕜 := ℝ) 1).smul_const (x - z)).add_const z using 1 <;> simp
      have hc : ConvexOn ℝ Set.univ (psi ∘ line) := by
        simpa [line] using hpsiConv.comp_affineMap line
      have hd : HasDerivAt (psi ∘ line) (inner ℝ (gradPsi x) (x - z)) 1 := by
        have hx : HasFDerivAt psi (fderiv ℝ psi x) (line 1) := by
          simpa [line] using hH.psi_differentiable x |>.hasFDerivAt
        have hcomp := hx.comp_hasDerivAt 1 hline
        simpa [line, hH.psi_gradient x, innerSL_apply_apply] using hcomp
      have hslope := hc.slope_le_of_hasDerivAt (show (0 : ℝ) ∈ Set.univ by simp)
        (show (1 : ℝ) ∈ Set.univ by simp) zero_lt_one hd
      simpa [slope_def_field, line, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using hslope
    have hphiFinite (j : ℕ) (hj : 1 ≤ j) : phi (u j) ≠ ⊤ ∧ phi (u j) ≠ ⊥ := by
      have hz := theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB j hj
      constructor
      · exact subgradient_value_ne_top hH.phi_proper hz
      · exact hH.phi_proper.1 _
    have hGtel (q : H) (hq : q ∈ Optimization.argminSet Θ) :
        ∀ n m : ℕ, ∀ hn : 2 ≤ n, ∀ hnm : n ≤ m,
          auxiliaryG u y a b lam q n hn -
              auxiliaryG u y a b lam q m (le_trans hn hnm) -
              inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q) ≤
            (phi q).toReal - (phi (u m)).toReal := by
      intro n m hn hnm
      have hqtop : phi q ≠ ⊤ :=
        (ERealFunction.mem_dom_iff phi q).mp
          (minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq) |>.ne
      induction m, hnm using Nat.le_induction with
      | base =>
          have hs : phi (u n) +
              (inner ℝ (q - u n) (-zSequence u y a b lam n (by omega)) : EReal) ≤
                phi q := by
            simpa [add_comm] using
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                n (by omega)) q
          have hleftbot : phi (u n) +
              (inner ℝ (q - u n) (-zSequence u y a b lam n (by omega)) : EReal) ≠ ⊥ :=
            EReal.add_ne_bot_iff.mpr ⟨(hphiFinite n (by omega)).2, EReal.coe_ne_bot _⟩
          have hsreal := EReal.toReal_le_toReal hs hleftbot hqtop
          rw [EReal.toReal_add (hphiFinite n (by omega)).1 (hphiFinite n (by omega)).2
            (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsreal
          norm_num at hsreal
          rw [show q - u n = -(u n - q) by abel, inner_neg_left,
            real_inner_comm (zSequence u y a b lam n (by omega)) (u n - q)] at hsreal
          simp only [inner_neg_left]
          linarith
      | succ m hnm ih =>
          have hm : 2 ≤ m := le_trans hn hnm
          have hs : phi (u (m + 1)) +
              (inner ℝ (u m - u (m + 1))
                (-zSequence u y a b lam (m + 1) (by omega)) : EReal) ≤ phi (u m) := by
            simpa [add_comm] using
              (theorem1_neg_z_mem_subgradient phi psi gradPsi a b lam u y hIFB
                (m + 1) (by omega)) (u m)
          have hleftbot : phi (u (m + 1)) +
              (inner ℝ (u m - u (m + 1))
                (-zSequence u y a b lam (m + 1) (by omega)) : EReal) ≠ ⊥ :=
            EReal.add_ne_bot_iff.mpr
              ⟨(hphiFinite (m + 1) (by omega)).2, EReal.coe_ne_bot _⟩
          have hsreal := EReal.toReal_le_toReal
            hs hleftbot (hphiFinite m (by omega)).1
          rw [EReal.toReal_add (hphiFinite (m + 1) (by omega)).1
            (hphiFinite (m + 1) (by omega)).2
            (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsreal
          norm_num at hsreal
          have hinc := auxiliaryG_increment u y a b lam q (m - 1) (by omega)
          have hvel : velocity u (m + 1) (by omega) = u (m + 1) - u m := by
            rw [velocity_eq_sub_of_one_le]
            simp
          have hm1 : m - 1 + 1 = m := by omega
          have hm2 : m - 1 + 2 = m + 1 := by omega
          simp only [hm1, hm2] at hinc
          rw [hvel] at hinc
          calc
            auxiliaryG u y a b lam q n (by omega) -
                  auxiliaryG u y a b lam q (m + 1) (by omega) -
                  inner ℝ (-zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - q) =
                (auxiliaryG u y a b lam q n (by omega) -
                  auxiliaryG u y a b lam q m (by omega) -
                  inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q)) +
                  inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - u m) := by
                    simp only [inner_neg_left]
                    linear_combination -hinc
            _ ≤ ((phi q).toReal - (phi (u m)).toReal) +
                  inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - u m) := by
                      have ih' : auxiliaryG u y a b lam q n (by omega) -
                          auxiliaryG u y a b lam q m (by omega) -
                          inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q) ≤
                            (phi q).toReal - (phi (u m)).toReal := by
                        simpa only using ih
                      have hadd := add_le_add_right ih'
                        (inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                          (u (m + 1) - u m))
                      simpa only [add_comm] using hadd
            _ ≤ (phi q).toReal - (phi (u (m + 1))).toReal := by
              have hsreal' : inner ℝ (zSequence u y a b lam (m + 1) (by omega))
                  (u (m + 1) - u m) ≤
                  (phi (u m)).toReal - (phi (u (m + 1))).toReal := by
                rw [show u m - u (m + 1) = -(u (m + 1) - u m) by abel,
                  inner_neg_left,
                  real_inner_comm (zSequence u y a b lam (m + 1) (by omega))
                    (u (m + 1) - u m)] at hsreal
                linarith
              linarith
    have hGgap (q : H) (hq : q ∈ Optimization.argminSet Θ) :
        ∀ n m : ℕ, ∀ hn : 2 ≤ n, ∀ hnm : n ≤ m,
          auxiliaryG u y a b lam q n hn -
              auxiliaryG u y a b lam q m (le_trans hn hnm) ≤
            (Θ q).toReal - (Θ (u m)).toReal +
              (1 / b) * (liapunovF u y a b lam q (m - 1) (by omega) -
                liapunovF u y a b lam q m (by omega)) := by
      intro n m hn hnm
      have hm : 2 ≤ m := le_trans hn hnm
      have hb : b ≠ 0 := ne_of_gt hH.b_pos
      have htel := hGtel q hq n m hn hnm
      have hinc := (theorem1_proposition3_local phi Θ psi gradPsi u y a b lam Lpsi q
        (m - 1) hH hIFB (by omega) hH.theta_convex).2.1
      have hres : inner ℝ
          (zSequence u y a b lam m (by omega) - gradPsi (u m)) (u m - q) =
          (1 / b) * (liapunovF u y a b lam q m (by omega) -
            liapunovF u y a b lam q (m - 1) (by omega)) := by
        have hvec := theorem1_residual_vector phi psi gradPsi a b lam u y hIFB (m - 2)
        have hmidx : m - 2 + 2 = m := by omega
        simp only [hmidx] at hvec
        rw [hvec]
        simp only [show m - 1 + 1 = m by omega] at hinc
        rw [← hinc]
        field_simp [hb]
      have hpsiB := hpsiSupport (u m) q
      have hendpoint : inner ℝ (-zSequence u y a b lam m (by omega)) (u m - q) ≤
          (1 / b) * (liapunovF u y a b lam q (m - 1) (by omega) -
            liapunovF u y a b lam q m (by omega)) + psi q - psi (u m) := by
        rw [show -zSequence u y a b lam m (by omega) =
          -(zSequence u y a b lam m (by omega) - gradPsi (u m)) - gradPsi (u m) by abel,
          inner_sub_left, inner_neg_left, hres]
        linarith
      have hqtop : phi q ≠ ⊤ :=
        (ERealFunction.mem_dom_iff phi q).mp
          (minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq) |>.ne
      have hqbot : phi q ≠ ⊥ := hH.phi_proper.1 q
      have hthetaq : (Θ q).toReal = (phi q).toReal + psi q := by
        rw [hH.theta_eq, EReal.toReal_add hqtop hqbot
          (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
        simp
      have hthetam : (Θ (u m)).toReal = (phi (u m)).toReal + psi (u m) := by
        rw [hH.theta_eq, EReal.toReal_add (hphiFinite m (by omega)).1
          (hphiFinite m (by omega)).2 (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
        simp
      rw [hthetaq, hthetam]
      linarith
    have hdist : ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
        Filter.Tendsto (fun k ↦ ‖u k - q‖) Filter.atTop (nhds l) := by
      intro q hq
      rcases hAlim q hq with ⟨lA, hlA⟩
      rcases hFlim q hq with ⟨lF, hlF⟩
      have hqeq : Θ q = sInf (Set.range Θ) :=
        (Optimization.mem_argminSet_iff_eq_sInf Θ q).mp hq
      have hqtop : Θ q ≠ ⊤ := by
        rw [hH.theta_eq]
        exact EReal.add_ne_top
          ((ERealFunction.mem_dom_iff phi q).mp
            (minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq) |>.ne)
          (EReal.coe_ne_top _)
      have hqbot : Θ q ≠ ⊥ := by
        rw [hH.theta_eq]
        exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 q, EReal.coe_ne_bot _⟩
      have htheta : Filter.Tendsto (fun k : ℕ => (Θ (u k)).toReal)
          Filter.atTop (nhds ((Θ q).toReal)) := by
        have hobjectiveq : Filter.Tendsto (fun k : ℕ => Θ (u k))
            Filter.atTop (nhds (Θ q)) := by
          simpa only [hqeq] using hobjective
        exact (EReal.tendsto_toReal hqtop hqbot).comp hobjectiveq
      let c : ℝ := (a + b) / (2 * lam)
      let d : ℕ → ℝ := fun k => ‖u (k + 1) - q‖ ^ 2
      let e : ℕ → ℝ := fun m =>
        (1 / lam + b) * ((Θ q).toReal - (Θ (u (m + 2))).toReal +
          (1 / b) * (liapunovF u y a b lam q (m + 1) (by omega) -
            liapunovF u y a b lam q (m + 2) (by omega)))
      have hc : 0 < c := by
        dsimp [c]
        exact div_pos (by linarith [hH.a_pos, hH.b_pos])
          (mul_pos (by norm_num) hH.step_pos)
      have he : Filter.Tendsto e Filter.atTop (nhds 0) := by
        have htheta2 := htheta.comp (Filter.tendsto_add_atTop_nat 2)
        have hF2 := hlF.comp (Filter.tendsto_add_atTop_nat 1)
        have hsubF := hlF.sub hF2
        have hzeroTheta : Filter.Tendsto
            (fun m : ℕ => (Θ q).toReal - (Θ (u (m + 2))).toReal)
            Filter.atTop (nhds 0) := by
          convert tendsto_const_nhds.sub htheta2 using 1 <;> simp
        dsimp [e]
        convert (hzeroTheta.add (hsubF.const_mul (1 / b))).const_mul (1 / lam + b)
          using 1 <;> simp
      have hineq (n m : ℕ) (hnm : n ≤ m) :
          c * d n ≤ c * d m +
            (theorem1AuxiliaryA u y a b lam q n -
              theorem1AuxiliaryA u y a b lam q m) + e m := by
        have hg := hGgap q hq (n + 2) (m + 2) (by omega) (by omega)
        dsimp [c, d, e, theorem1AuxiliaryA]
        have hn1 : n + 2 - 1 = n + 1 := by omega
        have hm1 : m + 2 - 1 = m + 1 := by omega
        simp only [hn1, hm1] at hg
        have hzcoef : 0 ≤ 1 / lam + b := by
          nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
        have hgmul := mul_le_mul_of_nonneg_left hg hzcoef
        linarith [hgmul]
      rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨R, hR⟩
      let B : ℝ := (R + ‖q‖) ^ 2
      have hdmem : ∀ k, d k ∈ Set.Icc 0 B := by
        intro k
        constructor
        · exact sq_nonneg _
        · have hk : ‖u (k + 1) - q‖ ≤ R + ‖q‖ := by
            calc
              ‖u (k + 1) - q‖ ≤ ‖u (k + 1)‖ + ‖q‖ := norm_sub_le _ _
              _ ≤ R + ‖q‖ := by
                linarith [hR _ (Set.mem_range_self (k + 1))]
          have hRnonneg : 0 ≤ R := by
            linarith [hR _ (Set.mem_range_self 0), norm_nonneg (u 0)]
          exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hk
      have hdcluster : ∀ r s : ℝ,
          IsSequentialClusterPt d r → IsSequentialClusterPt d s → r = s := by
        intro r s hr hs
        have hrs : r ≤ s := by
          rcases hr with ⟨t, htmono, ht⟩
          rcases hs with ⟨v, hvmono, hv⟩
          have htTop := htmono.tendsto_atTop
          have hvTop := hvmono.tendsto_atTop
          have hvcomp : Filter.Tendsto (d ∘ (v ∘ t)) Filter.atTop (nhds s) := by
            exact hv.comp htTop
          have hleft := (ht.const_mul c).sub (hvcomp.const_mul c)
          have heright := he.comp (hvTop.comp htTop)
          have hAdiff := (hlA.comp htTop).sub (hlA.comp (hvTop.comp htTop))
          have hright := hAdiff.add heright
          have hle : ∀ᶠ j : ℕ in Filter.atTop,
              c * d (t j) - c * d (v (t j)) ≤
                (theorem1AuxiliaryA u y a b lam q (t j) -
                  theorem1AuxiliaryA u y a b lam q (v (t j))) + e (v (t j)) := by
            filter_upwards [] with j
            linarith [hineq (t j) (v (t j))
              (StrictMono.id_le hvmono (t j))]
          have hlimle := le_of_tendsto_of_tendsto hleft hright hle
          have : c * r - c * s ≤ 0 := by simpa [Function.comp_def] using hlimle
          nlinarith
        have hsr : s ≤ r := by
          rcases hs with ⟨t, htmono, ht⟩
          rcases hr with ⟨v, hvmono, hv⟩
          have htTop := htmono.tendsto_atTop
          have hvTop := hvmono.tendsto_atTop
          have hvcomp : Filter.Tendsto (d ∘ (v ∘ t)) Filter.atTop (nhds r) := by
            exact hv.comp htTop
          have hleft := (ht.const_mul c).sub (hvcomp.const_mul c)
          have heright := he.comp (hvTop.comp htTop)
          have hAdiff := (hlA.comp htTop).sub (hlA.comp (hvTop.comp htTop))
          have hright := hAdiff.add heright
          have hle : ∀ᶠ j : ℕ in Filter.atTop,
              c * d (t j) - c * d (v (t j)) ≤
                (theorem1AuxiliaryA u y a b lam q (t j) -
                  theorem1AuxiliaryA u y a b lam q (v (t j))) + e (v (t j)) := by
            filter_upwards [] with j
            linarith [hineq (t j) (v (t j))
              (StrictMono.id_le hvmono (t j))]
          have hlimle := le_of_tendsto_of_tendsto hleft hright hle
          have : c * s - c * r ≤ 0 := by simpa [Function.comp_def] using hlimle
          nlinarith
        exact le_antisymm hrs hsr
      rcases isCompact_Icc.isSeqCompact hdmem with ⟨r, hrmem, t, htmono, ht⟩
      have hdlim : Filter.Tendsto d Filter.atTop (nhds r) :=
        tendsto_of_unique_sequential_cluster_point isCompact_Icc.isSeqCompact hdmem
          (fun s hs => hdcluster s r hs ⟨t, htmono, ht⟩)
      refine ⟨Real.sqrt r, ?_⟩
      have hsqrt := (Real.continuous_sqrt.tendsto r).comp hdlim
      have hshift : Filter.Tendsto (fun k : ℕ => ‖u (k + 1) - q‖)
          Filter.atTop (nhds (Real.sqrt r)) := by
        convert hsqrt using 1
        ext k
        dsimp [d]
        rw [Real.sqrt_sq (norm_nonneg _)]
      exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by
        simpa only [Nat.add_comm] using hshift)
    exact opial_lemma hS u hdist hcluster
```

## Proof explanation
The proof begins with the imported result `proposition6`. Applied to $\phi,\Theta,\psi,\mathrm{gradPsi},a,b,\lambda,L_\psi,u,y$, with hypotheses `hH` and `hIFB`, it yields three conclusions: first, $\Theta(u_k)\to\inf\Theta$; second, every weak sequential cluster point of $(u_k)$ belongs to $S=\mathrm{argmin}\Theta$; third, if $S=\varnothing$, then $`\|u_k\|\to+\infty`$. The Lean command `rcases ... with ⟨hobjective, hcluster, hempty⟩` unpacks this conjunction into those three facts. The subsequent `refine ⟨hobjective, ?_, hempty⟩` uses the first and third facts directly for the first and third conjuncts of the target theorem and leaves the middle weak-convergence assertion to be proved.

The proof then introduces the nonemptiness of the minimizer set and the disjunction of four cases:
```lean
rintro ⟨hS, hcase⟩
```
So from now on $S\neq\varnothing$, and one of the four alternatives holds. Before treating the cases, the proof records a boundedness and Liapunov-limit package. The local result `theorem1_proposition8_local` says that, under `hH`, `hIFB`, and $S\neq\varnothing$, the range of $u$ is bounded and, for every $q\in S$, the Liapunov quantity

```math
F_q(k)=\texttt{liapunovF }u\,y\,a\,b\,\lambda\,q\,k
```

has a limit along $k+1$. The proof extracts exactly these two facts as `hbounded` and `hFlim`. Then `theorem1_auxiliaryA_tendsto` is applied. That result says that if $u$ is bounded and if $F_q(k+1)$ has a limit for every $q\in S$, then for every $q\in S$ the auxiliary sequence

```math
A_q(k)=\texttt{theorem1AuxiliaryA }u\,y\,a\,b\,\lambda\,q\,k
```

also has a limit. This is recorded as `hAlim`.

The proof now splits on the four alternatives in `hcase`.

In the singleton case, $`S=\{q_0\}`$. If$p$and$q$are two weak sequential cluster points of$(u_k)$, then `hcluster` puts both $p$ and $q$ into $S$, hence both are equal to $q_0$. Thus there is at most one weak sequential cluster point. The theorem `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint` states that a sequence in a Hilbert space converges weakly if and only if it is bounded and has at most one weak sequential cluster point. Since boundedness was already obtained from `theorem1_proposition8_local`, the proof applies this criterion and obtains a weak limit $q$. Finally $q$ itself is a weak sequential cluster point of the sequence, so `hcluster` gives $q\in S$. This proves the desired existential statement in the singleton case.

In the second case, $\phi$ is real-valued: there are `phiReal : H → ℝ`, a differentiability proof, and a gradient field `gradPhi` with weak-to-weak sequential continuity. The proof first shows that every subgradient of $\phi$ is actually the gradient. The subdifferential definition gives that $g\in\partial\phi(x)$ means

$$
\langle z-x,g\rangle+\phi(x)\le\phi(z)
$$

for every $z$. Since here $\phi$ is the coercion of a real function $\phi_{\mathbb R}$, this says that $x$ minimizes

$$
z\mapsto \phi_{\mathbb R}(z)-\langle g,z\rangle.
$$

At a differentiability point of this function, the derivative must vanish. The derivative of $\phi_{\mathbb R}$ is represented by `gradPhi`, while the derivative of $z\mapsto\langle g,z\rangle$ is the linear functional $\langle g,\cdot\rangle$. Evaluating the derivative identity at $\mathrm{gradPhi}(x)-g$ shows that

```math
\|g-\mathrm{gradPhi}(x)\|^2=0,
```

hence $g=\mathrm{gradPhi}(x)$. This is the local lemma `hsubgradient_eq`.

Next the proof obtains from `theorem1_velocity_tendsto_zero` that

$$
u_{k+1}-u_k\to 0.
$$

Suppose $p$ and $q$ are weak sequential cluster points of $(u_k)$, witnessed by strictly increasing subsequences $t_j$ and $s_j$. By `hcluster`, both $p$ and $q$ lie in $S$. The result `theorem1_shift_two_weakly` then upgrades the weak limits along the subsequences by two steps: since $u_{k+1}-u_k\to0$ and $t_j,s_j\to\infty$, one has

$$
u_{t_j+2}\rightharpoonup p,\qquad u_{s_j+2}\rightharpoonup q.
$$

The weak continuity of `gradPhi` therefore gives weak convergence of the gradient values. The proof also recalls that $-z_{t_j+2}\in\partial\phi(u_{t_j+2})$ and $-z_{s_j+2}\in\partial\phi(u_{s_j+2})$, from `theorem1_neg_z_mem_subgradient`; the subgradient equality just proved identifies these with $\mathrm{gradPhi}$ values. Using the four-term identity `auxiliaryA_four_term` and the limits of $A_p,A_q$, the proof obtains a sequence expression tending to $0$, while the inner-product limits give its limit as

```math
\frac{a+b}{\lambda}(-\|p-q\|^2)
-\left(\frac1\lambda+b\right)
\langle \mathrm{gradPhi}(p)-\mathrm{gradPhi}(q),p-q\rangle .
```

This expression must equal $0$. Separately, convexity of the real-valued $\phi$ gives the support inequality

$$
\phi_{\mathbb R}(x)-\phi_{\mathbb R}(z)
\le \langle \mathrm{gradPhi}(x),x-z\rangle,
$$

which implies

$$
\langle \mathrm{gradPhi}(p)-\mathrm{gradPhi}(q),p-q\rangle\ge0.
$$

The coefficients $\frac{a+b}{\lambda}$ and $\frac1\lambda+b$ are positive, so the equality forces $`\|p-q\|=0`$, hence$p=q$. Thus there is at most one weak sequential cluster point. Applying the boundedness plus uniqueness criterion again gives weak convergence, and `hcluster` identifies the weak limit as an element of $S$.

The third case assumes that `gradPsi` is weak-to-weak sequentially continuous. The proof again records $u_{k+1}-u_k\to0$ from `theorem1_velocity_tendsto_zero`. First it proves that for each $q\in S$,

$$
\left\langle
z_{k+2}-\mathrm{gradPsi}(u_{k+2}),
u_{k+2}-q
\right\rangle\to0.
$$

Indeed, `hFlim` gives a limit for $F_q(k+1)$, and `theorem1_liapunov_shift_tendsto` gives the same limit for $F_q(k+2)$. The equality in `theorem1_proposition3_local`, together with the residual identity `theorem1_residual_vector`

$$
z_{r+2}-\mathrm{gradPsi}(u_{r+2})
=\left(\frac1\lambda-a\right)v_{r+2}
+\left(\frac1\lambda+b\right)\zeta_{r+2},
$$

shows that the above inner product is $(1/b)(F_q(k+2)-F_q(k+1))$, hence tends to $0$.

Now take two weak sequential cluster points $p,q$, witnessed by subsequences $t_j,s_j$. As before, `hcluster` puts $p,q\in S$, and `theorem1_shift_two_weakly` gives

$$
u_{t_j+2}\rightharpoonup p,\qquad u_{s_j+2}\rightharpoonup q.
$$

The weak continuity of `gradPsi` therefore gives

$$
\mathrm{gradPsi}(u_{t_j+2})\rightharpoonup \mathrm{gradPsi}(p),\qquad
\mathrm{gradPsi}(u_{s_j+2})\rightharpoonup \mathrm{gradPsi}(q).
$$

Using the residual-inner-product limit just proved, the proof obtains the corresponding limit for

$$
\langle z_{t_j+2}-z_{s_j+2},q-p\rangle.
$$

Combining this with `auxiliaryA_four_term` and the fact that $A_p$ and $A_q$ have limits gives

```math
0=\frac{a+b}{\lambda}(-\|p-q\|^2)
-\left(\frac1\lambda+b\right)
\langle \mathrm{gradPsi}(p)-\mathrm{gradPsi}(q),q-p\rangle .
```

It remains to know that the last inner product is nonnegative. The proof establishes a local fact `hminimizer_subgradient`: if $x\in S$, then

$$
-\mathrm{gradPsi}(x)\in\partial\phi(x).
$$

To see this, it uses $\Theta=\phi+\psi$ and minimality of $x$, then differentiates along the line $t\mapsto x+t(z-x)$. The chord inequality coming from convexity of $\phi$ gives, for $0\lt t\lt 1$,

$$
-\frac{\psi(x+t(z-x))-\psi(x)}{t}
\le \phi(z)-\phi(x).
$$

Letting $t\downarrow0$, the differentiability of $\psi$ with gradient `gradPsi` gives

$$
-\langle \mathrm{gradPsi}(x),z-x\rangle
\le \phi(z)-\phi(x),
$$

which is exactly the subgradient inequality defining $-\mathrm{gradPsi}(x)\in\partial\phi(x)$. The result `isMonotone_subdifferential` states that the subdifferential of a proper convex function is monotone: if $x^*\in\partial\phi(x)$ and $y^*\in\partial\phi(y)$, then

$$
\langle x^*-y^*,x-y\rangle\ge0.
$$

Applying this to $-\mathrm{gradPsi}(p)\in\partial\phi(p)$ and $-\mathrm{gradPsi}(q)\in\partial\phi(q)$ gives

$$
\langle \mathrm{gradPsi}(p)-\mathrm{gradPsi}(q),q-p\rangle\ge0.
$$

Again positivity of the coefficients forces $`\|p-q\|=0`$, so$p=q$. The uniqueness criterion now yields weak convergence, and `hcluster` identifies the limit as a minimizer.

The fourth case assumes that the epigraph of $\psi$ is convex. The proof first converts this into convexity of the real-valued function $\psi$, then derives the first-order support inequality for convex differentiable $\psi$:

$$
\psi(x)-\psi(z)\le \langle \mathrm{gradPsi}(x),x-z\rangle .
$$

This is proved by restricting $\psi$ to the line $t\mapsto z+t(x-z)$ and comparing the secant slope on $[0,1]$ with the derivative at $1$.

Next the proof shows that for every $j\ge1$, $\phi(u_j)$ is finite, i.e. neither $\top$ nor $\bot$. This uses `theorem1_neg_z_mem_subgradient`, which gives $-z_j\in\partial\phi(u_j)$, together with `subgradient_value_ne_top` and properness of $\phi$.

The proof then uses the subgradient inequalities for $-z_j\in\partial\phi(u_j)$ and the increment identity `auxiliaryG_increment`

$$
G_q(k+2)-G_q(k+1)
=\langle z_{k+2},u_{k+2}-q\rangle
-\langle z_{k+1},u_{k+1}-q\rangle
-\langle z_{k+2},u_{k+2}-u_{k+1}\rangle
$$

to prove a telescoping estimate `hGtel`. It says that for $n\le m$, $n\ge2$,

$$
G_q(n)-G_q(m)-\langle -z_m,u_m-q\rangle
\le (\phi(q))_{\mathrm{toReal}}-(\phi(u_m))_{\mathrm{toReal}} .
$$

Combining this with the residual identity and the support inequality for $\psi$ gives `hGgap`:

$$
G_q(n)-G_q(m)
\le (\Theta(q))_{\mathrm{toReal}}-(\Theta(u_m))_{\mathrm{toReal}}
+\frac1b\bigl(F_q(m-1)-F_q(m)\bigr).
$$

Here the conversions from `EReal` to real numbers are justified by the finiteness facts established above.

The proof now fixes $q\in S$ and derives convergence of the distances $`\|u_k-q\|`$. It defines

```math
c=\frac{a+b}{2\lambda}>0,\qquad
d_k=\|u_{k+1}-q\|^2,
```

and

$$
e_m=\left(\frac1\lambda+b\right)
\left(
(\Theta(q))_{\mathrm{toReal}}-(\Theta(u_{m+2}))_{\mathrm{toReal}}
+\frac1b\bigl(F_q(m+1)-F_q(m+2)\bigr)
\right).
$$

Because $q\in S$, the first conclusion of `proposition6` gives $\Theta(u_{m+2})\to\Theta(q)$. The Liapunov limits `hFlim` make the difference $F_q(m+1)-F_q(m+2)$ tend to $0$. Hence $e_m\to0$. From `hGgap` the proof obtains, for $n\le m$,

```math
c\,d_n\le c\,d_m+\bigl(A_q(n)-A_q(m)\bigr)+e_m .
```

Since $A_q$ has a limit by `hAlim`, the right-hand side tends to $0$ along the relevant subsequences. The sequence $d_k$ is bounded because $u$ is bounded, so it lies in some compact interval $[0,B]$. If $d$ had two different sequential cluster points, the displayed inequality applied in both orders would force them to be equal. Therefore $d$ has a unique sequential cluster point. The theorem `tendsto_of_unique_sequential_cluster_point` then gives convergence of $d$, and taking square roots gives convergence of $`\|u_{k+1}-q\|`$, hence of$`\|u_k-q\|`$. Thus

```math
\exists l\in\mathbb R,\qquad \|u_k-q\|\to l
```

for every $q\in S$.

Finally, the proof applies `opial_lemma` with $C=S$. The lemma states that if $C\neq\varnothing$, if for every $z\in C$ the distances $`\|x_n-z\|`$have a limit, and if every weak sequential cluster point of$(x_n)$lies in$C$, then$(x_n)$converges weakly to some point of$C$. Here$C=S$ is nonempty by `hS`, the distance-limit condition is exactly the result just proved, and the cluster-point condition is `hcluster` from `proposition6`. Therefore `opial_lemma` produces $q\in S$ such that $u_k\rightharpoonup q$, completing the middle conjunct of the theorem in the convex- $\psi$ case.

