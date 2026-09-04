## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/thm_5.lean`

## Lean statement
```lean
theorem proximal_gradient_gradient_case {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (Psi : H → ℝ)
    (S : Set H) (x : ℝ → H) (mu beta : ℝ)
    (hPsi_convex : ConvexOn ℝ Set.univ Psi)
    (hPsi_grad : ∀ z, HasGradientAt Psi (∇ Psi z) z) (hS : S.Nonempty)
    (hbeta : 0 < beta) (hmu : 0 < mu)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ ∇ Psi w))
    (hsolution : ∀ z, z ∈ S ↔ -∇ Psi z ∈ ERealFunction.subdifferential Phi z)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt x (deriv x t) t)
    (hAC : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hdynamics : ∀ t, 0 ≤ t → deriv x t + x t -
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • ∇ Psi (x t)) = 0) :
    (∃ xinf ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H xinf))) ∧
    (∀ z ∈ S, Tendsto (fun t ↦ ∇ Psi (x t)) atTop (nhds (∇ Psi z)) ∧
      IntegrableOn (fun t ↦ ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Ioi 0)) ∧
    Tendsto (deriv x) atTop (nhds 0)
```

## Statement explanation
The theorem `proximal_gradient_gradient_case` states a convergence result for a proximal-gradient dynamical system in a real Hilbert space.

The type and data are as follows. \(H\) is a real Hilbert space: it has a normed additive commutative group structure, an inner product space structure over \(\mathbb R\), and is complete. There is a function
\[
\Phi:H\to \operatorname{Set.Ioi}(\bot:\mathrm{EReal})
\]
taking extended-real values above the order-theoretic bottom, and \(h\Phi\) asserts that \(\Phi\) belongs to the class `ERealFunction.gammaZero H`, the class used for the proximal operator. There is a real-valued function \(\Psi:H\to\mathbb R\), a set \(S\subseteq H\), a trajectory \(x:\mathbb R\to H\), and real parameters \(\mu,\beta\).

The hypotheses are:

- \(h\Psi_{\mathrm{convex}}\): \(\Psi\) is convex on all of \(H\).
- \(h\Psi_{\mathrm{grad}}\): for every \(z\), \(\Psi\) has gradient \(\nabla\Psi(z)\) at \(z\).
- \(hS\): \(S\) is nonempty.
- \(h\beta,h\mu\): \(0<\beta\) and \(0<\mu\).
- \(hB\): the gradient \(\nabla\Psi\) is \(\beta\)-cocoercive on all of \(H\).
- \(h_{\mathrm{solution}}\): for every \(z\),
  \[
  z\in S \iff -\nabla\Psi(z)\in \operatorname{ERealFunction.subdifferential}\Phi(z).
  \]
- \(h_{\mathrm{deriv}}\): on \(t\ge 0\), \(x\) is differentiable, with derivative \(\operatorname{deriv}x(t)\).
- \(hAC\): for every \(b>0\), \(x\) is absolutely continuous on \([0,b]\).
- \(h_{\mathrm{dynamics}}\): for every \(t\ge 0\),
  \[
  \operatorname{deriv}x(t)+x(t)
  -
  \operatorname{ERealFunction.scaledProximityOperator}\Phi\,h\Phi\,\langle\mu,h\mu\rangle
  \bigl(x(t)-\mu\,\nabla\Psi(x(t))\bigr)=0.
  \]

The conclusion has three parts:

1. There exists \(x_{\inf}\in S\) such that \(x(t)\) converges weakly to \(x_{\inf}\) as \(t\to+\infty\).
2. For every \(z\in S\), \(\nabla\Psi(x(t))\) converges strongly to \(\nabla\Psi(z)\) as \(t\to+\infty\), and
   \[
   t\mapsto \|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
   \]
   is integrable on the positive reals.
3. The derivative \(\operatorname{deriv}x(t)\) converges strongly to \(0\) as \(t\to+\infty\).

## Lean proof
```lean
by
  have hlyap_base : ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t + mu⁻¹ * ‖deriv x t‖ ^ 2 +
        beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 +
          inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z) ≤ 0 := by
    exact proximal_gradient_cocoercive_lyapunov Phi hPhi (fun y => ∇ Psi y) S x mu beta hmu
      hB hsolution hderiv hdynamics
  let E : H → ℝ → ℝ := fun z t =>
    (2 * mu)⁻¹ * ‖x t - z‖ ^ 2 +
      (Psi (x t) - inner ℝ (∇ Psi z) (x t - z) - Psi z)
  have hE_nonneg : ∀ z : H, ∀ t : ℝ, 0 ≤ E z t := by
    intro z t
    have hsupport := convex_supporting_baillon_haddad Psi (fun y => ∇ Psi y)
      hPsi_convex hPsi_grad z (x t)
    have hquad : 0 ≤ (2 * mu)⁻¹ * ‖x t - z‖ ^ 2 := by
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hmu.le)) (sq_nonneg _)
    dsimp [E]
    linarith
  have hE_hasDeriv : ∀ z : H, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (E z)
        (mu⁻¹ * inner ℝ (x t - z) (deriv x t) +
          inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z)) t := by
    intro z t ht
    have hcomp := ((hPsi_grad (x t)).hasFDerivAt.comp t (hderiv t ht).hasFDerivAt).hasDerivAt
    have hcomp' : HasDerivAt (fun s => Psi (x s))
        (inner ℝ (∇ Psi (x t)) (deriv x t)) t := by
      simpa [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
        real_inner_comm] using hcomp
    have hlin' : HasDerivAt (fun s => inner ℝ (∇ Psi z) (x s - z))
        (inner ℝ (∇ Psi z) (deriv x t)) t := by
      simpa using (hasDerivAt_const (x := t) (∇ Psi z)).inner ℝ ((hderiv t ht).sub_const z)
    convert (((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)).add
        ((hcomp'.sub hlin').sub_const (Psi z)) using 1
    simp [inner_sub_right, real_inner_comm]; ring
  have hlyap : ∀ z ∈ S, ∀ t, 0 ≤ t →
      deriv (E z) t + mu⁻¹ * ‖deriv x t‖ ^ 2 +
        beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤ 0 := by
    intro z hz t ht
    rw [(hE_hasDeriv z t ht).deriv]
    have hquad : deriv (fun s => (2 * mu)⁻¹ * ‖x s - z‖ ^ 2) t =
        mu⁻¹ * inner ℝ (x t - z) (deriv x t) := by
      rw [(((hderiv t ht).sub_const z).norm_sq.const_mul ((2 * mu)⁻¹)).deriv]
      field_simp [hmu.ne']
    have hbase := hlyap_base z hz t ht
    rw [hquad] at hbase
    linarith
  have hE_antitone : ∀ z ∈ S, AntitoneOn (E z) (Set.Ici 0) := by
    intro z hz
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t ht
      exact (hE_hasDeriv z t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      exact (hE_hasDeriv z t ht0).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have h := hlyap z hz t ht0
      have hdxnonneg : 0 ≤ mu⁻¹ * ‖deriv x t‖ ^ 2 := by
        exact mul_nonneg (inv_nonneg.mpr hmu.le) (sq_nonneg _)
      have hgradnonneg : 0 ≤ beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 :=
        mul_nonneg hbeta.le (sq_nonneg _)
      linarith
  have hE_limit : ∀ z ∈ S, ∃ l : ℝ, Tendsto (E z) atTop (nhds l) := by
    intro z hz
    exact tendsto_of_antitone_nonneg_on_Ici (E z) (hE_antitone z hz)
      (fun t ht => hE_nonneg z t)
  have hgrad_cont : Continuous (∇ Psi) := by
    change Continuous (fun u : H => (fun w : Set.univ => ∇ Psi w) ⟨u, Set.mem_univ u⟩)
    exact (lipschitzWith_of_cocoercive hB).continuous.comp
      (continuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hfield_cont : Continuous (fun u =>
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ (u - mu • ∇ Psi u) - u) :=
    proximal_gradient_field_continuous Phi hPhi (∇ Psi) mu beta hmu hB
  have hdx_eq : ∀ t, 0 ≤ t → deriv x t =
      ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
        (x t - mu • ∇ Psi (x t)) - x t := by
    intro t ht
    apply (eq_sub_iff_add_eq).mpr
    simpa [add_comm] using (sub_eq_zero.mp (hdynamics t ht))
  have hdx_continuous : ∀ T, 0 < T → ContinuousOn (deriv x) (Set.Icc 0 T) := by
    intro T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hcomp : ContinuousOn (fun t =>
        ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩
          (x t - mu • ∇ Psi (x t)) - x t) (Set.Icc 0 T) := by
      simpa only [Function.comp_apply] using
        (hfield_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
    exact hcomp.congr fun t ht => hdx_eq t ht.1
  have hdiss_continuous : ∀ z : H, ∀ T, 0 < T → ContinuousOn (fun t =>
      mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Icc 0 T) := by
    intro z T hT
    have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
    have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
      simpa only [Function.comp_apply] using
        (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
    exact (continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2)).add
      (continuousOn_const.mul ((hgradx_cont.sub continuousOn_const).norm.pow 2))
  have hfinite : ∀ z ∈ S, ∀ T, 0 < T →
      ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
        E z 0 := by
    intro z hz T hT
    have hE_cont : ContinuousOn (E z) (Set.Icc 0 T) := by
      intro t ht
      exact (hE_hasDeriv z t ht.1).continuousAt.continuousWithinAt
    have hEderiv_cont : ContinuousOn (fun t => deriv (E z) t) (Set.Icc 0 T) := by
      have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
        simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
      have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
        simpa only [Function.comp_apply] using
          (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
      have hform : ContinuousOn (fun t =>
          mu⁻¹ * inner ℝ (x t - z) (deriv x t) +
            inner ℝ (deriv x t) (∇ Psi (x t) - ∇ Psi z)) (Set.Icc 0 T) :=
        (continuousOn_const.mul ((hx_cont.sub continuousOn_const).inner
          (hdx_continuous T hT))).add
          ((hdx_continuous T hT).inner (hgradx_cont.sub continuousOn_const))
      exact hform.congr fun t ht => (hE_hasDeriv z t ht.1).deriv
    have hD_int : IntervalIntegrable (fun t =>
        mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
      (hdiss_continuous z T hT).intervalIntegrable_of_Icc (le_of_lt hT)
    have hderiv_int : IntervalIntegrable (fun t => -deriv (E z) t) volume 0 T :=
      (hEderiv_cont.intervalIntegrable_of_Icc (le_of_lt hT)).neg
    have hpoint : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
          -deriv (E z) t := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      linarith [hlyap z hz t ht.1]
    have hint := intervalIntegral.integral_mono_ae_restrict (le_of_lt hT) hD_int hderiv_int hpoint
    calc
      ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
          ∫ t in 0..T, -deriv (E z) t := hint
      _ = -(∫ t in 0..T, deriv (E z) t) := by rw [intervalIntegral.integral_neg]
      _ = -(E z T - E z 0) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hT) hE_cont]
        · intro t ht
          simpa only [(hE_hasDeriv z t ht.1.le).deriv] using hE_hasDeriv z t ht.1.le
        · exact hEderiv_cont.intervalIntegrable_of_Icc (le_of_lt hT)
      _ ≤ E z 0 := by linarith [hE_nonneg z T]
  have hdx_sq_integrable : ∀ z ∈ S,
      IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    have hscaled : IntegrableOn (fun t => mu⁻¹ * ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
      apply integrableOn_Ici_of_nonneg_interval_bound (C := E z 0)
      · intro T
        by_cases hT : 0 < T
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
            ((continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le)
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty
      · intro t ht
        exact mul_nonneg (inv_nonneg.mpr hmu.le) (sq_nonneg _)
      · intro T hT
        rcases hT.eq_or_lt with rfl | hT
        · simpa using hE_nonneg z 0
        · have hAint : IntervalIntegrable (fun t => mu⁻¹ * ‖deriv x t‖ ^ 2) volume 0 T :=
            (continuousOn_const.mul ((hdx_continuous T hT).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le
          have hDint : IntervalIntegrable (fun t =>
              mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
            (hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le
          calc
            ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 ≤
                ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 := by
              apply intervalIntegral.integral_mono_on hT.le hAint hDint
              intro t ht
              exact le_add_of_nonneg_right (mul_nonneg hbeta.le (sq_nonneg _))
            _ ≤ E z 0 := hfinite z hz T hT
    change Integrable (fun t => ‖deriv x t‖ ^ 2) (volume.restrict (Set.Ici 0))
    have hres := hscaled.const_mul mu
    change Integrable (fun t => mu * (mu⁻¹ * ‖deriv x t‖ ^ 2))
      (volume.restrict (Set.Ici 0)) at hres
    convert hres using 1
    funext t
    rw [← mul_assoc, mul_inv_cancel₀ hmu.ne', one_mul]
  have hgrad_sq_integrable : ∀ z ∈ S,
      IntegrableOn (fun t => ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Ici 0) := by
    intro z hz
    have hscaled : IntegrableOn (fun t => beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (Set.Ici 0) := by
      apply integrableOn_Ici_of_nonneg_interval_bound (C := E z 0)
      · intro T
        by_cases hT : 0 < T
        · have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
            simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
          have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
            simpa only [Function.comp_apply] using
              (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
          exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
            ((continuousOn_const.mul ((hgradx_cont.sub continuousOn_const).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le)
        · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hT)]
          exact integrableOn_empty
      · intro t ht
        exact mul_nonneg hbeta.le (sq_nonneg _)
      · intro T hT
        rcases hT.eq_or_lt with rfl | hT
        · simpa using hE_nonneg z 0
        · have hx_cont : ContinuousOn x (Set.Icc 0 T) := by
            simpa [Set.uIcc_of_le (le_of_lt hT)] using (hAC T hT).continuousOn
          have hgradx_cont : ContinuousOn (fun t => ∇ Psi (x t)) (Set.Icc 0 T) := by
            simpa only [Function.comp_apply] using
              (hgrad_cont.continuousOn.comp hx_cont (Set.mapsTo_univ x _))
          have hAint : IntervalIntegrable (fun t =>
              beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
            (continuousOn_const.mul ((hgradx_cont.sub continuousOn_const).norm.pow 2))
              |>.intervalIntegrable_of_Icc hT.le
          have hDint : IntervalIntegrable (fun t =>
              mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) volume 0 T :=
            (hdiss_continuous z T hT).intervalIntegrable_of_Icc hT.le
          calc
            ∫ t in 0..T, beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 ≤
                ∫ t in 0..T, mu⁻¹ * ‖deriv x t‖ ^ 2 + beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2 := by
              apply intervalIntegral.integral_mono_on hT.le hAint hDint
              intro t ht
              exact le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hmu.le) (sq_nonneg _))
            _ ≤ E z 0 := hfinite z hz T hT
    change Integrable (fun t => ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2) (volume.restrict (Set.Ici 0))
    have hres := hscaled.const_mul beta⁻¹
    change Integrable (fun t => beta⁻¹ * (beta * ‖∇ Psi (x t) - ∇ Psi z‖ ^ 2))
      (volume.restrict (Set.Ici 0)) at hres
    convert hres using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hbeta.ne', one_mul]
  rcases hS with ⟨z0, hz0⟩
  have hnorm_bound : ∀ t, 0 ≤ t → ‖x t - z0‖ ^ 2 ≤ 2 * mu * E z0 0 := by
    intro t ht
    have hsupport := convex_supporting_baillon_haddad Psi (fun y => ∇ Psi y)
      hPsi_convex hPsi_grad z0 (x t)
    have hrem : 0 ≤ Psi (x t) - inner ℝ (∇ Psi z0) (x t - z0) - Psi z0 := by
      linarith
    have hanti := hE_antitone z0 hz0 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hquad : (2 * mu)⁻¹ * ‖x t - z0‖ ^ 2 ≤ E z0 0 := by
      dsimp [E]
      linarith
    have hcoef : 0 < (2 * mu)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hmu)
    calc
      ‖x t - z0‖ ^ 2 = (2 * mu) * ((2 * mu)⁻¹ * ‖x t - z0‖ ^ 2) := by
        field_simp [hmu.ne']
      _ ≤ (2 * mu) * E z0 0 := by gcongr
  have hE0_nonneg : 0 ≤ E z0 0 := hE_nonneg z0 0
  let R : ℝ := Real.sqrt (2 * mu * E z0 0)
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hR_sq : R ^ 2 = 2 * mu * E z0 0 := by
    dsimp [R]
    simpa [pow_two] using Real.mul_self_sqrt (show 0 ≤ 2 * mu * E z0 0 by positivity)
  have hnorm_bound' : ∀ t, 0 ≤ t → ‖x t - z0‖ ≤ R := by
    intro t ht
    nlinarith [hnorm_bound t ht, norm_nonneg (x t - z0)]
  obtain ⟨L, hfield_lip⟩ := proximal_gradient_field_lipschitz Phi hPhi (∇ Psi) mu beta hmu hB
  let V : H → H := fun u =>
    ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu⟩ (u - mu • ∇ Psi u) - u
  let K : NNReal := ‖V z0‖₊ + L * R.toNNReal
  have hdx_bound : ∀ t, 0 ≤ t → ‖deriv x t‖ ≤ K := by
    intro t ht
    rw [hdx_eq t ht]
    change ‖V (x t)‖ ≤ K
    calc
      ‖V (x t)‖ = ‖(V (x t) - V z0) + V z0‖ := by congr 1; abel
      _ ≤ ‖V (x t) - V z0‖ + ‖V z0‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖x t - z0‖ + ‖V z0‖ := by
        gcongr
        simpa [V] using hfield_lip.norm_sub_le (x t) z0
      _ ≤ (L : ℝ) * R + ‖V z0‖ := by
        gcongr
        exact hnorm_bound' t ht
      _ = K := by
        simp [K, R, hR_nonneg]
        ring
  have hx_lip : LipschitzOnWith K x (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (hderiv t ht).differentiableAt
    · intro t ht
      apply NNReal.coe_le_coe.mpr
      exact hdx_bound t ht
  have hgrad_uc : UniformContinuous (∇ Psi) := by
    exact cocoercive_uniformContinuous hB
  have hgradstrong : ∀ z ∈ S, Tendsto (fun t => ∇ Psi (x t)) atTop (nhds (∇ Psi z)) := by
    intro z hz
    have hres_uc : UniformContinuousOn (fun t => ∇ Psi (x t) - ∇ Psi z) (Set.Ici 0) := by
      have htranslate : UniformContinuous (fun u : H => u - ∇ Psi z) :=
        uniformContinuous_id.sub uniformContinuous_const
      simpa only [Function.comp_def] using
        htranslate.comp_uniformContinuousOn
          (hgrad_uc.comp_uniformContinuousOn hx_lip.uniformContinuousOn)
    have hzero := uniformContinuousOn_sq_integrable_tendsto_zero _ hres_uc
      (hgrad_sq_integrable z hz)
    have h := hzero.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => ∇ Psi z) atTop (nhds (∇ Psi z)))
    simpa only [sub_add_cancel, zero_add] using h
  have hVuc : UniformContinuousOn (fun t : ℝ => V (x t)) (Set.Ici 0) := by
    exact (by simpa [V] using hfield_lip : LipschitzWith L V)
      |>.uniformContinuous.comp_uniformContinuousOn hx_lip.uniformContinuousOn
  have hdx_uc : UniformContinuousOn (deriv x) (Set.Ici 0) := by
    apply hVuc.congr
    intro t ht
    exact (hdx_eq t ht).symm
  have hdxzero : Tendsto (deriv x) atTop (nhds 0) :=
    uniformContinuousOn_sq_integrable_tendsto_zero _ hdx_uc (hdx_sq_integrable z0 hz0)
  refine ⟨?_, ?_, hdxzero⟩
  · have hcluster : ∀ z : H, ∀ u : ℕ → ℝ, Tendsto u atTop atTop →
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z)) → z ∈ S := by
      intro z u hu hweak
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (hu.eventually (eventually_ge_atTop (0 : ℝ)))
      have hweak_shift : Tendsto (fun n ↦ toWeakSpace ℝ H (x (u (n + N)))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa only [Function.comp_def] using hweak.comp (Filter.tendsto_add_atTop_nat N)
      have hgrad_shift : Tendsto (fun n ↦ ∇ Psi (x (u (n + N)))) atTop
          (nhds (∇ Psi z0)) := by
        simpa only [Function.comp_def] using (hgradstrong z0 hz0).comp hu |>.comp
          (Filter.tendsto_add_atTop_nat N)
      have hdx_shift : Tendsto (fun n ↦ deriv x (u (n + N))) atTop (nhds 0) := by
        simpa only [Function.comp_def] using hdxzero.comp hu |>.comp
          (Filter.tendsto_add_atTop_nat N)
      have hy : Tendsto (fun n ↦ toWeakSpace ℝ H
          (x (u (n + N)) + deriv x (u (n + N)))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        refine (weakConvergence_iff_forall_tendsto_inner_right _ z).2 ?_
        intro v
        have hweak_inner :=
          (weakConvergence_iff_forall_tendsto_inner_right _ z).1 hweak_shift v
        have hdx_inner : Tendsto (fun n ↦ inner ℝ (deriv x (u (n + N))) v) atTop
            (nhds (inner ℝ (0 : H) v)) :=
          hdx_shift.inner (tendsto_const_nhds (x := v))
        simpa only [inner_add_left, inner_zero_left, add_zero] using hweak_inner.add hdx_inner
      have hq : Tendsto (fun n ↦
          -∇ Psi (x (u (n + N))) - mu⁻¹ • deriv x (u (n + N))) atTop
          (nhds (-∇ Psi z0)) := by
        have hsmul : Tendsto (fun n ↦ (mu⁻¹ : ℝ) • deriv x (u (n + N))) atTop
            (nhds 0) := by
          simpa using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (mu⁻¹ : ℝ)) atTop
              (nhds mu⁻¹)).smul hdx_shift
        simpa using hgrad_shift.neg.sub hsmul
      have hsub : -∇ Psi z0 ∈ ERealFunction.subdifferential Phi z := by
        apply maximal_monotone_graph_weak_strong_closed (ERealFunction.subdifferential Phi)
          (ERealFunction.subdifferential_isMaximalMonotone_of_mem_gammaZero hPhi)
          (fun n ↦ x (u (n + N)) + deriv x (u (n + N)))
          (fun n ↦ -∇ Psi (x (u (n + N))) - mu⁻¹ • deriv x (u (n + N))) z (-∇ Psi z0)
          hy hq
        intro n
        apply proximal_gradient_classical_subgradient Phi hPhi (∇ Psi) x mu hmu hderiv hdynamics
        exact hN (n + N) (Nat.le_add_left _ _)
      have hgradeq : ∇ Psi z = ∇ Psi z0 :=
        cocoercive_weak_strong_closed hbeta hB (fun n ↦ x (u (n + N))) z (∇ Psi z0)
          hweak_shift hgrad_shift
      exact (hsolution z).mpr (by simpa [hgradeq] using hsub)
    have hunique_time : ∀ z1 z2 : H, ∀ u v : ℕ → ℝ, Tendsto u atTop atTop →
        Tendsto v atTop atTop →
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z1)) →
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (v n))) atTop
          (nhds (toWeakSpace ℝ H z2)) → z1 = z2 := by
      intro z1 z2 u v hu hv huweak hvweak
      have hz1 : z1 ∈ S := hcluster z1 u hu huweak
      have hz2 : z2 ∈ S := hcluster z2 v hv hvweak
      rcases hE_limit z1 hz1 with ⟨l1, hl1⟩
      rcases hE_limit z2 hz2 with ⟨l2, hl2⟩
      let F : ℝ → ℝ := fun t ↦ mu⁻¹ * inner ℝ (x t) (z2 - z1) +
        inner ℝ (x t) (∇ Psi z2 - ∇ Psi z1)
      let C : ℝ := (2 * mu)⁻¹ * (‖z1‖ ^ 2 - ‖z2‖ ^ 2) +
        inner ℝ (∇ Psi z1) z1 - inner ℝ (∇ Psi z2) z2 - Psi z1 + Psi z2
      have hident (t : ℝ) : E z1 t - E z2 t = F t + C := by
        dsimp [E, F, C]
        rw [← real_inner_self_eq_norm_sq (x t - z1),
          ← real_inner_self_eq_norm_sq (x t - z2),
          ← real_inner_self_eq_norm_sq z1,
          ← real_inner_self_eq_norm_sq z2]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      have hF : Tendsto F atTop (nhds (l1 - l2 - C)) := by
        have h := (hl1.sub hl2).sub (tendsto_const_nhds (x := C))
        convert h using 1
        · ext t
          rw [hident]
          ring
      let q1 : ℝ := mu⁻¹ * inner ℝ z1 (z2 - z1) +
        inner ℝ z1 (∇ Psi z2 - ∇ Psi z1)
      let q2 : ℝ := mu⁻¹ * inner ℝ z2 (z2 - z1) +
        inner ℝ z2 (∇ Psi z2 - ∇ Psi z1)
      have hFu : Tendsto (fun n ↦ F (u n)) atTop (nhds q1) := by
        have hcoord1 := (weakConvergence_iff_forall_tendsto_inner_right _ z1).1 huweak
          (z2 - z1)
        have hcoord2 := (weakConvergence_iff_forall_tendsto_inner_right _ z1).1 huweak
          (∇ Psi z2 - ∇ Psi z1)
        simpa [F, q1] using
          ((tendsto_const_nhds (x := mu⁻¹)).mul hcoord1).add hcoord2
      have hFv : Tendsto (fun n ↦ F (v n)) atTop (nhds q2) := by
        have hcoord1 := (weakConvergence_iff_forall_tendsto_inner_right _ z2).1 hvweak
          (z2 - z1)
        have hcoord2 := (weakConvergence_iff_forall_tendsto_inner_right _ z2).1 hvweak
          (∇ Psi z2 - ∇ Psi z1)
        simpa [F, q2] using
          ((tendsto_const_nhds (x := mu⁻¹)).mul hcoord1).add hcoord2
      have hsame : q1 = q2 := by
        calc
          q1 = l1 - l2 - C := tendsto_nhds_unique hFu (hF.comp hu)
          _ = q2 := (tendsto_nhds_unique hFv (hF.comp hv)).symm
      have hzero : mu⁻¹ * ‖z2 - z1‖ ^ 2 +
          inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) = 0 := by
        calc
          mu⁻¹ * ‖z2 - z1‖ ^ 2 +
              inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) = q2 - q1 := by
            dsimp [q1, q2]
            rw [← real_inner_self_eq_norm_sq (z2 - z1)]
            simp only [inner_sub_left, inner_sub_right, real_inner_comm]
            ring
          _ = 0 := sub_eq_zero.mpr hsame.symm
      have hmon : 0 ≤ inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) := by
        calc
          0 ≤ beta * ‖∇ Psi z2 - ∇ Psi z1‖ ^ 2 :=
            mul_nonneg hbeta.le (sq_nonneg _)
          _ ≤ inner ℝ (∇ Psi z2 - ∇ Psi z1) (z2 - z1) := by
            simpa [real_inner_comm] using
              hB.ineq ⟨z2, Set.mem_univ _⟩ ⟨z1, Set.mem_univ _⟩
      have hsq : ‖z2 - z1‖ ^ 2 = 0 := by
        nlinarith [hzero, hmon, inv_pos.mpr hmu]
      exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))).symm
    have hseq : ∀ u : ℕ → ℝ, Tendsto u atTop atTop → ∃ z : H,
        Tendsto (fun n ↦ toWeakSpace ℝ H (x (u n))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
      intro u hu
      obtain ⟨N, hN⟩ := eventually_atTop.1
        (hu.eventually (eventually_ge_atTop (0 : ℝ)))
      let y : ℕ → H := fun n ↦ x (u (n + N))
      have hybdd : Bornology.IsBounded (Set.range y) := by
        apply isBounded_iff_forall_norm_le.mpr
        refine ⟨R + ‖z0‖, ?_⟩
        rintro w ⟨n, rfl⟩
        calc
          ‖y n‖ = ‖(y n - z0) + z0‖ := by congr 1; abel
          _ ≤ ‖y n - z0‖ + ‖z0‖ := norm_add_le _ _
          _ ≤ R + ‖z0‖ := by
            gcongr
            exact hnorm_bound' (u (n + N)) (hN (n + N) (Nat.le_add_left _ _))
      have hyunique : ∀ z1 z2 : H,
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H z1) →
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (y n)) (toWeakSpace ℝ H z2) → z1 = z2 := by
        intro z1 z2 hz1 hz2
        rcases hz1.exists_subseq_tendsto with ⟨p, hp, hpweak⟩
        rcases hz2.exists_subseq_tendsto with ⟨q, hq, hqweak⟩
        apply hunique_time z1 z2 (fun n ↦ u (p n + N)) (fun n ↦ u (q n + N))
        · exact hu.comp ((Filter.tendsto_add_atTop_nat N).comp hp.tendsto_atTop)
        · exact hu.comp ((Filter.tendsto_add_atTop_nat N).comp hq.tendsto_atTop)
        · simpa [y, Function.comp_def] using hpweak
        · simpa [y, Function.comp_def] using hqweak
      obtain ⟨z, hz⟩ := (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint y).2
        ⟨hybdd, hyunique⟩
      refine ⟨z, ?_⟩
      apply tendsto_of_tendsto_add_nat_local N
      simpa [y] using hz
    have hnat_time : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := by
      simpa using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
    obtain ⟨xinf, hnat⟩ := hseq (fun n : ℕ ↦ (n : ℝ)) hnat_time
    have hxinfS : xinf ∈ S := hcluster xinf (fun n : ℕ ↦ (n : ℝ)) hnat_time hnat
    refine ⟨xinf, hxinfS, ?_⟩
    refine (weakConvergence_iff_forall_tendsto_inner_right x xinf).2 ?_
    intro w
    apply real_tendsto_atTop_of_all_divergent_sequences_local
    intro u hu
    obtain ⟨z, hz⟩ := hseq u hu
    have hzxinf : z = xinf := hunique_time z xinf u (fun n : ℕ ↦ (n : ℝ)) hu hnat_time hz hnat
    simpa [hzxinf] using
      (weakConvergence_iff_forall_tendsto_inner_right (fun n ↦ x (u n)) z).1 hz w
  · intro z hz
    exact ⟨hgradstrong z hz, (integrableOn_Ici_iff_integrableOn_Ioi).mp
      (hgrad_sq_integrable z hz)⟩
```

## Proof explanation
There is a separate proof. The proof is a Lyapunov energy argument combined with weak compactness and cocoercivity estimates.

Throughout the proof, `intro` is used to introduce universally quantified variables and hypotheses, `rw` is used to rewrite using previously proved equalities or derivative formulas, `simp` simplifies inner-product and algebraic expressions, `exact` closes a goal by applying a lemma or hypothesis, and `linarith` combines linear inequalities into the required conclusion. Other tactics such as `calc`, `field_simp`, `ring`, `gcongr`, `nlinarith`, and `filter_upwards` are used for chained inequalities, algebraic simplification, and almost-everywhere estimates.

The proof first derives a base Lyapunov inequality from the lemma `proximal_gradient_cocoercive_lyapunov`. For every \(z\in S\) and \(t\ge 0\),
\[
\frac{d}{dt}\left((2\mu)^{-1}\|x(t)-z\|^2\right)
+\mu^{-1}\|\operatorname{deriv}x(t)\|^2
+\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
+\langle \operatorname{deriv}x(t),\nabla\Psi(x(t))-\nabla\Psi(z)\rangle
\le 0.
\]

Then the proof introduces an energy functional
\[
E(z,t)
=
(2\mu)^{-1}\|x(t)-z\|^2
+
\bigl(
\Psi(x(t))
-\langle\nabla\Psi(z),x(t)-z\rangle
-\Psi(z)
\bigr).
\]
It proves that \(E(z,t)\ge 0\). The first quadratic term is nonnegative, and the remaining Bregman-type term is nonnegative by the lemma `convex_supporting_baillon_haddad`, using convexity and gradient differentiability of \(\Psi\). The proof computes the derivative of \(E(z,t)\):
\[
\partial_t E(z,t)
=
\mu^{-1}\langle x(t)-z,\operatorname{deriv}x(t)\rangle
+
\langle \operatorname{deriv}x(t),\nabla\Psi(x(t))-\nabla\Psi(z)\rangle.
\]
Combining this with the base Lyapunov inequality gives
\[
\partial_t E(z,t)
+
\mu^{-1}\|\operatorname{deriv}x(t)\|^2
+
\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
\le 0.
\]
Since the extra dissipation terms are nonnegative, \(\partial_t E(z,t)\le 0\). Therefore \(E(z,\cdot)\) is antitone on \([0,\infty)\). Because it is also nonnegative, the proof obtains a finite limit \(E(z,t)\to \ell_z\) as \(t\to+\infty\).

Next, the proof establishes continuity of \(\nabla\Psi\). Cocoercivity implies Lipschitz continuity of \(\nabla\Psi\), and hence continuity. The proximal-gradient field
\[
u\mapsto
\operatorname{prox}_{\mu\Phi}(u-\mu\nabla\Psi(u))-u
\]
is also continuous by `proximal_gradient_field_continuous`. From the dynamics equation, for \(t\ge 0\),
\[
\operatorname{deriv}x(t)
=
\operatorname{prox}_{\mu\Phi}(x(t)-\mu\nabla\Psi(x(t)))-x(t).
\]
This equality is used to show that \(\operatorname{deriv}x\) is continuous on compact intervals, since \(x\) is continuous by absolute continuity.

The proof then uses the derivative inequality for \(E\) to obtain an integral bound. For every \(z\in S\) and every \(T>0\),
\[
\int_0^T
\left(
\mu^{-1}\|\operatorname{deriv}x(t)\|^2
+
\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
\right)
\,dt
\le E(z,0).
\]
This is obtained by integrating the Lyapunov inequality, applying the fundamental theorem of calculus to \(\partial_t E(z,t)\), and using \(E(z,T)\ge 0\). Consequently, both \(\|\operatorname{deriv}x(t)\|^2\) and \(\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2\) are integrable on \([0,\infty)\). The proof rescales by \(\mu\) and by \(\beta^{-1}\) to remove the constants \(\mu^{-1}\) and \(\beta\).

The proof then chooses a point \(z_0\in S\). Since \(E(z_0,\cdot)\) is antitone and nonnegative,
\[
(2\mu)^{-1}\|x(t)-z_0\|^2 \le E(z_0,0),
\]
so
\[
\|x(t)-z_0\|^2 \le 2\mu E(z_0,0).
\]
Let
\[
R=\sqrt{2\mu E(z_0,0)}.
\]
Then \(\|x(t)-z_0\|\le R\) for all \(t\ge 0\).

Using the Lipschitz continuity of the proximal-gradient field \(V\), the proof defines
\[
V(u)
=
\operatorname{prox}_{\mu\Phi}(u-\mu\nabla\Psi(u))-u.
\]
If \(L\) is a Lipschitz constant for \(V\), then for
\[
K=\|V(z_0)\|+L R,
\]
one obtains
\[
\|\operatorname{deriv}x(t)\|
=
\|V(x(t))\|
\le
\|V(x(t))-V(z_0)\|+\|V(z_0)\|
\le
L\|x(t)-z_0\|+\|V(z_0)\|
\le
K.
\]
Thus the trajectory \(x\) is \(K\)-Lipschitz on \([0,\infty)\).

Cocoercivity of \(\nabla\Psi\) also gives uniform continuity of \(\nabla\Psi\). Since \(x\) is Lipschitz, the function
\[
t\mapsto \nabla\Psi(x(t))-\nabla\Psi(z)
\]
is uniformly continuous on \([0,\infty)\). This function has square-integrable norm, so by the lemma `uniformContinuousOn_sq_integrable_tendsto_zero`, it tends to \(0\). Therefore
\[
\nabla\Psi(x(t))\to \nabla\Psi(z)
\]
strongly as \(t\to+\infty\). Similarly, because \(V\) is Lipschitz and \(x\) is Lipschitz, \(t\mapsto V(x(t))\) is uniformly continuous. Since \(\operatorname{deriv}x(t)=V(x(t))\) on \([0,\infty)\), the derivative \(\operatorname{deriv}x\) is uniformly continuous and square-integrable, so the same lemma gives
\[
\operatorname{deriv}x(t)\to 0.
\]

The remaining part proves weak convergence of \(x(t)\) to a point in \(S\). The proof first shows a cluster-point property: if \(u_n\to+\infty\) and \(x(u_n)\to z\) weakly, then \(z\in S\). After shifting times by a large \(N\) so that all times are nonnegative, the proof shows that
\[
x(u_{n+N})+\operatorname{deriv}x(u_{n+N})
\to
z
\]
weakly, because \(x(u_{n+N})\to z\) weakly and \(\operatorname{deriv}x(u_{n+N})\to 0\) strongly. It also shows that
\[
-\nabla\Psi(x(u_{n+N}))
-\mu^{-1}\operatorname{deriv}x(u_{n+N})
\to
-\nabla\Psi(z_0)
\]
strongly. For each shifted time, the proximal-gradient dynamics implies
\[
-\nabla\Psi(x(t))-\mu^{-1}\operatorname{deriv}x(t)
\in
\operatorname{subdifferential}\Phi(x(t)+\operatorname{deriv}x(t)).
\]
The subdifferential of \(\Phi\) is maximal monotone because \(\Phi\) is in `gammaZero H`, so its graph is weak-strong closed. Passing to the limit gives
\[
-\nabla\Psi(z_0)\in \operatorname{subdifferential}\Phi(z).
\]
A separate weak-strong closedness lemma for cocoercive operators gives \(\nabla\Psi(z)=\nabla\Psi(z_0)\). Therefore
\[
-\nabla\Psi(z)\in \operatorname{subdifferential}\Phi(z),
\]
and by \(h_{\mathrm{solution}}\), \(z\in S\).

Next, the proof shows uniqueness of the weak cluster point. Suppose \(z_1,z_2\) are two weak cluster points of \(x(t)\). For each \(z\), the energy limit \(E(z,t)\to \ell_z\) exists. Define
\[
F(t)
=
\mu^{-1}\langle x(t),z_2-z_1\rangle
+
\langle x(t),\nabla\Psi(z_2)-\nabla\Psi(z_1)\rangle.
\]
A direct expansion shows that
\[
E(z_1,t)-E(z_2,t)=F(t)+C
\]
for a constant \(C\) depending only on \(z_1,z_2,\Psi\). Hence \(F(t)\) has a limit along \(t\to+\infty\). Along sequences converging weakly to \(z_1\) and \(z_2\), this limit must equal two values \(q_1\) and \(q_2\), respectively. Therefore \(q_1=q_2\). A computation gives
\[
q_2-q_1
=
\mu^{-1}\|z_2-z_1\|^2
+
\langle \nabla\Psi(z_2)-\nabla\Psi(z_1),z_2-z_1\rangle.
\]
Cocoercivity of \(\nabla\Psi\) implies
\[
\langle \nabla\Psi(z_2)-\nabla\Psi(z_1),z_2-z_1\rangle
\ge
\beta\|\nabla\Psi(z_2)-\nabla\Psi(z_1)\|^2
\ge 0.
\]
Since \(\mu^{-1}>0\), the equality \(q_2-q_1=0\) forces \(\|z_2-z_1\|=0\), so \(z_1=z_2\).

Finally, the proof proves that every divergent sequence of times has a weak cluster point. It uses the norm bound \(\|x(t)-z_0\|\le R\), the uniqueness of weak cluster points, and a weak sequential compactness criterion for bounded sequences in Hilbert space. Applying this to the natural time sequence gives a point \(x_{\inf}\in S\), and uniqueness gives that the full trajectory \(x(t)\) converges weakly to \(x_{\inf}\) as \(t\to+\infty\). The proof then assembles the three desired conclusions: weak convergence of \(x(t)\), strong convergence and integrability of the gradient mismatch for every \(z\in S\), and strong convergence of \(\operatorname{deriv}x(t)\) to \(0\).

