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
The theorem `proximal_gradient_gradient_case` is a convergence theorem for a continuous-time proximal-gradient trajectory in a real Hilbert space $H$, formalized as a complete real inner product space. The extended-real function $\Phi : H \to \mathrm{Set}_{\mathrm{Ioi}(\bot)}(\mathrm{EReal})$, with hypothesis `hPhi`, belongs to the class $\Gamma_0(H)$: it is a proper convex lower semicontinuous function with values in $`\mathbb R \cup \{+\infty\}`$. The function$\Psi : H \to \mathbb R$is convex on all of$H$, has gradient$\nabla \Psi$, and its gradient map is$\beta$-cocoercive on all of$H$, meaning that for all$u,v \in H$,

```math
\beta \|\nabla \Psi(u)-\nabla \Psi(v)\|^2
\le \langle u-v,\nabla \Psi(u)-\nabla \Psi(v)\rangle .
```

The set $S$ is nonempty and is the solution set characterized by

$$
z \in S \quad\Longleftrightarrow\quad -\nabla \Psi(z) \in \partial \Phi(z),
$$

where $\partial \Phi$ is the convex subdifferential. Thus $S$ is the set of critical points of $\Phi+\Psi$, equivalently the set of zeros of $\partial \Phi+\nabla \Psi$.

The parameters satisfy $\mu\gt 0$ and $\beta\gt 0$. The trajectory $x : \mathbb R \to H$ is differentiable on $t \ge 0$, absolutely continuous on every interval $[0,b]$ with $b\gt 0$, and satisfies the proximal-gradient differential equation

```math
\dot x(t)+x(t)-\mathrm{prox}_{\mu \Phi}\!\bigl(x(t)-\mu \nabla \Psi(x(t))\bigr)=0,
\qquad t \ge 0,
```

or equivalently

```math
\dot x(t)=\mathrm{prox}_{\mu \Phi}\!\bigl(x(t)-\mu \nabla \Psi(x(t))\bigr)-x(t).
```

Here $\mathrm{prox}_{\mu \Phi}$ denotes the scaled proximity operator of $\mu \Phi$, as given by `ERealFunction.scaledProximityOperator`.

The conclusion has three parts. First, there exists $x_\infty \in S$ such that $x(t)$ converges weakly to $x_\infty$ as $t \to \infty$, formalized by convergence in the weak topology via `toWeakSpace`. Second, for every $z \in S$, the gradients converge strongly,

$$
\nabla \Psi(x(t)) \to \nabla \Psi(z),
$$

and the squared error is integrable on $(0,\infty)$:

```math
\int_0^\infty \|\nabla \Psi(x(t))-\nabla \Psi(z)\|^2\,dt < \infty.
```

Third, the velocity tends to zero,

$$
\dot x(t) \to 0.
$$

So the theorem says that, under convexity and cocoercivity of the gradient of $\Psi$, the proximal-gradient flow converges weakly to a stationary point of $\Phi+\Psi$, the gradients converge to the corresponding limiting gradient, the squared gradient discrepancy is integrable, and the trajectory slows down to zero velocity.

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
The proof begins by applying `proximal_gradient_cocoercive_lyapunov` with $B=\nabla \Psi$. That cited result assumes $\Phi \in \Gamma_0(H)$, $B$ is $\beta$-cocoercive, $S$ is characterized by $z \in S \iff -Bz \in \partial \Phi(z)$, and the trajectory satisfies the same proximal dynamics. It provides the pointwise Lyapunov inequality: for every $z \in S$ and every $t \ge 0$,

```math
\frac{d}{dt}\!\left(\frac{1}{2\mu}\|x(t)-z\|^2\right)
+\frac1\mu\|\dot x(t)\|^2
+\beta\|\nabla \Psi(x(t))-\nabla \Psi(z)\|^2
+\langle \dot x(t),\nabla \Psi(x(t))-\nabla \Psi(z)\rangle \le 0.
```

This is the basic energy dissipation inequality. The first term is the derivative of a quadratic distance to the solution $z$, the second is kinetic energy, the third is the cocoercive dissipation, and the final inner product couples the velocity with the gradient difference.

Next the proof defines the Lyapunov-type function

```math
E(z,t)
=\frac{1}{2\mu}\|x(t)-z\|^2
+\Psi(x(t))-\langle \nabla \Psi(z),x(t)-z\rangle-\Psi(z).
```

The second line is the Bregman divergence of $\Psi$ between $x(t)$ and $z$, plus a linear correction. The proof shows $E(z,t)\ge 0$ for all $z,t$. It uses `convex_supporting_baillon_haddad`, which for a convex differentiable function $\Psi$ says

$$
\Psi(z)+\langle \nabla \Psi(z),u-z\rangle \le \Psi(u).
$$

Taking $u=x(t)$, the Bregman part is nonnegative. The quadratic part is also nonnegative because $\mu\gt 0$. The tactic `linarith` combines these nonnegativities to prove $E(z,t)\ge0$.

Then the proof computes the derivative of $E(z,\cdot)$. The chain rule is applied to $t \mapsto \Psi(x(t))$, using `hPsi_grad (x t)` and `hderiv t ht`. The derivative of $t \mapsto \langle \nabla \Psi(z),x(t)-z\rangle$ is $\langle \nabla \Psi(z),\dot x(t)\rangle$. The derivative of the quadratic term is $\mu^{-1}\langle x(t)-z,\dot x(t)\rangle$. Hence

$$
\frac{d}{dt}E(z,t)
=\mu^{-1}\langle x(t)-z,\dot x(t)\rangle
+\langle \dot x(t),\nabla \Psi(x(t))-\nabla \Psi(z)\rangle.
$$

The Lean commands `convert`, `simp`, and `ring` are used to match the derivative of the sum with this formula and to simplify inner-product algebra.

Substituting this derivative formula into the initial Lyapunov inequality gives: for every $z \in S$ and $t \ge 0$,

```math
\frac{d}{dt}E(z,t)
+\frac1\mu\|\dot x(t)\|^2
+\beta\|\nabla \Psi(x(t))-\nabla \Psi(z)\|^2
\le 0.
```

The proof obtains this by rewriting the derivative of the quadratic term and using `linarith`. Since the last two terms are nonnegative, it follows that

$$
\frac{d}{dt}E(z,t)\le 0
$$

for all $t\ge0$. The theorem `antitoneOn_of_deriv_nonpos` then implies that $E(z,\cdot)$ is antitone on $[0,\infty)$: it is continuous on $[0,\infty)$, differentiable on the interior, and has nonpositive derivative there. Because $E(z,t)\ge0$, the theorem `tendsto_of_antitone_nonneg_on_Ici` gives a finite limit:

$$
E(z,t) \to \ell_z \quad \text{as } t\to\infty.
$$

This is a standard fact: a nonnegative antitone real function on $[0,\infty)$ has a limit in $[0,\infty)$.

The proof next establishes continuity of the relevant fields. The lemma `lipschitzWith_of_cocoercive` says that a cocoercive map is Lipschitz with constant $\mathrm{toNNReal}(1/\beta)$. Since $\nabla\Psi$ is cocoercive by `hB`, it is continuous. The theorem `proximal_gradient_field_continuous` then gives continuity of the proximal-gradient field

```math
u \mapsto \mathrm{prox}_{\mu\Phi}\!\bigl(u-\mu\nabla\Psi(u)\bigr)-u.
```

From the dynamics, the proof rewrites the derivative as

```math
\dot x(t)
=\mathrm{prox}_{\mu\Phi}\!\bigl(x(t)-\mu\nabla\Psi(x(t))\bigr)-x(t).
```

Using that $x$ is continuous on every $[0,T]$ by absolute continuity, and that the field above is continuous, the proof obtains continuity of $\dot x$ on every $[0,T]$. It also obtains continuity of the dissipation integrand

```math
t \mapsto \mu^{-1}\|\dot x(t)\|^2
+\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2.
```

The proof then derives the crucial finite-energy estimate. For fixed $z\in S$ and $T\gt 0$, the Lyapunov inequality gives

```math
\mu^{-1}\|\dot x(t)\|^2
+\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
\le -\frac{d}{dt}E(z,t)
```

for all $t\in[0,T]$. Both sides are interval integrable. The theorem `intervalIntegral.integral_mono_ae_restrict` allows integrating this almost-everywhere inequality over $[0,T]$. The integral of $-\frac{d}{dt}E(z,t)$ is

```math
-\int_0^T \frac{d}{dt}E(z,t)\,dt
=-(E(z,T)-E(z,0))
=E(z,0)-E(z,T).
```

Since $E(z,T)\ge0$, this is at most $E(z,0)$. Therefore

```math
\int_0^T\left(
\mu^{-1}\|\dot x(t)\|^2
+\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
\right)dt
\le E(z,0).
```

From this uniform bound on finite intervals, the proof proves global integrability. It applies `integrableOn_Ici_of_nonneg_interval_bound` to

```math
g(t)=\mu^{-1}\|\dot x(t)\|^2.
```

The lemma requires local integrability on intervals $(0,T]$, nonnegativity on $[0,\infty)$, and a uniform bound on the integrals up to $T$. These hold because of the continuity just established and the finite-energy estimate. Thus

```math
\int_0^\infty \mu^{-1}\|\dot x(t)\|^2\,dt < \infty.
```

Multiplying by $\mu$ and cancelling $\mu\mu^{-1}=1$ gives

```math
\int_0^\infty \|\dot x(t)\|^2\,dt < \infty.
```

The same argument applied to

```math
g(t)=\beta\|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2
```

gives, after multiplying by $\beta^{-1}$,

```math
\int_0^\infty \|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2\,dt < \infty.
```

This proves the integrability part of the second conclusion.

The proof then shows that the trajectory is bounded. Since $S$ is nonempty, choose $z_0\in S$. Again using the convex supporting inequality for $\Psi$, the Bregman term in $E(z_0,t)$ is nonnegative. Since $E(z_0,\cdot)$ is antitone, $E(z_0,t)\le E(z_0,0)$. Therefore the quadratic part satisfies

```math
\frac{1}{2\mu}\|x(t)-z_0\|^2 \le E(z_0,0),
```

so

```math
\|x(t)-z_0\|^2 \le 2\mu E(z_0,0).
```

Let

$$
R=\sqrt{2\mu E(z_0,0)}.
$$

Then $R\ge0$ and $`\|x(t)-z_0\|\le R`$for all$t\ge0$. This gives a uniform bound on the trajectory relative to the fixed solution$z_0$.

The theorem `proximal_gradient_field_lipschitz` supplies a nonnegative constant $L$ such that the field

```math
V(u)
=\mathrm{prox}_{\mu\Phi}\!\bigl(u-\mu\nabla\Psi(u)\bigr)-u
```

is Lipschitz with constant $L$. Since $\dot x(t)=V(x(t))$, the proof bounds the velocity by

```math
\|\dot x(t)\|
\le \|V(x(t))-V(z_0)\|+\|V(z_0)\|
\le L\|x(t)-z_0\|+\|V(z_0)\|
\le LR+\|V(z_0)\|.
```

Thus the derivative of $x$ is uniformly bounded on $[0,\infty)$. The theorem `lipschitzOnWith_of_nnnorm_deriv_le` for convex domains then implies that $x$ is Lipschitz on $[0,\infty)$ with constant $`K=LR+\|V(z_0)\|`$. In particular,$x$is uniformly continuous on$[0,\infty)$.

Next the proof proves gradient convergence. The theorem `cocoercive_uniformContinuous` says that a cocoercive map is uniformly continuous, so $\nabla\Psi$ is uniformly continuous. Since $x$ is Lipschitz on $[0,\infty)$, the composition $t\mapsto \nabla\Psi(x(t))$ is uniformly continuous on $[0,\infty)$. Subtracting the constant $\nabla\Psi(z)$ gives uniform continuity of

$$
t\mapsto \nabla\Psi(x(t))-\nabla\Psi(z).
$$

Its squared norm is integrable by the earlier integrability result. The theorem `uniformContinuousOn_sq_integrable_tendsto_zero` states that a uniformly continuous function on $[0,\infty)$ whose squared norm is integrable must tend to zero at infinity. Applying it gives

$$
\nabla\Psi(x(t))-\nabla\Psi(z) \to 0,
$$

hence

$$
\nabla\Psi(x(t)) \to \nabla\Psi(z).
$$

This proves the gradient convergence part of the second conclusion.

Similarly, because $V$ is Lipschitz and $x$ is Lipschitz on $[0,\infty)$, the composition $t\mapsto V(x(t))=\dot x(t)$ is uniformly continuous on $[0,\infty)$. Its squared norm is integrable by the earlier result. Applying `uniformContinuousOn_sq_integrable_tendsto_zero` again gives

$$
\dot x(t)\to 0.
$$

This proves the third conclusion.

The remaining and most delicate part is the weak convergence of $x(t)$. The proof first shows that every weak sequential cluster point of the trajectory is a solution. Suppose $u:\mathbb N\to\mathbb R$ tends to infinity and $x(u_n)\rightharpoonup z$ weakly. After shifting the sequence by a large $N$, one may assume all times are nonnegative. Along this shifted sequence, the gradient converges strongly:

$$
\nabla\Psi(x(u_{n+N}))\to \nabla\Psi(z_0),
$$

because $z_0\in S$ and the previous strong-gradient convergence applies. Also $\dot x(u_{n+N})\to0$.

The proof then shows that

$$
x(u_{n+N})+\dot x(u_{n+N})\rightharpoonup z
$$

weakly. This uses `weakConvergence_iff_forall_tendsto_inner_right`, which says that weak convergence is equivalent to convergence of all inner products. For any vector $v$, the inner product with $x(u_{n+N})+\dot x(u_{n+N})$ is the sum of the inner product with $x(u_{n+N})$, which converges to $\langle z,v\rangle$, and the inner product with $\dot x(u_{n+N})$, which tends to zero.

It also shows the strong convergence

$$
-\nabla\Psi(x(u_{n+N}))
-\mu^{-1}\dot x(u_{n+N})
\to -\nabla\Psi(z_0).
$$

For each $n$, the theorem `proximal_gradient_classical_subgradient` gives the subgradient inclusion

$$
-\nabla\Psi(x(t_n))-\mu^{-1}\dot x(t_n)
\in
\partial\Phi\bigl(x(t_n)+\dot x(t_n)\bigr),
$$

where $t_n=u_{n+N}$. This is the classical subgradient identity for proximal-gradient dynamics.

The theorem `subdifferential_isMaximalMonotone_of_mem_gammaZero` says that since $\Phi\in\Gamma_0(H)$, the subdifferential operator $\partial\Phi$ is maximal monotone. The lemma `maximal_monotone_graph_weak_strong_closed` then states that the graph of a maximal monotone operator is closed under weak convergence in the first variable and strong convergence in the second variable. Applying it with $T=\partial\Phi$, weak limit $z$, and strong limit $-\nabla\Psi(z_0)$, the proof obtains

$$
-\nabla\Psi(z_0)\in \partial\Phi(z).
$$

The lemma `cocoercive_weak_strong_closed` is then applied to the cocoercive gradient map: from $x(u_{n+N})\rightharpoonup z$ and $\nabla\Psi(x(u_{n+N}))\to\nabla\Psi(z_0)$, it concludes

$$
\nabla\Psi(z)=\nabla\Psi(z_0).
$$

Substituting this into the subdifferential inclusion gives

$$
-\nabla\Psi(z)\in\partial\Phi(z),
$$

so by the characterization of $S$, $z\in S$. Thus every weak sequential cluster point of the trajectory belongs to $S$.

The proof then shows uniqueness of such limits. If two sequences tending to infinity produce weak limits $z_1$ and $z_2$, then both are in $S$. The Lyapunov functions $E(z_1,\cdot)$ and $E(z_2,\cdot)$ have finite limits. The proof writes

$$
E(z_1,t)-E(z_2,t)=F(t)+C
$$

for an explicit affine-in- $x(t)$ function $F$ and a constant $C$. Taking limits along the two sequences and using the weak convergence of $x$ gives two limiting values $q_1$ and $q_2$. Since both must equal the same limit of $E(z_1,\cdot)-E(z_2,\cdot)$, one obtains $q_1=q_2$. Computing $q_2-q_1$ yields

```math
\mu^{-1}\|z_2-z_1\|^2
+\langle \nabla\Psi(z_2)-\nabla\Psi(z_1),z_2-z_1\rangle=0.
```

Cocoercivity of $\nabla\Psi$ gives

```math
0\le \beta\|\nabla\Psi(z_2)-\nabla\Psi(z_1)\|^2
\le
\langle \nabla\Psi(z_2)-\nabla\Psi(z_1),z_2-z_1\rangle.
```

Therefore the second term in the sum is nonnegative, while the first is also nonnegative. Their sum being zero forces both to be zero, hence $z_2=z_1$. Thus there is at most one weak sequential cluster point.

Now the proof uses `weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint`. This theorem states that a sequence has a weak limit if and only if its range is bounded and it has at most one weak sequential cluster point. The trajectory along any divergent sequence is bounded by the earlier estimate $`\|x(t)-z_0\|\le R`$, and the uniqueness argument just given says there is at most one weak sequential cluster point. Therefore every divergent sequence of times has a weakly convergent subsequence, and in fact the whole shifted sequence has a weak limit. The lemma `tendsto_of_tendsto_add_nat_local` removes the finite shift $N$. Hence for every sequence $u_n\to\infty$, there exists $z$ such that $x(u_n)\rightharpoonup z$.

Applying this to the natural sequence $n\mapsto n$, the proof obtains $x_\infty\in S$ and $x(n)\rightharpoonup x_\infty$. To upgrade this to convergence along the continuous parameter $t\to\infty$, the proof uses `real_tendsto_atTop_of_all_divergent_sequences_local`: if every sequence $u_n\to\infty$ has $f(u_n)\to a$, then $f(t)\to a$ as $t\to\infty$. For any such sequence, the previous paragraph gives a weak limit $z$ along $u_n$, and uniqueness of weak cluster points compared with the natural sequence gives $z=x_\infty$. Then `weakConvergence_iff_forall_tendsto_inner_right` translates weak convergence along $u_n$ into convergence of all inner products. Since this holds for every divergent sequence, the theorem gives convergence of each inner product as $t\to\infty$, and another application of `weakConvergence_iff_forall_tendsto_inner_right` upgrades this to weak convergence

$$
x(t)\rightharpoonup x_\infty.
$$

Thus the first conclusion is proved.

Finally, the proof assembles the three conclusions. The first conjunct is the weak convergence to some $x_\infty\in S$. For the second conjunct, for each $z\in S$, the already proved strong gradient convergence gives

$$
\nabla\Psi(x(t))\to\nabla\Psi(z),
$$

and the earlier integrability result, converted from $[0,\infty)$ to $(0,\infty)$ using `integrableOn_Ici_iff_integrableOn_Ioi`, gives

```math
\int_0^\infty \|\nabla\Psi(x(t))-\nabla\Psi(z)\|^2\,dt<\infty.
```

The third conjunct is the already proved velocity convergence $\dot x(t)\to0$. This completes the proof.

