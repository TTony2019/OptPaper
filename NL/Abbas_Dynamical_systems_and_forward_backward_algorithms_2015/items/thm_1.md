## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/thm_1.lean`

## Lean statement
```lean
theorem theorem_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (lam beta : ℝ) (x0 v0 : H)
    (hlam : 0 < lam) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (hv0 : v0 ∈ ERealFunction.subdifferential Phi x0) :
    ∃! xv : (ℝ → H) × (ℝ → H),
      IsStrongGlobalSolutionCombined Phi B lam x0 v0 xv.1 xv.2 ∧
      (∀ t, t < 0 → xv.1 t = x0) ∧
      (∀ t, t < 0 → xv.2 t = v0)
```

## Statement explanation
This theorem states existence and uniqueness of a solution to a forward-backward dynamical system in a complete real inner product space \(H\). The data are:

- \(H\) is a normed additive commutative group with a real inner product space structure and is complete.
- \(\Phi : H \to \operatorname{Set.Ioi}(\bot : \mathrm{EReal})\) is an extended-real-valued function whose values are strictly above the bottom element of \(\mathrm{EReal}\).
- \(\Phi\) is assumed to belong to the class \(\mathrm{ERealFunction.gammaZero}\ H\), the gamma-zero class used by the library.
- \(B : H \to H\) is a cocoercive map. Specifically, \(B\) is \(\beta\)-cocoercive on the whole space \(H\).
- \(\lambda, \beta \in \mathbb{R}\) are positive real parameters, with \(0 < \lambda\) and \(0 < \beta\).
- \(x_0, v_0 \in H\) are initial points.
- \(v_0\) is assumed to lie in the subdifferential of \(\Phi\) at \(x_0\), i.e. \(v_0 \in \partial \Phi(x_0)\).

The conclusion asserts that there exists a unique pair \(xv = (x, v)\) of functions \(x, v : \mathbb{R} \to H\) such that:

1. The pair \((x,v)\) is a strong global solution of the combined system,
   \[
   \operatorname{IsStrongGlobalSolutionCombined}\ \Phi\ B\ \lambda\ x_0\ v_0\ x\ v.
   \]
   In the proof this predicate is expanded as:
   - \(x\) and \(v\) are absolutely continuous on every interval \([0,b]\) with \(b>0\);
   - for every \(t \ge 0\), \(v(t) \in \partial \Phi(x(t))\);
   - for almost every \(t \ge 0\),
     \[
     \frac{d}{dt}\bigl(\lambda x(t) + v(t)\bigr) = -(v(t) + B(x(t)));
     \]
   - \(x(0) = x_0\) and \(v(0) = v_0\).

2. For every \(t < 0\), \(x(t) = x_0\).

3. For every \(t < 0\), \(v(t) = v_0\).

Thus the theorem says that the forward-backward combined system has exactly one strong global solution that is constant in the past at the prescribed initial values.

## Lean proof
```lean
by
  have hB_lipschitz : LipschitzWith (Real.toNNReal (1 / beta)) B :=
    cocoercive_implies_lipschitz B beta hB
  let gamma : ERealFunction.PosReal := ⟨lam⁻¹, inv_pos.mpr hlam⟩
  let P : H → H := Prox[gamma, Phi, hPhi]
  have hP_firm : FirmlyNonexpansive P := by
    simpa [P, gamma, ERealFunction.scaledProximityOperator] using
      ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
        (ERealFunction.smul_mem_gammaZero Phi hPhi gamma)
  have hP_lipschitz : LipschitzWith 1 P :=
    lipschitzWith_one_of_firmlyNonexpansive hP_firm
  let F : H → H := fun q => P q - q - lam⁻¹ • B (P q)
  let K : NNReal := Real.toNNReal (2 + |lam⁻¹| / beta)
  have hK_nonneg : 0 ≤ 2 + |lam⁻¹| / beta := by positivity
  have hF_lipschitz : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    rw [show (K : ℝ) = 2 + |lam⁻¹| / beta by
      exact Real.coe_toNNReal _ (by positivity)]
    have hPpq : ‖P p - P q‖ ≤ ‖p - q‖ := by
      simpa [dist_eq_norm] using hP_lipschitz.dist_le_mul p q
    have hBPpq : ‖B (P p) - B (P q)‖ ≤ (1 / beta) * ‖P p - P q‖ := by
      simpa only [dist_eq_norm,
        Real.coe_toNNReal (1 / beta) (one_div_nonneg.mpr hbeta.le)] using
        hB_lipschitz.dist_le_mul (P p) (P q)
    calc
      dist (F p) (F q) = ‖(P p - P q) - (p - q) - lam⁻¹ • (B (P p) - B (P q))‖ := by
        rw [dist_eq_norm]
        congr 1
        simp only [F]
        module
      _ ≤ ‖P p - P q‖ + ‖p - q‖ + ‖lam⁻¹ • (B (P p) - B (P q))‖ := by
        calc
          _ ≤ ‖(P p - P q) - (p - q)‖ + ‖lam⁻¹ • (B (P p) - B (P q))‖ := norm_sub_le _ _
          _ ≤ (‖P p - P q‖ + ‖p - q‖) + ‖lam⁻¹ • (B (P p) - B (P q))‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = _ := by ac_rfl
      _ = ‖P p - P q‖ + ‖p - q‖ + |lam⁻¹| * ‖B (P p) - B (P q)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖p - q‖ + ‖p - q‖ + |lam⁻¹| * ((1 / beta) * ‖p - q‖) := by
        exact add_le_add (add_le_add hPpq le_rfl)
          (mul_le_mul_of_nonneg_left (hBPpq.trans (mul_le_mul_of_nonneg_left hPpq
            (one_div_nonneg.mpr hbeta.le))) (abs_nonneg _))
      _ = (2 + |lam⁻¹| / beta) * dist p q := by
        rw [dist_eq_norm]
        ring
  let q0 : H := x0 + lam⁻¹ • v0
  have hPq0 : P q0 = x0 := by
    rw [show P q0 = Prox[gamma • Phi, ERealFunction.smul_mem_gammaZero Phi hPhi gamma] q0 by
      rfl]
    symm
    apply (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
      (ERealFunction.smul_mem_gammaZero Phi hPhi gamma) q0 x0).2
    rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
    change q0 - x0 ∈ (gamma : ℝ) • ((ERealFunction.subdifferential Phi) x0)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ gamma.2.ne']
    simpa [q0, gamma, smul_smul, mul_inv_cancel₀ hlam.ne'] using hv0
  obtain ⟨z, hz0, hzderiv⟩ := exists_global_solution_of_lipschitz F hF_lipschitz q0
  have hz0' : z 0 = x0 + lam⁻¹ • v0 := by simpa [q0] using hz0
  have hz_continuous : Continuous z := continuous_iff_continuousAt.2 fun t =>
    (hzderiv t).continuousAt
  have hF_continuous : Continuous F := hF_lipschitz.continuous
  have hz_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval z 0 b := by
    intro b hb
    have hFz_continuous : Continuous (fun t => F (z t)) :=
      hF_continuous.comp hz_continuous
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      hFz_continuous.continuousOn
    have hC_nonneg : 0 ≤ C := by
      exact (norm_nonneg _).trans (hC 0 ⟨le_rfl, hb.le⟩)
    have hz_lipschitz : LipschitzOnWith (Real.toNNReal C) z (Set.Icc 0 b) := by
      apply (convex_Icc 0 b).lipschitzOnWith_of_nnnorm_deriv_le
      · intro t ht
        exact (hzderiv t).differentiableAt
      · intro t ht
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hC_nonneg]
        simp only [coe_nnnorm]
        simpa only [(hzderiv t).deriv] using hC t ht
    have hz_lipschitz' : LipschitzOnWith (Real.toNNReal C) z (Set.uIcc 0 b) := by
      simpa only [Set.uIcc_of_le hb.le] using hz_lipschitz
    exact hz_lipschitz'.absolutelyContinuousOnInterval
  let x : ℝ → H := fun t => P (z t)
  let v : ℝ → H := fun t => lam • (z t - x t)
  have hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b := by
    intro b hb
    apply ac_comp_of_lipschitzOn_image_vec (hz_ac b hb)
    exact hP_lipschitz.lipschitzOnWith
  have hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b := by
    intro b hb
    simpa [v] using (hz_ac b hb).sub (hx_ac b hb) |>.const_smul lam
  have hx0 : x 0 = x0 := by
    simpa [x] using (congrArg P hz0).trans hPq0
  have hv0' : v 0 = v0 := by
    simp only [v]
    rw [hx0, hz0']
    calc
      lam • (x0 + lam⁻¹ • v0 - x0) = (lam * lam⁻¹) • v0 := by module
      _ = v0 := by rw [mul_inv_cancel₀ hlam.ne']; simp
  have hv_subgradient : ∀ t, v t ∈ ERealFunction.subdifferential Phi (x t) := by
    intro t
    simpa [v, x, P, gamma] using
      ERealFunction.scaledProximityOperator_residual_mem hPhi gamma (z t)
  have hz_eq : z = fun t => x t + lam⁻¹ • v t := by
    funext t
    simp only [x, v]
    rw [smul_smul, inv_mul_cancel₀ hlam.ne']
    module
  have hF_eq : ∀ t, F (z t) = -lam⁻¹ • (v t + B (x t)) := by
    intro t
    simp only [F, x, v]
    rw [smul_add, smul_smul, neg_mul, inv_mul_cancel₀ hlam.ne']
    module
  have h_combined : ∀ t,
      HasDerivAt (fun s => lam • x s + v s) (-(v t + B (x t))) t := by
    intro t
    have hfun : (fun s => lam • x s + v s) = fun s => lam • z s := by
      funext s
      simp only [x, v]
      module
    rw [hfun]
    convert (hzderiv t).const_smul lam using 1
    rw [hF_eq, smul_smul, mul_neg, mul_inv_cancel₀ hlam.ne']
    module
  let xt : ℝ → H := fun t => if t < 0 then x0 else x t
  let vt : ℝ → H := fun t => if t < 0 then v0 else v t
  have hxt_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval xt 0 b := by
    intro b hb
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    rcases (absolutelyContinuousOnInterval_iff _ _ _).mp (hx_ac b hb) ε hε with
      ⟨δ, hδ, hδ_bound⟩
    refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
    have hbound := hδ_bound (n, I) hnI₁ hnI₂
    apply lt_of_le_of_lt ?_ hbound
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 0 ≤ (I i).1 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).left.1
    have hi2 : 0 ≤ (I i).2 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).right.1
    rw [show xt (I i).1 = x (I i).1 by simp [xt, not_lt.mpr hi1],
      show xt (I i).2 = x (I i).2 by simp [xt, not_lt.mpr hi2]]
  have hvt_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval vt 0 b := by
    intro b hb
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    rcases (absolutelyContinuousOnInterval_iff _ _ _).mp (hv_ac b hb) ε hε with
      ⟨δ, hδ, hδ_bound⟩
    refine ⟨δ, hδ, fun (n, I) hnI₁ hnI₂ => ?_⟩
    have hbound := hδ_bound (n, I) hnI₁ hnI₂
    apply lt_of_le_of_lt ?_ hbound
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 0 ≤ (I i).1 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).left.1
    have hi2 : 0 ≤ (I i).2 := by
      simpa [min_eq_left hb.le] using (hnI₁.left i hi).right.1
    rw [show vt (I i).1 = v (I i).1 by simp [vt, not_lt.mpr hi1],
      show vt (I i).2 = v (I i).2 by simp [vt, not_lt.mpr hi2]]
  have hpositive_ae : ∀ᵐ t ∂volume.restrict (Set.Ici (0 : ℝ)), 0 < t := by
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    exact ae_restrict_mem measurableSet_Ioi
  have ht_combined : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      HasDerivAt (fun s => lam • xt s + vt s) (-(vt t + B (xt t))) t := by
    filter_upwards [hpositive_ae] with t htpos
    have hxt_eq : xt =ᶠ[nhds t] x := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      have hs0 : 0 < s := hs
      simp [xt, not_lt.mpr hs0.le]
    have hvt_eq : vt =ᶠ[nhds t] v := by
      filter_upwards [Ioi_mem_nhds htpos] with s hs
      have hs0 : 0 < s := hs
      simp [vt, not_lt.mpr hs0.le]
    have hcombined_eq : (fun s => lam • xt s + vt s) =ᶠ[nhds t]
        (fun s => lam • x s + v s) := hxt_eq.const_smul lam |>.add hvt_eq
    simpa [xt, vt, not_lt.mpr htpos.le] using
      (h_combined t).congr_of_eventuallyEq hcombined_eq
  have h_exists :
      IsStrongGlobalSolutionCombined Phi B lam x0 v0 xt vt ∧
      (∀ t, t < 0 → xt t = x0) ∧
      (∀ t, t < 0 → vt t = v0) := by
    refine ⟨⟨hxt_ac, hvt_ac, ?_, ht_combined, ?_, ?_⟩, ?_, ?_⟩
    · intro t ht
      simpa [xt, vt, not_lt.mpr ht] using hv_subgradient t
    · simpa [xt, not_lt.mpr le_rfl] using hx0
    · simpa [vt, not_lt.mpr le_rfl] using hv0'
    · intro t ht
      simp [xt, ht]
    · intro t ht
      simp [vt, ht]
  refine ⟨⟨xt, vt⟩, h_exists, ?_⟩
  intro y hy
  rcases hy with ⟨⟨hyx_ac, hyv_ac, hy_subgradient, hy_combined,
    hyx0, hyv0⟩, hyx_neg, hyv_neg⟩
  let q : ℝ → H := fun t => y.1 t + lam⁻¹ • y.2 t
  have hq_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval q 0 b := by
    intro b hb
    simpa [q] using (hyx_ac b hb).add ((hyv_ac b hb).const_smul lam⁻¹)
  have hq0 : q 0 = q0 := by
    simp [q, q0, hyx0, hyv0]
  have hy_prox : ∀ t, 0 ≤ t → y.1 t = P (q t) := by
    intro t ht
    rw [show P (q t) = Prox[gamma • Phi,
      ERealFunction.smul_mem_gammaZero Phi hPhi gamma] (q t) by rfl]
    apply (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
      (ERealFunction.smul_mem_gammaZero Phi hPhi gamma) (q t) (y.1 t)).2
    rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
    change q t - y.1 t ∈
      (gamma : ℝ) • ((ERealFunction.subdifferential Phi) (y.1 t))
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ gamma.2.ne']
    simpa [q, gamma, smul_smul, mul_inv_cancel₀ hlam.ne'] using hy_subgradient t ht
  have hy_combined_volume : ∀ᵐ t ∂volume,
      t ∈ Set.Ici 0 → HasDerivAt (fun s => lam • y.1 s + y.2 s)
        (-(y.2 t + B (y.1 t))) t := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hy_combined
  have hq_dynamics_Icc (b : ℝ) (hb : 0 < b) :
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt q (F (q t)) t := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hy_combined_volume] with t hdyn ht
    have hcandidate_dyn := hdyn (Set.mem_Ici.mpr ht.1)
    have hqDA : HasDerivAt q (-lam⁻¹ • (y.2 t + B (y.1 t))) t := by
      have hqfun : q = fun s => lam⁻¹ • (lam • y.1 s + y.2 s) := by
        funext s
        simp only [q, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      have hscaled := hcandidate_dyn.const_smul lam⁻¹
      rw [hqfun]
      convert hscaled using 1
      module
    have hFq : F (q t) = -lam⁻¹ • (y.2 t + B (y.1 t)) := by
      simp only [F, q]
      rw [← hy_prox t ht.1]
      module
    rw [hFq]
    exact hqDA
  have hq_right (b : ℝ) (hb : 0 < b) : ∀ t ∈ Set.Ico 0 b,
      HasDerivWithinAt q (F (q t)) (Set.Ici t) t := by
    have hFq_cont : ContinuousOn (fun t => F (q t)) (Set.Icc 0 b) :=
      hF_continuous.continuousOn.comp (by
        simpa only [Set.uIcc_of_le hb.le] using (hq_ac b hb).continuousOn)
        (fun _ _ => Set.mem_univ _)
    exact ac_hasDerivWithinAt_right_of_ae_hasDerivAt hb.le (hq_ac b hb)
      hFq_cont (hq_dynamics_Icc b hb)
  have hq_eq_z_Icc (b : ℝ) (hb : 0 < b) : Set.EqOn q z (Set.Icc 0 b) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ : ℝ => F) (s := fun _ => Set.univ) (K := K)
    · intro t ht
      exact hF_lipschitz.lipschitzOnWith
    · simpa only [Set.uIcc_of_le hb.le] using (hq_ac b hb).continuousOn
    · exact hq_right b hb
    · intro t ht
      exact Set.mem_univ _
    · exact hz_continuous.continuousOn
    · intro t ht
      exact (hzderiv t).hasDerivWithinAt
    · intro t ht
      exact Set.mem_univ _
    · exact hq0.trans hz0.symm
  have hq_eq_z (t : ℝ) (ht : 0 ≤ t) : q t = z t := by
    exact hq_eq_z_Icc (t + 1) (by linarith) ⟨ht, by linarith⟩
  have hyx_eq (t : ℝ) (ht : 0 ≤ t) : y.1 t = xt t := by
    rw [show xt t = x t by simp [xt, not_lt.mpr ht], hy_prox t ht, hq_eq_z t ht]
  have hyv_recover (t : ℝ) : y.2 t = lam • (q t - y.1 t) := by
    simp [q]
    rw [smul_smul, mul_inv_cancel₀ hlam.ne']
    module
  have hyv_eq (t : ℝ) (ht : 0 ≤ t) : y.2 t = vt t := by
    rw [hyv_recover t, hq_eq_z t ht]
    have hyx : y.1 t = x t := by
      simpa [xt, not_lt.mpr ht] using hyx_eq t ht
    rw [hyx]
    simp [vt, v, not_lt.mpr ht]
  apply Prod.ext <;> funext t
  · by_cases ht : t < 0
    · simp [hyx_neg t ht, xt, ht]
    · exact hyx_eq t (le_of_not_gt ht)
  · by_cases ht : t < 0
    · simp [hyv_neg t ht, vt, ht]
    · exact hyv_eq t (le_of_not_gt ht)
```

## Proof explanation
The proof is constructive: it builds the solution using a proximity operator and an auxiliary ODE, then proves uniqueness by reduction to uniqueness for that ODE.

Throughout, `intro` fixes arbitrary objects or hypotheses, `rw` and `simp` rewrite using definitions and equalities, `exact` closes a goal with an already-known fact, `module` and `ring` handle vector-space and real-number arithmetic, and `linarith` solves linear inequalities.

**Step 1: Lipschitz constants and the auxiliary map \(F\).**

First, the proof uses the cocoercivity assumption on \(B\) to obtain a Lipschitz constant:
\[
\operatorname{LipschitzWith}\Bigl(\frac{1}{\beta}\Bigr)\ B.
\]
This is the standard fact that a \(\beta\)-cocoercive map is \(1/\beta\)-Lipschitz.

It then defines the positive parameter
\[
\gamma = \lambda^{-1},
\]
using the positivity of \(\lambda\). It defines the proximity operator
\[
P = \operatorname{Prox}[\gamma,\Phi,h_\Phi],
\]
the proximal operator associated with the scaled function \(\gamma \Phi\). Because \(\Phi\) is gamma-zero and \(\gamma\) is positive, the scaled proximity operator is firmly nonexpansive, hence \(P\) is \(1\)-Lipschitz.

Then the proof defines the auxiliary vector field
\[
F(q) = P(q) - q - \lambda^{-1}\cdot B(P(q)).
\]
It proves that \(F\) is Lipschitz with constant
\[
K = \operatorname{Real.toNNReal}\left(2 + \frac{|\lambda^{-1}|}{\beta}\right).
\]
For two points \(p,q\), the estimate is
\[
\|F(p)-F(q)\|
\le \|P(p)-P(q)\| + \|p-q\|
+ |\lambda^{-1}|\,\|B(P(p))-B(P(q))\|.
\]
Using that \(P\) is \(1\)-Lipschitz,
\[
\|P(p)-P(q)\| \le \|p-q\|,
\]
and using that \(B\) is \(1/\beta\)-Lipschitz,
\[
\|B(P(p))-B(P(q))\| \le \frac{1}{\beta}\|P(p)-P(q)\|
\le \frac{1}{\beta}\|p-q\|,
\]
the proof obtains
\[
\|F(p)-F(q)\|
\le \left(2+\frac{|\lambda^{-1}|}{\beta}\right)\|p-q\|.
\]
This is done with a `calc` chain using triangle inequalities, `norm_sub_le`, `norm_smul`, and `ring` for the final real arithmetic.

**Step 2: Initial condition for the proximal equation.**

The proof defines
\[
q_0 = x_0 + \lambda^{-1} v_0.
\]
It then proves
\[
P(q_0) = x_0.
\]
This uses the characterization of the proximity operator:
\[
P(q_0)=x_0
\iff q_0 - x_0 \in \partial(\gamma\Phi)(x_0).
\]
The subdifferential of the scaled function is rewritten using
\[
\partial(\gamma\Phi)(x_0) = \gamma\,\partial\Phi(x_0).
\]
Thus it suffices to show
\[
\gamma^{-1}(q_0-x_0) \in \partial\Phi(x_0).
\]
Since \(\gamma = \lambda^{-1}\), we have \(\gamma^{-1}=\lambda\), and
\[
\lambda(q_0-x_0)=\lambda(\lambda^{-1}v_0)=v_0.
\]
The assumption \(v_0 \in \partial\Phi(x_0)\) gives exactly the desired membership. The Lean proof uses `eq_proximityOperator_iff_sub_mem_subdifferential`, `subdifferential_posReal_smul_eq_smul`, and `Set.mem_smul_set_iff_inv_smul_mem₀`.

**Step 3: Auxiliary global ODE solution \(z\).**

Using the global existence theorem for Lipschitz ODEs,
\[
\operatorname{exists\_global\_solution\_of\_lipschitz}\ F\ hF_{\mathrm{lipschitz}}\ q_0,
\]
the proof obtains a function
\[
z : \mathbb{R} \to H
\]
satisfying
\[
z(0) = q_0, \qquad z'(t) = F(z(t))
\]
for all \(t\).

The proof then shows that \(z\) is absolutely continuous on every interval \([0,b]\), \(b>0\). First, differentiability gives continuity of \(z\). Since \(F\) is Lipschitz, \(F\) is continuous, so \(t \mapsto F(z(t))\) is continuous. On the compact interval \([0,b]\), this continuous function is bounded by some constant \(C\). The derivative bound gives a Lipschitz bound on \(z\), which implies absolute continuity. This uses `lipschitzOnWith_of_nnnorm_deriv_le` and `absolutelyContinuousOnInterval`.

**Step 4: Construction of the candidate pair \((x,v)\).**

Define
\[
x(t) = P(z(t)), \qquad v(t) = \lambda(z(t)-x(t)).
\]
The proof verifies:

- \(x\) is absolutely continuous on every \([0,b]\), because it is the composition of the absolutely continuous \(z\) with the Lipschitz map \(P\).
- \(v\) is absolutely continuous on every \([0,b]\), because it is a scalar multiple of the difference \(z-x\).
- \(x(0)=x_0\), using \(z(0)=q_0\) and \(P(q_0)=x_0\).
- \(v(0)=v_0\), using the definition of \(q_0\):
  \[
  v(0)=\lambda(x_0+\lambda^{-1}v_0-x_0)=v_0.
  \]
- For every \(t\), \(v(t)\in \partial\Phi(x(t))\). This follows from the residual property of the proximity operator:
  \[
  v(t)=\lambda(z(t)-P(z(t)))\in \partial\Phi(P(z(t))).
  \]
- The identity
  \[
  z(t) = x(t) + \lambda^{-1}v(t)
  \]
  holds for all \(t\).
- The auxiliary vector field satisfies
  \[
  F(z(t)) = -\lambda^{-1}(v(t)+B(x(t))).
  \]
- Therefore, from \(z'(t)=F(z(t))\), the proof derives the pointwise derivative
  \[
  \frac{d}{dt}\bigl(\lambda x(t)+v(t)\bigr)
  = -(v(t)+B(x(t))).
  \]
  This is because \(\lambda x(t)+v(t)=\lambda z(t)\), and
  \[
  \lambda z'(t)=\lambda F(z(t))
  = -\lambda\lambda^{-1}(v(t)+B(x(t)))
  = -(v(t)+B(x(t))).
  \]

**Step 5: Extension to negative time.**

The candidate solution is extended before time \(0\) by the constant initial values:
\[
\widetilde{x}(t)=
\begin{cases}
x_0, & t<0,\\
x(t), & t\ge 0,
\end{cases}
\qquad
\widetilde{v}(t)=
\begin{cases}
v_0, & t<0,\\
v(t), & t\ge 0.
\end{cases}
\]
In Lean these are defined with `if t < 0 then ... else ...`.

The proof checks that \(\widetilde{x}\) and \(\widetilde{v}\) are still absolutely continuous on \([0,b]\) for every \(b>0\). This uses the epsilon-delta criterion for absolute continuity. For any family of subintervals inside \([0,b]\), the endpoints are nonnegative, so on those endpoints the `if` branches reduce to the original \(x\) and \(v\). The inequality is then inherited from the absolute continuity of \(x\) and \(v\). The Lean commands `absolutelyContinuousOnInterval_iff`, `Finset.sum_le_sum`, and simplification of the `if` conditions are used here.

It also checks that the derivative equation holds almost everywhere on \([0,\infty)\). For almost every \(t>0\), the extended functions coincide with \(x\) and \(v\) in a neighborhood of \(t\), so the pointwise derivative identity from Step 4 transfers to the extended functions. This uses `filter_upwards` and `Ioi_mem_nhds`.

Finally, the proof assembles the five required properties of `IsStrongGlobalSolutionCombined`:

- absolute continuity of \(\widetilde{x}\) and \(\widetilde{v}\);
- subdifferential inclusion for \(t\ge 0\);
- the almost-everywhere differential equation for \(t\ge 0\);
- initial conditions \(\widetilde{x}(0)=x_0\) and \(\widetilde{v}(0)=v_0\).

It also verifies the two negative-time constancy conditions. This proves existence.

**Step 6: Uniqueness.**

Suppose \(y=(y_1,y_2)\) is another pair satisfying the strong solution conditions and the negative-time constancy conditions. Define
\[
q(t) = y_1(t) + \lambda^{-1} y_2(t).
\]
Then \(q\) is absolutely continuous on every \([0,b]\), and
\[
q(0)=q_0.
\]
Using the subdifferential inclusion for \(y\),
\[
y_2(t)\in \partial\Phi(y_1(t)),
\]
the same proximity-operator characterization implies
\[
y_1(t)=P(q(t))
\]
for every \(t\ge 0\).

The proof then uses the differential equation for \(y\) to derive an ODE for \(q\). It shows that for almost every \(t\in[0,b]\),
\[
q'(t)=F(q(t)).
\]
Passing to right derivatives on \([0,b)\), it obtains
\[
\operatorname{HasDerivWithinAt}\ q\ (F(q(t)))\ (\operatorname{Set.Ici} t)\ t
\]
for all \(t\in[0,b)\). This uses `ac_hasDerivWithinAt_right_of_ae_hasDerivAt` and the continuity of \(F\circ q\).

Now both \(q\) and \(z\) are solutions of the same ODE with the same initial value:
\[
q(0)=q_0=z(0), \qquad q' = F(q), \quad z'=F(z).
\]
Since \(F\) is Lipschitz, the uniqueness theorem for ODEs on intervals,
`ODE_solution_unique_of_mem_Icc_right`, implies
\[
q(t)=z(t)
\]
on every \([0,b]\), hence for all \(t\ge 0\).

Therefore, for \(t\ge 0\),
\[
y_1(t)=P(q(t))=P(z(t))=x(t)=\widetilde{x}(t).
\]
Also, from the definition of \(q\),
\[
y_2(t)=\lambda(q(t)-y_1(t)),
\]
so for \(t\ge 0\),
\[
y_2(t)=\lambda(z(t)-x(t))=v(t)=\widetilde{v}(t).
\]
For \(t<0\), the negative-time constancy conditions give
\[
y_1(t)=x_0=\widetilde{x}(t), \qquad
y_2(t)=v_0=\widetilde{v}(t).
\]
Thus \(y_1=\widetilde{x}\) and \(y_2=\widetilde{v}\). The proof concludes using `Prod.ext` and `funext` to prove equality of the pair of functions. This gives uniqueness.

