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
In a complete real Hilbert space \(H\), let
\[
\Phi:H\to (-\infty,+\infty]
\]
be an extended-real-valued function in the admissible class denoted \(\Gamma_0(H)\) by the hypothesis `hPhi`, and let
\[
B:H\to H
\]
be a \(\beta\)-cocoercive map on all of \(H\), as expressed by `hB`. The cocoercivity condition is the standard one: for all \(x,y\in H\),
\[
\langle B x-B y,x-y\rangle \ge \beta\|B x-B y\|^2,
\]
which in particular will imply that \(B\) is Lipschitz with constant \(1/\beta\). The parameters satisfy \(\lambda>0\) and \(\beta>0\), and the initial data are \(x_0,v_0\in H\). The final hypothesis is
\[
v_0\in \partial\Phi(x_0),
\]
meaning that \(v_0\) is a subgradient of \(\Phi\) at \(x_0\): for every \(y\in H\),
\[
\langle y-x_0,v_0\rangle+\Phi(x_0)\le \Phi(y),
\]
with the inequality interpreted in the extended real numbers.

The theorem asserts that there exists a unique pair of trajectories
\[
(x,v):\mathbb R\to H\times H
\]
such that the following conditions hold. First, \(x\) and \(v\) are absolutely continuous on every interval \([0,b]\) with \(b>0\). Second, for every \(t\ge 0\),
\[
v(t)\in \partial\Phi(x(t)).
\]
Third, for almost every \(t\ge 0\) with respect to volume restricted to \([0,\infty)\),
\[
\frac{d}{dt}\bigl(\lambda x(t)+v(t)\bigr)
=
-\bigl(v(t)+B(x(t))\bigr).
\]
Fourth, the initial conditions are
\[
x(0)=x_0,\qquad v(0)=v_0.
\]
Finally, the pair is extended constantly to negative times:
\[
t<0\implies x(t)=x_0,\qquad t<0\implies v(t)=v_0.
\]
Thus the theorem gives global existence and uniqueness of a strong solution to a subgradient differential inclusion combined with an ordinary differential equation, with the left half-line filled in by the constant initial values.

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
The proof first converts the cocoercivity of \(B\) into a Lipschitz estimate. Applying `cocoercive_implies_lipschitz` to \(B\), \(\beta\), and `hB` gives
\[
\operatorname{LipschitzWith}(\operatorname{toNNReal}(1/\beta))\,B.
\]
Concretely, for all \(p,q\in H\),
\[
\|B p-B q\|\le \frac1\beta\|p-q\|.
\]
This estimate is used later to show that the auxiliary vector field \(F\) below is Lipschitz.

Next the proof introduces the positive real
\[
\gamma=\lambda^{-1}
\]
and the scaled proximity operator
\[
P=\operatorname{Prox}[\gamma,\Phi,hPhi].
\]
Since \(\gamma>0\), the lemma `smul_mem_gammaZero` says that \(\gamma\Phi\) again belongs to \(\Gamma_0(H)\). Therefore the proximity operator of \(\gamma\Phi\) exists, and the theorem `proximityOperator_firmlyNonexpansive_of_mem_gammaZero` says that it is firmly nonexpansive. Because \(P\) is precisely the proximity operator of \(\gamma\Phi\), this gives
\[
P \text{ is firmly nonexpansive}.
\]
For a map on a Hilbert space, firm nonexpansiveness means
\[
\|P p-P q\|^2\le \langle P p-P q,p-q\rangle,
\]
and the lemma `lipschitzWith_one_of_firmlyNonexpansive` converts this into the ordinary estimate
\[
\|P p-P q\|\le \|p-q\|.
\]
So \(P\) is \(1\)-Lipschitz.

The proof then defines
\[
F(q)=P(q)-q-\lambda^{-1}B(P(q)).
\]
It wants \(F\) to be globally Lipschitz. Let
\[
K=\operatorname{toNNReal}\bigl(2+|\lambda^{-1}|/\beta\bigr).
\]
For \(p,q\in H\), the triangle inequality gives
\[
\|F(p)-F(q)\|
\le
\|P(p)-P(q)\|+\|p-q\|+|\lambda^{-1}|\,\|B(P(p))-B(P(q))\|.
\]
Using \(\|P(p)-P(q)\|\le\|p-q\|\) and
\[
\|B(P(p))-B(P(q))\|\le \frac1\beta\|P(p)-P(q)\|\le \frac1\beta\|p-q\|,
\]
the right-hand side is at most
\[
\|p-q\|+\|p-q\|+|\lambda^{-1}|\frac1\beta\|p-q\|
=
\left(2+\frac{|\lambda^{-1}|}{\beta}\right)\|p-q\|.
\]
Thus \(F\) is Lipschitz with constant \(K\). In the Lean proof this is the block using `LipschitzWith.of_dist_le_mul`, `norm_sub_le`, `norm_smul`, `gcongr`, and algebraic simplification with `ring` and `ac_rfl`.

A crucial compatibility step is the identity
\[
P\bigl(x_0+\lambda^{-1}v_0\bigr)=x_0.
\]
Let \(q_0=x_0+\lambda^{-1}v_0\). Since \(P\) is the proximity operator of \(\gamma\Phi\), the characterization
\[
p=\operatorname{Prox}[f,hf](x)
\quad\Longleftrightarrow\quad
x-p\in\partial f(p)
\]
from `eq_proximityOperator_iff_sub_mem_subdifferential` says it is enough to prove
\[
q_0-x_0\in\partial(\gamma\Phi)(x_0).
\]
The lemma `subdifferential_posReal_smul_eq_smul` gives
\[
\partial(\gamma\Phi)=\gamma\,\partial\Phi.
\]
Because \(\gamma=\lambda^{-1}>0\), membership in \(\gamma\partial\Phi(x_0)\) is equivalent to
\[
\gamma^{-1}(q_0-x_0)\in\partial\Phi(x_0).
\]
But
\[
\gamma^{-1}(q_0-x_0)
=
\lambda\bigl((x_0+\lambda^{-1}v_0)-x_0\bigr)
=
v_0,
\]
and \(v_0\in\partial\Phi(x_0)\) is exactly `hv0`. Hence the proximal optimality condition holds and \(P(q_0)=x_0\).

The proof then solves the ODE
\[
z'(t)=F(z(t)),\qquad z(0)=q_0.
\]
The lemma `exists_global_solution_of_lipschitz` applies because \(F\) is Lipschitz on the complete space \(H\). It gives a global trajectory \(z:\mathbb R\to H\) satisfying
\[
z(0)=q_0,\qquad \forall t,\ \operatorname{HasDerivAt} z\,(F(z(t)))\,t.
\]
In particular \(z\) is differentiable everywhere, hence continuous. Since \(F\) is Lipschitz, \(F\) is continuous, so \(t\mapsto F(z(t))\) is continuous. For each \(b>0\), this continuous function is bounded on the compact interval \([0,b]\) by some \(C\). The derivative bound
\[
\|z'(t)\|=\|F(z(t))\|\le C
\]
on \([0,b]\) then implies that \(z\) is Lipschitz on \([0,b]\), using `convex_Icc.lipschitzOnWith_of_nnnorm_deriv_le`. Lipschitz functions on intervals are absolutely continuous, so
\[
z \text{ is absolutely continuous on } [0,b]
\]
for every \(b>0\).

Now define
\[
x(t)=P(z(t)),\qquad v(t)=\lambda(z(t)-x(t)).
\]
The absolute continuity of \(x\) follows from that of \(z\) and the Lipschitzness of \(P\) via `ac_comp_of_lipschitzOn_image_vec`: if \(z\) is absolutely continuous on an interval and \(P\) is Lipschitz on the image of that interval, then \(P\circ z\) is absolutely continuous there. Since \(P\) is globally \(1\)-Lipschitz, this hypothesis is immediate. The absolute continuity of \(v\) follows because \(v\) is a scalar multiple of the difference of the absolutely continuous functions \(z\) and \(x\).

The initial values are
\[
x(0)=P(z(0))=P(q_0)=x_0,
\]
and
\[
v(0)=\lambda(z(0)-x(0))
=
\lambda(q_0-x_0)
=
\lambda(\lambda^{-1}v_0)
=
v_0.
\]
The subgradient condition is obtained from `scaledProximityOperator_residual_mem`, which says that for \(f\in\Gamma_0(H)\) and \(\gamma>0\),
\[
\gamma^{-1}\bigl(z-\operatorname{Prox}[\gamma,f](z)\bigr)
\in
\partial f\bigl(\operatorname{Prox}[\gamma,f](z)\bigr).
\]
Here \(f=\Phi\), \(\gamma=\lambda^{-1}\), and \(P(z(t))=x(t)\), so
\[
\lambda(z(t)-x(t))=v(t)\in\partial\Phi(x(t)).
\]
This proves the required inclusion for every \(t\).

The differential equation is also a direct consequence of the construction. Since
\[
v=\lambda(z-x),
\]
we have
\[
z=x+\lambda^{-1}v,
\]
hence
\[
\lambda x+v=\lambda z.
\]
Also,
\[
F(z(t))
=
P(z(t))-z(t)-\lambda^{-1}B(P(z(t)))
=
x(t)-z(t)-\lambda^{-1}B(x(t))
=
-\lambda^{-1}\bigl(v(t)+B(x(t))\bigr).
\]
Therefore, differentiating \(\lambda x+v=\lambda z\) and using \(z'=F(z)\), we get
\[
\frac{d}{dt}\bigl(\lambda x(t)+v(t)\bigr)
=
\lambda F(z(t))
=
-\bigl(v(t)+B(x(t))\bigr).
\]
Thus the combined differential equation holds for all \(t\), hence almost everywhere on \([0,\infty)\).

To get the desired negative-time behavior, the proof defines
\[
x_t(t)=
\begin{cases}
x_0,&t<0,\\
x(t),&t\ge 0,
\end{cases}
\qquad
v_t(t)=
\begin{cases}
v_0,&t<0,\\
v(t),&t\ge 0.
\end{cases}
\]
On any interval \([0,b]\), these functions agree with \(x\) and \(v\), so they inherit absolute continuity. The subgradient condition and the differential equation hold on \([0,\infty)\). The initial conditions hold at \(0\), and the negative-time conditions are true by definition. For the almost-everywhere derivative statement, the proof uses the fact that almost every \(t\) in \([0,\infty)\) is strictly positive, so near such a \(t\) the functions \(x_t\) and \(v_t\) are eventually equal to \(x\) and \(v\). This is formalized with `hpositive_ae`, `MeasureTheory.restrict_Ioi_eq_restrict_Ici`, and `filter_upwards`. Hence existence of the pair \((x_t,v_t)\) is established.

For uniqueness, suppose \((y_1,y_2)\) is any other pair satisfying the same strong-solution conditions and the negative-time constant conditions. Define
\[
q(t)=y_1(t)+\lambda^{-1}y_2(t).
\]
Then \(q\) is absolutely continuous on each \([0,b]\), because it is a sum of an absolutely continuous function and a scalar multiple of an absolutely continuous function. Also,
\[
q(0)=x_0+\lambda^{-1}v_0=q_0.
\]
For \(t\ge 0\), the proof shows
\[
y_1(t)=P(q(t)).
\]
Indeed, by the scaled proximal characterization, it is enough to prove
\[
q(t)-y_1(t)\in\partial(\gamma\Phi)(y_1(t)).
\]
Using \(\partial(\gamma\Phi)=\gamma\partial\Phi\), this is equivalent to
\[
\gamma^{-1}\bigl(q(t)-y_1(t)\bigr)\in\partial\Phi(y_1(t)).
\]
But \(\gamma^{-1}=\lambda\) and
\[
\gamma^{-1}(q(t)-y_1(t))
=
\lambda\bigl(y_1(t)+\lambda^{-1}y_2(t)-y_1(t)\bigr)
=
y_2(t),
\]
and \(y_2(t)\in\partial\Phi(y_1(t))\) is part of the assumed strong-solution data. Thus \(y_1(t)=P(q(t))\).

Next the proof shows that \(q\) solves the same ODE as \(z\). From the assumed differential equation for \((y_1,y_2)\), for almost every \(t\ge 0\),
\[
\frac{d}{dt}\bigl(\lambda y_1(t)+y_2(t)\bigr)
=
-\bigl(y_2(t)+B(y_1(t))\bigr).
\]
Since
\[
q=\lambda^{-1}(\lambda y_1+y_2),
\]
differentiating gives
\[
q'(t)
=
-\lambda^{-1}\bigl(y_2(t)+B(y_1(t))\bigr).
\]
Using \(y_1(t)=P(q(t))\) and \(q(t)=y_1(t)+\lambda^{-1}y_2(t)\), the right-hand side becomes
\[
P(q(t))-q(t)-\lambda^{-1}B(P(q(t)))
=
F(q(t)).
\]
Thus \(q'=F(q)\) almost everywhere on \([0,b]\).

The proof then upgrades this almost-everywhere derivative to a right derivative using `ac_hasDerivWithinAt_right_of_ae_hasDerivAt`. Specialized here, that result says: if an absolutely continuous function on \([0,b]\) has almost everywhere derivative equal to a continuous function \(g\), then for every \(t\in[0,b)\), its right derivative at \(t\) is \(g(t)\). Applying this with \(g(t)=F(q(t))\) gives
\[
\forall t\in[0,b),\quad
\operatorname{HasDerivWithinAt} q\,(F(q(t)))\,([t,\infty))\,t.
\]
Now both \(q\) and \(z\) are continuous on \([0,b]\), have the same initial value \(q(0)=q_0=z(0)\), and satisfy the same ODE \(u'=F(u)\) on \([0,b]\), with \(q\) in right-derivative form and \(z\) in ordinary derivative form. Since \(F\) is Lipschitz with constant \(K\), the ODE uniqueness lemma `ODE_solution_unique_of_mem_Icc_right` applies. Its consequence in this situation is exactly
\[
q(t)=z(t)\qquad\text{for all }t\in[0,b].
\]
Because \(b>0\) is arbitrary, this gives \(q(t)=z(t)\) for every \(t\ge 0\).

Therefore, for \(t\ge 0\),
\[
y_1(t)=P(q(t))=P(z(t))=x(t)=x_t(t),
\]
and
\[
y_2(t)=\lambda(q(t)-y_1(t))
=
\lambda(z(t)-x(t))
=
v(t)=v_t(t).
\]
For \(t<0\), the assumed negative-time conditions on \((y_1,y_2)\) give \(y_1(t)=x_0=x_t(t)\) and \(y_2(t)=v_0=v_t(t)\). Hence \(y_1=x_t\) and \(y_2=v_t\) as functions. The final Lean steps use `Prod.ext` to split equality of the pair into equality of the two components, `funext` to prove equality of functions pointwise, and `by_cases` to split into the cases \(t<0\) and \(t\ge 0\). This completes the uniqueness proof.

Throughout, tactics such as `rw`, `simp`, `ring`, and `module` perform definitional and algebraic rewrites; `gcongr` proves the needed inequalities term by term; `filter_upwards` combines almost-everywhere statements; `convert` transfers derivative statements along eventually-equal functions; and `linarith` handles the arithmetic needed to choose positive interval endpoints.

