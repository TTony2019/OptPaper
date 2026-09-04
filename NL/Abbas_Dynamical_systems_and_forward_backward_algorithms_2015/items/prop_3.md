## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/prop_3.lean`

## Lean statement
```lean
theorem proposition_2_16 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (z : H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hz : z ∈ S)
    (hlam : 0 < lam) (hmu : 0 < mu) (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf))) :
    Integrable (fun t ↦ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
      inner ℝ (B z) (x t - z)) (volume.restrict (Set.Ici 0)) ∧
    Tendsto (fun t ↦ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
      inner ℝ (B z) (x t - z)) atTop (nhds 0) ∧
    ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)) ∧
      Tendsto (fun t ↦ (Phi (x t) : EReal).toReal) atTop
        (nhds (Phi xinf : EReal).toReal)
```

## Statement explanation
The theorem assumes a real Hilbert space \(H\), a set \(S\subseteq H\), and an extended-real-valued function \(\Phi\), represented as a function from \(H\) into the subtype of \(\mathrm{EReal}\) values strictly above the bottom element. The hypothesis \(hPhi\) states that \(\Phi\) belongs to the class \(\mathrm{ERealFunction.gammaZero}(H)\). There is also a map \(B:H\to H\), a point \(z\in H\), and functions \(x,v:\mathbb R\to H\). The scalars are \(\lambda,\mu,\beta\in\mathbb R\).

The main assumptions are as follows.

- \(S\) is nonempty and \(z\in S\).
- \(\lambda>0\), \(\mu>0\), and \(\mu\lambda=1\).
- \(\beta>0\).
- \(B\) is \(\beta\)-cocoercive on the whole space: for all \(u,w\),
  \[
  \beta\|B(u)-B(w)\|^2\le \langle u-w,B(u)-B(w)\rangle.
  \]
- For every \(b>0\), \(x\) and \(v\) are absolutely continuous on the interval \([0,b]\).
- On every interval \([0,T]\), almost everywhere,
  \[
  x'(t)=\operatorname{deriv}x(t),\qquad v'(t)=\operatorname{deriv}v(t).
  \]
- For every \(t\ge 0\), \(v(t)\in\partial\Phi(x(t))\), the subdifferential of \(\Phi\) at \(x(t)\).
- For every \(b>0\), \(v\) and \(\operatorname{deriv}x\) are \(L^2\)-integrable on \([0,b]\).
- Almost everywhere on \([0,\infty)\),
  \[
  v(t)\in\partial\Phi(x(t))
  \]
  and
  \[
  \lambda x'(t)+v'(t)+v(t)+B(x(t))=0.
  \]
- For every \(w\in S\), \(-B(w)\in\partial\Phi(w)\).
- For every \(t\ge 0\), \(x(t)\) lies in the effective domain of \(\Phi\), and every \(w\in S\) also lies in the effective domain.
- There exists some \(x_\infty\in S\) such that \(x(t)\) converges weakly to \(x_\infty\) as \(t\to\infty\).

Define
\[
F(t)=(\Phi(x(t)))_{\mathbb R}-(\Phi(z))_{\mathbb R}
+\langle B(z),x(t)-z\rangle,
\]
where \((\cdot)_{\mathbb R}\) denotes the real coercion of an extended real number.

The theorem concludes three things:

1. \(F\) is integrable with respect to Lebesgue measure restricted to \([0,\infty)\).
2. \(F(t)\to 0\) as \(t\to\infty\).
3. There exists \(x_\infty\in S\) such that \(x(t)\rightharpoonup x_\infty\) weakly and
   \[
   (\Phi(x(t)))_{\mathbb R}\to(\Phi(x_\infty))_{\mathbb R}.
   \]

## Lean proof
```lean
by
  have hp := proposition_2_12 S Phi hPhi B x v z lam mu beta hS hz hlam hmu
    hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2
    horbit hsolution hdom
  rcases hp with ⟨hGamma_anti, hGamma_lim, hBsq, hx_bound, hdx_sq, hres_sq,
    hdv_sq, hv_bound, henergy_lim⟩
  let F : ℝ → ℝ := fun t ↦ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
    inner ℝ (B z) (x t - z)
  have hF_nonneg : ∀ t, 0 ≤ t → 0 ≤ F t := by
    intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsolution z hz) (hdom.1 t ht)
    dsimp [F]
    rw [real_inner_comm]
    rw [inner_neg_left, real_inner_comm] at hineq
    linarith
  have hphi_chain : ∀ T, 0 < T →
      AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (Phi (x s) : EReal).toReal) t = inner ℝ (v t) (deriv x t) := by
    intro T hT
    apply subgradient_chain_rule Phi hPhi x v T hT (hx_ac T hT)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hsubgradient t ht.1
    · intro t ht
      exact hdom.1 t ht.1
    · exact hx_deriv T hT
    · exact hvL2 T hT
    · exact hdxL2 T hT
  let Gamma : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))
  have hGamma_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval Gamma 0 T := by
    intro T hT
    have hx0 := hx_ac T hT
    have hconstx : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hconstp : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => (Phi z : EReal).toReal) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hi : AbsolutelyContinuousOnInterval
        (fun t => inner ℝ (z - x t) (v t)) 0 T := by
      have hi' := prop216_inner_ac (hx0.sub hconstx) (hv_ac T hT)
      convert hi'.neg using 1
      funext t
      simp [inner_sub_left]
    have ht : AbsolutelyContinuousOnInterval
        (fun t ↦ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
          inner ℝ (z - x t) (v t)) 0 T :=
      (hconstp.sub (hphi_chain T hT).1).sub hi
    simpa [Gamma] using
      (prop216_sqdist_ac hx0 z).add (ht.const_mul mu)
  have hderivGamma : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv Gamma t + mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
    intro T hT
    have hmonoSub : SetValuedOperator.IsMonotone
        (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
      ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
    have hinner : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        0 ≤ inner ℝ (deriv x t) (deriv v t) := by
      have hh : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
          0 ≤ inner ℝ (deriv x t) (deriv v t) := by
        filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
            Set.Ioc_subset_Icc_self (hx_deriv T hT),
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset
            Set.Ioc_subset_Icc_self (hv_deriv T hT),
          ae_restrict_mem measurableSet_Ioc] with t hxt hvt ht
        exact prop216_inner_deriv_nonneg hmonoSub hsubgradient ht.1 hxt hvt
      rw [MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc] at hh
      exact hh
    have horbT := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
    filter_upwards [hx_deriv T hT, hv_deriv T hT, (hphi_chain T hT).2,
      hinner, horbT, ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae (hphi_chain T hT).1.ae_differentiableAt] with
      t hxt hvt hphit hdt horb ht hphid
    have hphi' := (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hxt.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hin : HasDerivAt (fun s ↦ inner ℝ (z - x s) (v s))
        (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
      convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1
      simp [inner_sub_left, real_inner_comm]
      ring
    have hG : HasDerivAt Gamma
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      have hh := ((((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi').sub
          hin).const_mul mu)
      convert hsq.add hh using 1
      simp only [inner_sub_left, real_inner_comm]
      rw [hphit]
      ring
    have hmono := hmonoSub (v t) horb.1 (-B z) (hsolution z hz)
    have hmono' : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      rw [real_inner_comm]
      simpa [inner_sub_right, inner_add_right, inner_neg_right] using hmono
    have hcoco := hB.ineq ⟨x t, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hcoco' : beta * ‖B (x t) - B z‖ ^ 2 ≤
        inner ℝ (x t - z) (B (x t) - B z) := hcoco
    have horb' := prop216_orbit_inner_identity lam mu hmu_lam (x t - z)
      (deriv x t) (deriv v t) (v t + B (x t)) (by simpa [add_assoc] using horb.2)
    have hsplit : inner ℝ (x t - z) (v t + B (x t)) =
        inner ℝ (x t - z) (v t + B z) +
          inner ℝ (x t - z) (B (x t) - B z) := by
      rw [show B (x t) = B z + (B (x t) - B z) by abel]
      simp only [inner_add_right]
      abel_nf
    rw [inner_sub_right] at hcoco'
    rw [inner_add_right] at horb'
    have horb_scalar : inner ℝ (x t - z) (deriv x t) +
        mu * inner ℝ (x t - z) (deriv v t) +
        mu * inner ℝ (x t - z) (v t + B (x t)) = 0 := by
      simpa [mul_add, add_assoc] using horb'
    rw [hsplit] at horb_scalar
    have hmono_mu := mul_nonneg hmu.le (by simpa [inner_add_right] using hmono')
    have hcoco_mu := mul_le_mul_of_nonneg_left hcoco' hmu.le
    have hinnerB : inner ℝ (x t - z) (B (x t) - B z) =
        inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z) := by
      rw [inner_sub_right]
    have hcoco_mu' : mu * beta * ‖B (x t) - B z‖ ^ 2 ≤
        mu * inner ℝ (x t - z) (B (x t) - B z) := by
      rw [hinnerB]
      simpa [mul_assoc] using hcoco_mu
    have hsub := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      horb.1 (hdom.2 z hz)
    rw [show z - x t = -(x t - z) by abel, inner_neg_right, real_inner_comm] at hsub
    have hFle : F t ≤ inner ℝ (x t - z) (v t) + inner ℝ (B z) (x t - z) := by
      dsimp [F]
      linarith
    have hinnerBz : inner ℝ (B z) (x t - z) = inner ℝ (x t - z) (B z) :=
      real_inner_comm _ _
    rw [hinnerBz] at hFle
    have hFle_mu := mul_le_mul_of_nonneg_left hFle hmu.le
    have hmono_mu' : 0 ≤ mu * (inner ℝ (x t - z) (v t) + inner ℝ (x t - z) (B z)) := by
      simpa [inner_add_right] using hmono_mu
    rw [inner_add_right] at horb_scalar
    rw [hinnerB] at horb_scalar
    rw [hinnerB] at hcoco_mu'
    have horb_scalar' : inner ℝ (x t - z) (deriv x t) +
        mu * inner ℝ (x t - z) (deriv v t) +
        mu * (inner ℝ (x t - z) (v t) + inner ℝ (x t - z) (B z)) +
        mu * (inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z)) = 0 := by
      linarith [horb_scalar]
    rw [hG.deriv]
    linarith [horb_scalar', hmono_mu', hFle_mu, hcoco_mu']
  have hq_local : ∀ T, 0 < T →
      IntegrableOn (fun t => mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2) (Set.Ioc 0 T) := by
    intro T hT
    have hxc : ContinuousOn x (Set.uIcc 0 T) := (hx_ac T hT).continuousOn
    have hcF : ContinuousOn F (Set.Icc 0 T) := by
      have hpc : ContinuousOn (fun t => (Phi (x t) : EReal).toReal)
          (Set.Icc 0 T) := (hphi_chain T hT).1.continuousOn.mono Set.Icc_subset_uIcc
      have hxc' : ContinuousOn x (Set.Icc 0 T) := hxc.mono Set.Icc_subset_uIcc
      have hi : ContinuousOn (fun t => inner ℝ (B z) (x t - z)) (Set.Icc 0 T) :=
        continuousOn_const.inner (hxc'.sub continuousOn_const)
      simpa [F] using (hpc.sub continuousOn_const).add hi
    have hcB : ContinuousOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) := by
      have hBc : Continuous B :=
        (lipschitzWith_of_cocoercive hB).continuous.comp
          (continuous_id.subtype_mk fun _ => Set.mem_univ _)
      exact ((hBc.continuousOn.comp (hxc.mono Set.Icc_subset_uIcc)
          (Set.mapsTo_univ x _)).sub
        continuousOn_const).norm.pow 2
    have hiF : IntegrableOn (fun t => mu * F t) (Set.Icc 0 T) :=
      (hcF.const_mul mu).integrableOn_Icc
    have hiB : IntegrableOn (fun t => mu * beta * ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      (hcB.const_mul (mu * beta)).integrableOn_Icc
    exact (hiF.add hiB).mono_set Set.Ioc_subset_Icc_self
  have hq_int : Integrable (fun t => mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    apply prop216_dissipation_on_Ici (F := Gamma)
      (q := fun t => mu * F t + mu * beta * ‖B (x t) - B z‖ ^ 2) (L := 0)
      hGamma_ac hq_local
      (fun t ht => add_nonneg (mul_nonneg hmu.le (hF_nonneg t ht))
        (mul_nonneg (mul_nonneg hmu.le hbeta.le) (sq_nonneg _)))
      (fun t ht => by
        have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
          (hsubgradient t ht) (hdom.2 z hz)
        rw [real_inner_comm] at hineq
        dsimp [Gamma]
        nlinarith [sq_nonneg (‖x t - z‖)])
      (by simpa [add_assoc] using hderivGamma)
  have hF_int : Integrable F (volume.restrict (Set.Ici 0)) := by
    have hmuF : Integrable (fun t => mu * F t) (volume.restrict (Set.Ici 0)) := by
      convert hq_int.sub (hBsq.const_mul (mu * beta)) using 1
      funext t
      dsimp
      ring
    convert hmuF.const_mul mu⁻¹ using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ hmu.ne', one_mul]
  have hFlim : Tendsto F atTop (nhds 0) := by
    obtain ⟨C, hC⟩ := hv_bound
    let G : ℝ → ℝ := fun t ↦ (C + ‖B z‖) * ‖deriv x t‖
    have hCnonneg : 0 ≤ C := by
      have hC0 := hC 0 le_rfl
      exact le_trans (norm_nonneg (v 0)) hC0
    have hG_nonneg : ∀ t, 0 ≤ G t := by
      intro t
      dsimp [G]
      exact mul_nonneg (add_nonneg hCnonneg (norm_nonneg _)) (norm_nonneg _)
    have hnorm_meas : AEStronglyMeasurable (fun t ↦ ‖deriv x t‖)
        (volume.restrict (Set.Ici 0)) := by
      apply AEMeasurable.aestronglyMeasurable
      convert hdx_sq.aestronglyMeasurable.aemeasurable.sqrt using 1
      funext t
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hG_meas : AEStronglyMeasurable G (volume.restrict (Set.Ici 0)) := by
      dsimp [G]
      exact hnorm_meas.const_mul _
    have hG_sq : Integrable (fun t ↦ G t ^ 2)
        (volume.restrict (Set.Ici 0)) := by
      convert hdx_sq.const_mul ((C + ‖B z‖) ^ 2) using 1
      funext t
      dsimp [G]
      ring
    have hG : MemLp G 2 (volume.restrict (Set.Ici 0)) := by
      rw [memLp_two_iff_integrable_sq_norm hG_meas]
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg _)] using hG_sq
    have hderivF0 : ∀ n : ℕ, ∀ᵐ t ∂volume, t ∈ Set.Icc (0 : ℝ) (n + 1) →
        deriv F t ≤ G t := by
      intro n
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hlocal : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) ((n : ℝ) + 1)), deriv F t ≤ G t := by
        filter_upwards [hx_deriv (n + 1) hn, (hphi_chain (n + 1) hn).2,
          MeasureTheory.ae_restrict_of_ae (hphi_chain (n + 1) hn).1.ae_differentiableAt,
          ae_restrict_mem measurableSet_Icc] with t hxt hphit hphid ht
        have hphi' := (hphid (by simpa [Set.uIcc_of_le hn.le] using ht)).hasDerivAt
        have hi : HasDerivAt (fun s ↦ inner ℝ (B z) (x s - z))
            (inner ℝ (B z) (deriv x t)) t := by
          simpa [inner_sub_right] using
            ((hasDerivAt_const (x := t) (B z)).inner ℝ (hxt.sub_const z))
        have hF' := ((hphi'.sub_const ((Phi z : EReal).toReal)).add hi)
        have hFd : deriv F t = inner ℝ (v t) (deriv x t) +
            inner ℝ (B z) (deriv x t) := by
          dsimp [F]
          simpa [hphit] using hF'.deriv
        rw [hFd]
        have hC' := hC t ht.1
        have hinner : inner ℝ (v t) (deriv x t) + inner ℝ (B z) (deriv x t) ≤
            (‖v t‖ + ‖B z‖) * ‖deriv x t‖ := by
          calc
            _ ≤ |inner ℝ (v t) (deriv x t)| + |inner ℝ (B z) (deriv x t)| := by
              linarith [le_abs_self (inner ℝ (v t) (deriv x t)),
                le_abs_self (inner ℝ (B z) (deriv x t))]
            _ ≤ ‖v t‖ * ‖deriv x t‖ + ‖B z‖ * ‖deriv x t‖ := by
              gcongr
              · exact abs_real_inner_le_norm _ _
              · exact abs_real_inner_le_norm _ _
            _ = (‖v t‖ + ‖B z‖) * ‖deriv x t‖ := by ring
        have hcoef : (‖v t‖ + ‖B z‖) * ‖deriv x t‖ ≤ G t := by
          dsimp [G]
          gcongr
        exact hinner.trans hcoef
      exact (ae_restrict_iff' (s := Set.Icc (0 : ℝ) (n + 1)) measurableSet_Icc).mp hlocal
    have hderivF : ∀ᵐ t ∂volume.restrict (Set.Ici 0), deriv F t ≤ G t := by
      rw [ae_restrict_iff' measurableSet_Ici]
      have hall : ∀ᵐ t ∂volume, ∀ n : ℕ,
          t ∈ Set.Icc (0 : ℝ) (n + 1) → deriv F t ≤ G t :=
        ae_all_iff.2 hderivF0
      filter_upwards [hall] with t ht htn
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ht n ⟨htn, by linarith⟩
    have hF_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval F 0 T := by
      intro T hT
      have hconstz : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) 0 T :=
        contDiffOn_const.absolutelyContinuousOnInterval
      have hi : AbsolutelyContinuousOnInterval
          (fun t => inner ℝ (B z) (x t - z)) 0 T := by
        exact prop216_inner_ac (contDiffOn_const.absolutelyContinuousOnInterval)
          ((hx_ac T hT).sub hconstz)
      have hconstp : AbsolutelyContinuousOnInterval (fun _ : ℝ => (Phi z : EReal).toReal) 0 T :=
        contDiffOn_const.absolutelyContinuousOnInterval
      simpa [F] using (((hphi_chain T hT).1.sub hconstp).add hi)
    exact prop216_limit_zero_of_memLp_deriv_bound_Ici F G 1 2
      (by norm_num) (by norm_num) (by norm_num) hF_nonneg
      hF_ac (memLp_one_iff_integrable.mpr hF_int) hG hderivF
  refine ⟨hF_int, ?_, ?_⟩
  · simpa [F] using hFlim
  · rcases hweak with ⟨xinf, hxinfS, hxweak⟩
    have hmonoSub : SetValuedOperator.IsMonotone
        (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
      ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
    have hmono := hmonoSub (-B xinf) (hsolution xinf hxinfS) (-B z) (hsolution z hz)
    have hmono' : inner ℝ (xinf - z) (B xinf - B z) ≤ 0 := by
      have hm : 0 ≤ inner ℝ (xinf - z) (-B xinf + B z) := by
        simpa [real_inner_comm] using hmono
      have heq : inner ℝ (xinf - z) (B xinf - B z) =
          -inner ℝ (xinf - z) (-B xinf + B z) := by
        simp only [inner_sub_right, inner_add_right, inner_neg_right]
        ring
      rw [heq]
      exact neg_nonpos.mpr hm
    have hcoco := hB.ineq ⟨xinf, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hcoco' : beta * ‖B xinf - B z‖ ^ 2 ≤
        inner ℝ (xinf - z) (B xinf - B z) := hcoco
    have hnorm : ‖B xinf - B z‖ = 0 := by
      have hs : ‖B xinf - B z‖ ^ 2 = 0 := by
        nlinarith [hcoco', hmono']
      nlinarith [hs, norm_nonneg (B xinf - B z)]
    have hB_equal : B xinf = B z := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hinner := (weakConvergence_iff_forall_tendsto_inner_right x xinf).1 hxweak (B z)
    have hinner_sub : Tendsto (fun t ↦ inner ℝ (B z) (x t - xinf)) atTop
        (nhds (inner ℝ (B z) (xinf - xinf))) := by
      have hconst : Tendsto (fun _ : ℝ ↦ inner ℝ xinf (B z)) atTop
          (nhds (inner ℝ xinf (B z))) := tendsto_const_nhds
      have hh := hinner.sub hconst
      simpa [inner_sub_right, real_inner_comm] using hh
    have hineq_z := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsolution z hz) (hdom.2 xinf hxinfS)
    have hineq_inf := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsolution xinf hxinfS) (hdom.2 z hz)
    have hvalue_zero : (Phi xinf : EReal).toReal - (Phi z : EReal).toReal +
        inner ℝ (B z) (xinf - z) = 0 := by
      have hz' : (Phi xinf : EReal).toReal ≥ (Phi z : EReal).toReal -
          inner ℝ (B z) (xinf - z) := by
        simpa [inner_neg_left, real_inner_comm] using hineq_z
      have hi' : (Phi z : EReal).toReal ≥ (Phi xinf : EReal).toReal +
          inner ℝ (B z) (xinf - z) := by
        rw [hB_equal] at hineq_inf
        rw [inner_neg_left] at hineq_inf
        rw [show z - xinf = -(xinf - z) by abel, inner_neg_right] at hineq_inf
        simp only [neg_neg] at hineq_inf
        exact hineq_inf
      linarith
    have hinner_z : Tendsto (fun t ↦ inner ℝ (B z) (x t - z)) atTop
        (nhds (inner ℝ (B z) (xinf - z))) := by
      have hconst : Tendsto (fun _ : ℝ ↦ inner ℝ z (B z)) atTop
          (nhds (inner ℝ z (B z))) := tendsto_const_nhds
      have hh := hinner.sub hconst
      simpa [inner_sub_right, real_inner_comm] using hh
    have hsum : Tendsto
        (fun t ↦ F t + (Phi z : EReal).toReal - inner ℝ (B z) (x t - z)) atTop
        (nhds (0 + (Phi z : EReal).toReal - inner ℝ (B z) (xinf - z))) := by
      simpa using (hFlim.add tendsto_const_nhds).sub hinner_z
    have hval : Tendsto (fun t ↦ (Phi (x t) : EReal).toReal) atTop
        (nhds (Phi xinf : EReal).toReal) := by
      have hsum' : Tendsto
          (fun t ↦ F t + (Phi z : EReal).toReal - inner ℝ (B z) (x t - z)) atTop
          (nhds (Phi xinf : EReal).toReal) := by
        have hsum0 : Tendsto
            (fun t ↦ F t + (Phi z : EReal).toReal - inner ℝ (B z) (x t - z)) atTop
            (nhds ((Phi z : EReal).toReal - inner ℝ (B z) (xinf - z))) := by
          simpa using hsum
        rw [show (Phi z : EReal).toReal - inner ℝ (B z) (xinf - z) =
            (Phi xinf : EReal).toReal from by linarith [hvalue_zero]] at hsum0
        exact hsum0
      apply Filter.Tendsto.congr' _ hsum'
      filter_upwards [] with t
      dsimp [F]
      ring
    exact ⟨xinf, hxinfS, hxweak, hval⟩
```

## Proof explanation
The proof first invokes `proposition_2_12` with most of the hypotheses. This gives a collection of consequences. The parts used later are:

- integrability of \(\|B(x(t))-B(z)\|^2\) on \([0,\infty)\);
- integrability of \(\|\operatorname{deriv}x(t)\|^2\) on \([0,\infty)\);
- a uniform bound \(\|v(t)\|\le C\) for all \(t\ge 0\).

The command `rcases` is used to unpack this conjunction. Then the proof defines
\[
F(t)=(\Phi(x(t)))_{\mathbb R}-(\Phi(z))_{\mathbb R}
+\langle B(z),x(t)-z\rangle.
\]

A first auxiliary result shows that \(F(t)\ge 0\) for all \(t\ge 0\). This uses the subgradient inequality for \(\Phi\) at \(x(t)\) with subgradient \(v(t)\), the fact that \(-B(z)\in\partial\Phi(z)\), and rewriting of inner products. The inequality obtained is then closed by `linarith`.

Next the proof establishes a chain rule for the real-valued function
\[
t\mapsto (\Phi(x(t)))_{\mathbb R}.
\]
Using the lemma `subgradient_chain_rule`, it proves that on every interval \([0,T]\) this function is absolutely continuous and, almost everywhere,
\[
\frac{d}{dt}(\Phi(x(t)))_{\mathbb R}
=
\langle v(t),\operatorname{deriv}x(t)\rangle.
\]
This uses the subgradient condition \(v(t)\in\partial\Phi(x(t))\), the domain hypothesis, the absolute continuity of \(x\), and the \(L^2\) hypotheses.

The proof then introduces an auxiliary potential
\[
\Gamma(t)
=
\frac12\|x(t)-z\|^2
+
\mu\left(
(\Phi(z))_{\mathbb R}
-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t),v(t)\rangle
\right).
\]
It shows that \(\Gamma\) is absolutely continuous on every interval \([0,T]\). This uses the absolute continuity of \(x\), \(v\), the chain rule just proved, and lemmas about absolute continuity of squared distance and inner products.

The main differential inequality proved is that for every \(T>0\), almost everywhere on \([0,T]\),
\[
\Gamma'(t)+\mu F(t)+\mu\beta\|B(x(t))-B(z)\|^2\le 0.
\]
The proof of this inequality combines several ingredients.

- The subdifferential of a gamma-zero function is monotone. Since \(v(t)\in\partial\Phi(x(t))\) and \(-B(z)\in\partial\Phi(z)\), one obtains
  \[
  \langle x(t)-z,v(t)+B(z)\rangle\ge 0.
  \]
- Cocoercivity of \(B\) gives
  \[
  \beta\|B(x(t))-B(z)\|^2
  \le
  \langle x(t)-z,B(x(t))-B(z)\rangle.
  \]
- The orbit equation, multiplied in the inner product by \(x(t)-z\), and using \(\mu\lambda=1\), gives a scalar identity equivalent to
  \[
  \Gamma'(t)
  +\mu\langle x(t)-z,v(t)+B(x(t))\rangle
  =0.
  \]
  In the Lean proof this is obtained via `prop216_orbit_inner_identity`.
- A subgradient inequality gives
  \[
  F(t)\le
  \langle x(t)-z,v(t)\rangle
  +\langle B(z),x(t)-z\rangle.
  \]

After rewriting the inner products and scaling by \(\mu\), the proof combines these inequalities using `linarith` to get the desired differential inequality.

Next, let
\[
q(t)=\mu F(t)+\mu\beta\|B(x(t))-B(z)\|^2.
\]
The proof shows \(q\) is locally integrable on every interval \([0,T]\). It does this by proving \(F\) and the norm-squared term are continuous on \([0,T]\), using absolute continuity of \(x\), continuity of \(B\), and the chain rule.

Then a lemma `prop216_dissipation_on_Ici` is applied with potential \(\Gamma\), dissipation \(q\), and lower bound \(0\). The proof verifies the required nonnegativity of \(q\), the lower bound \(\Gamma(t)\ge 0\), and the derivative inequality \(\Gamma'(t)+q(t)\le 0\). The conclusion is that \(q\) is integrable on \([0,\infty)\). Here the command `nlinarith` is used to close nonlinear inequalities involving squares.

Since \(q\) is integrable and \(\|B(x(t))-B(z)\|^2\) is already integrable, subtraction shows that \(\mu F\) is integrable on \([0,\infty)\). Multiplying by \(\mu^{-1}\), using \(\mu\ne 0\), proves that \(F\) itself is integrable.

The next goal is \(\lim_{t\to\infty}F(t)=0\). The proof obtains a constant \(C\) such that \(\|v(t)\|\le C\) for all \(t\ge 0\), and defines
\[
G(t)=(C+\|B(z)\|)\|\operatorname{deriv}x(t)\|.
\]
It proves \(G\) is \(L^2\)-integrable on \([0,\infty)\) because \(\operatorname{deriv}x\) is \(L^2\). It also proves that, almost everywhere, \(F'(t)\le G(t)\). Indeed,
\[
F'(t)=
\langle v(t),\operatorname{deriv}x(t)\rangle
+\langle B(z),\operatorname{deriv}x(t)\rangle,
\]
so Cauchy-Schwarz and the bound on \(\|v(t)\|\) give
\[
F'(t)\le
(\|v(t)\|+\|B(z)\|)\|\operatorname{deriv}x(t)\|
\le G(t).
\]
The proof first obtains this bound almost everywhere on each interval \([0,n+1]\), then extends it to almost everywhere on \([0,\infty)\). It also proves \(F\) is absolutely continuous on intervals. Finally it applies `prop216_limit_zero_of_memLp_deriv_bound_Ici` to get \(F(t)\to 0\).

The last part proves the convergence of \(\Phi(x(t))\) along a weakly convergent subsequence. The initial weak convergence hypothesis gives some \(x_\infty\in S\) with \(x(t)\rightharpoonup x_\infty\). Monotonicity of the subdifferential and cocoercivity of \(B\) are used to prove
\[
B(x_\infty)=B(z).
\]
Specifically, monotonicity gives
\[
\langle x_\infty-z,B(x_\infty)-B(z)\rangle\le 0,
\]
while cocoercivity gives
\[
\beta\|B(x_\infty)-B(z)\|^2
\le
\langle x_\infty-z,B(x_\infty)-B(z)\rangle.
\]
Since \(\beta>0\), the norm must be zero.

Using subgradient inequalities at \(z\) and at \(x_\infty\), together with \(B(x_\infty)=B(z)\), the proof shows
\[
(\Phi(x_\infty))_{\mathbb R}
-(\Phi(z))_{\mathbb R}
+\langle B(z),x_\infty-z\rangle
=0.
\]
Weak convergence implies
\[
\langle B(z),x(t)-z\rangle
\to
\langle B(z),x_\infty-z\rangle.
\]
Since \(F(t)\to 0\), and
\[
(\Phi(x(t)))_{\mathbb R}
=
F(t)
+(\Phi(z))_{\mathbb R}
-\langle B(z),x(t)-z\rangle,
\]
the limit of \((\Phi(x(t)))_{\mathbb R}\) is
\[
(\Phi(z))_{\mathbb R}
-\langle B(z),x_\infty-z\rangle
=
(\Phi(x_\infty))_{\mathbb R}.
\]
This yields the final existence statement.

Important Lean commands used include `intro` and `intros` to introduce variables and hypotheses, `let` and `have` to create local definitions and intermediate facts, `rw` and `simp` to rewrite using equalities, `exact` to close goals by providing a term, `rcases` to destruct existential or conjunctive facts, `convert` to close goals by identifying expressions up to definitional rewriting, `ring` and `abel` to prove algebraic rearrangements, `linarith` and `nlinarith` to finish linear and nonlinear arithmetic inequalities, and `filter_upwards` to prove almost-everywhere statements by combining almost-everywhere hypotheses.

