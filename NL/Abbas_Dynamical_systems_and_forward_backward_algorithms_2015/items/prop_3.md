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
The theorem concerns a complete real inner product space $H$, a set $S\subseteq H$, a point $z\in S$, a function

$$
\Phi:H\to (-\infty,\infty]
$$

modeled as $H\to \{r\in \overline{\mathbb R}: r>-\infty\}$, a map $B:H\to H$, curves $x,v:\mathbb R\to H$, and positive parameters $\lambda,\mu,\beta$ with $\mu\lambda=1$. The hypothesis $\Phi\in\mathrm{gammaZero}(H)$ says that $\Phi$ belongs to the class $\Gamma_0(H)$, and the hypothesis on $B$ says that $B$ is $\beta$-cocoercive on all of $H$, i.e. for all $u,w\in H$,

$$
\beta\|Bu-Bw\|^2\le \langle u-w,Bu-Bw\rangle .
$$

The theorem assumes that $x$ and $v$ are absolutely continuous on every interval $[0,T]$ with $T>0$, that they are differentiable almost everywhere there with derivatives $\dot x$ and $\dot v$, and that

$$
v(t)\in \partial\Phi(x(t))
$$

for every $t\ge 0$. It also assumes local $L^2$ bounds for $v$ and $\dot x$ on $[0,T]$, and that almost everywhere on $[0,\infty)$,

$$
\lambda\dot x(t)+\dot v(t)+v(t)+B(x(t))=0.
$$

The set $S$ is a solution set: for every $w\in S$,

$$
-Bw\in \partial\Phi(w),
$$

equivalently $0\in Bw+\partial\Phi(w)$. The effective-domain hypotheses say that $x(t)\in\mathrm{dom}\Phi$ for all $t\ge 0$, and that every $w\in S$ lies in $\mathrm{dom}\Phi$. Finally, the weak-convergence hypothesis says that there exists $x_\infty\in S$ such that

$$
x(t)\rightharpoonup x_\infty
$$

in the weak topology as $t\to\infty$.

The conclusion is threefold. First, the function

$$
F(t)=(\Phi(x(t)))_{\mathbb R}-(\Phi z)_{\mathbb R}
+\langle Bz,x(t)-z\rangle
$$

is integrable on $[0,\infty)$. Second,

$$
F(t)\to 0
\qquad (t\to\infty).
$$

Third, there exists $x_\infty\in S$ such that $x(t)\rightharpoonup x_\infty$ and, in addition,

$$
(\Phi(x(t)))_{\mathbb R}\to(\Phi(x_\infty))_{\mathbb R}.
$$

The weak-convergence part of the third conclusion is already present in the hypothesis; the new information is the convergence of the real values of $\Phi$ along the curve.

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
The proof first invokes `proposition_2_12` with exactly the same data. That theorem supplies several facts. Let

$$
\Gamma(t)=\frac12\|x(t)-z\|^2+\mu\Bigl(
(\Phi z)_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t),v(t)\rangle\Bigr).
$$

The cited proposition says that $\Gamma$ is nonincreasing on $[0,\infty)$, that $\Gamma(t)$ has a finite limit as $t\to\infty$, that $\|B(x(t))-Bz\|^2$ is integrable on $[0,\infty)$, that $\|x(t)\|$ is bounded, that $\|\dot x(t)\|^2$, $\|\dot v(t)+v(t)+Bz\|^2$, and $\|\dot v(t)\|^2$ are integrable on $[0,\infty)$, that $\|v(t)\|$ is bounded, and that

$$
(\Phi(x(t)))_{\mathbb R}+\langle x(t),Bz\rangle
$$

has a finite limit as $t\to\infty$. The last fact is recorded in the proof but is not used later.

The proof then defines

$$
F(t)=(\Phi(x(t)))_{\mathbb R}-(\Phi z)_{\mathbb R}
+\langle Bz,x(t)-z\rangle.
$$

It first shows $F(t)\ge 0$ for every $t\ge 0$. For this it uses the subgradient inequality `subgradient_ineq_toReal_of_mem_gammaZero`. Since $-Bz\in\partial\Phi(z)$, since $x(t)\in\mathrm{dom}\Phi$, and since $\Phi\in\Gamma_0(H)$, that inequality gives

$$
(\Phi(x(t)))_{\mathbb R}
\ge (\Phi z)_{\mathbb R}+\langle -Bz,x(t)-z\rangle.
$$

Using symmetry of the real inner product and $\langle -Bz,x(t)-z\rangle=-\langle Bz,x(t)-z\rangle$, this rearranges to $F(t)\ge 0$.

Next the proof establishes that the scalar function

$$
t\mapsto (\Phi(x(t)))_{\mathbb R}
$$

is absolutely continuous on each $[0,T]$, and that, almost everywhere on $[0,T]$,

$$
\frac{d}{dt}(\Phi(x(t)))_{\mathbb R}
=\langle v(t),\dot x(t)\rangle.
$$

This is exactly the conclusion of `subgradient_chain_rule`, applied with $b=T$. Its hypotheses are supplied as follows: $\Phi\in\Gamma_0(H)$, $x$ is absolutely continuous on $[0,T]$, $v(t)\in\partial\Phi(x(t))$ for almost every $t\in[0,T]$, $x(t)\in\mathrm{dom}\Phi$ on $[0,T]$, $x$ is differentiable almost everywhere, and $v,\dot x\in L^2([0,T])$.

The proof then defines the same auxiliary function $\Gamma$ from `proposition_2_12` and proves that it is absolutely continuous on every $[0,T]$. It uses three closure facts. First, `prop216_inner_ac` says that the real inner product of two absolutely continuous curves is absolutely continuous. Applying it to $z-x(t)$ and $v(t)$, and using

$$
\langle z-x(t),v(t)\rangle=-\langle x(t)-z,v(t)\rangle,
$$

shows that $t\mapsto\langle z-x(t),v(t)\rangle$ is absolutely continuous. Second, `prop216_sqdist_ac` says that if $x$ is absolutely continuous, then so is

$$
t\mapsto \frac12\|x(t)-z\|^2.
$$

Third, absolutely continuous functions are closed under addition, subtraction, and multiplication by constants. Therefore $\Gamma$ is absolutely continuous on $[0,T]$.

The central estimate is that, for every $T>0$, almost everywhere on $[0,T]$,

$$
\Gamma'(t)+\mu F(t)+\mu\beta\|B(x(t))-Bz\|^2\le 0.
$$

To prove this, the proof first uses `isMonotone_subdifferential`. Since $\Phi\in\Gamma_0(H)$, the cited `isProper_of_mem_gammaZero` gives that the extended-real function $y\mapsto(\Phi y)_{\mathbb R}$ is proper, and then `isMonotone_subdifferential` gives that $\partial\Phi$ is monotone as a set-valued operator: whenever $u\in\partial\Phi(a)$ and $w\in\partial\Phi(b)$,

$$
0\le \langle u-w,a-b\rangle.
$$

From monotonicity of $\partial\Phi$ and differentiability of $x$ and $v$, the proof obtains almost everywhere on $[0,T]$

$$
0\le \langle \dot x(t),\dot v(t)\rangle.
$$

This is the content of `prop216_inner_deriv_nonneg`, applied to the monotone operator $\partial\Phi$, the membership $v(t)\in\partial\Phi(x(t))$, and the derivatives of $x$ and $v$ at $t$. The almost-everywhere statement is first proved on $(0,T]$ and then transferred to $[0,T]$, since the endpoint $0$ has measure zero.

For almost every $t\in[0,T]$, the proof collects the following facts: $x$ and $v$ are differentiable at $t$; the derivative of $(\Phi(x(t)))_{\mathbb R}$ is $\langle v(t),\dot x(t)\rangle$; the orbit equation

$$
\lambda\dot x(t)+\dot v(t)+v(t)+B(x(t))=0
$$

holds; and $0\le\langle \dot x(t),\dot v(t)\rangle$.

It then computes derivatives. The derivative of

$$
t\mapsto \frac12\|x(t)-z\|^2
$$

is

$$
\langle x(t)-z,\dot x(t)\rangle.
$$

The derivative of

$$
t\mapsto \langle z-x(t),v(t)\rangle
$$

is

$$
\langle z-x(t),\dot v(t)\rangle-\langle \dot x(t),v(t)\rangle.
$$

Therefore the derivative of $\Gamma$ is

$$
\Gamma'(t)
=\langle x(t)-z,\dot x(t)\rangle
+\mu\langle x(t)-z,\dot v(t)\rangle.
$$

The proof next uses three inequalities. First, monotonicity of $\partial\Phi$ applied to $v(t)\in\partial\Phi(x(t))$ and $-Bz\in\partial\Phi(z)$ gives

$$
0\le \langle v(t)+Bz,x(t)-z\rangle
=\langle x(t)-z,v(t)+Bz\rangle.
$$

Multiplying by $\mu>0$,

$$
0\le \mu\bigl(\langle x(t)-z,v(t)\rangle
+\langle x(t)-z,Bz\rangle\bigr).
$$

Second, cocoercivity of $B$ gives

$$
\beta\|B(x(t))-Bz\|^2
\le \langle x(t)-z,B(x(t))-Bz\rangle.
$$

Multiplying by $\mu>0$,

$$
\mu\beta\|B(x(t))-Bz\|^2
\le \mu\langle x(t)-z,B(x(t))-Bz\rangle.
$$

Third, the subgradient inequality with $v(t)\in\partial\Phi(x(t))$ and $z\in\mathrm{dom}\Phi$ gives

$$
(\Phi z)_{\mathbb R}
\ge (\Phi(x(t)))_{\mathbb R}
+\langle v(t),z-x(t)\rangle.
$$

Equivalently,

$$
(\Phi(x(t)))_{\mathbb R}-(\Phi z)_{\mathbb R}
\le \langle x(t)-z,v(t)\rangle,
$$

and hence

$$
F(t)\le \langle x(t)-z,v(t)\rangle+\langle x(t)-z,Bz\rangle.
$$

Multiplying by $\mu>0$ preserves the inequality.

Finally, the proof uses `prop216_orbit_inner_identity`. Since $\mu\lambda=1$ and

$$
\lambda\dot x(t)+\dot v(t)+v(t)+B(x(t))=0,
$$

with $a=x(t)-z$ and $q=v(t)+B(x(t))$, one obtains

$$
\langle x(t)-z,\dot x(t)\rangle
+\mu\langle x(t)-z,\dot v(t)+v(t)+B(x(t))\rangle=0.
$$

Splitting

$$
B(x(t))=Bz+(B(x(t))-Bz),
$$

this becomes

$$
\Gamma'(t)
+\mu\langle x(t)-z,v(t)+Bz\rangle
+\mu\langle x(t)-z,B(x(t))-Bz\rangle=0.
$$

Combining this identity with the three inequalities above, `linarith` proves

$$
\Gamma'(t)+\mu F(t)+\mu\beta\|B(x(t))-Bz\|^2\le 0.
$$

The proof next defines

$$
q(t)=\mu F(t)+\mu\beta\|B(x(t))-Bz\|^2.
$$

It shows $q$ is integrable on every finite interval $(0,T]$. Indeed, $x$ is continuous on $[0,T]$ because it is absolutely continuous there; the map $t\mapsto(\Phi(x(t)))_{\mathbb R}$ is continuous on $[0,T]$ by the absolute-continuity conclusion from the chain rule; $B$ is continuous because `lipschitzWith_of_cocoercive` turns the cocoercivity of $B$ into a Lipschitz estimate, hence in particular continuity. Therefore $F$ and $\|B(x(t))-Bz\|^2$ are continuous on $[0,T]$, so their combination $q$ is continuous and hence integrable on $[0,T]$, and therefore also on $(0,T]$.

The proof then applies `prop216_dissipation_on_Ici` with $F$ replaced by $\Gamma$, $q$ as above, and lower bound $L=0$. The lemma says that if $\Gamma$ is absolutely continuous on every $[0,T]$, $q$ is integrable on every $(0,T]$, $q\ge0$ on $[0,\infty)$, $\Gamma\ge0$ on $[0,\infty)$, and almost everywhere on $[0,T]$

$$
\Gamma'(t)+q(t)\le0,
$$

then $q$ is integrable on $[0,\infty)$. All hypotheses are available: $\Gamma\ge0$ follows from the same subgradient inequality as before together with $\frac12\|x(t)-z\|^2\ge0$ and $\mu>0$; $q\ge0$ follows from $F\ge0$, $\mu>0$, $\beta>0$, and nonnegativity of the square. Thus $q$ is integrable on $[0,\infty)$.

Since

$$
q(t)=\mu F(t)+\mu\beta\|B(x(t))-Bz\|^2
$$

and $\|B(x(t))-Bz\|^2$ is integrable by `proposition_2_12`, the proof subtracts to obtain integrability of $\mu F$, then multiplies by $1/\mu$ to obtain integrability of $F$ on $[0,\infty)$. This proves the first conclusion.

To prove $F(t)\to0$, the proof uses the boundedness of $v$ supplied by `proposition_2_12`: there is $C\ge0$ with

$$
\|v(t)\|\le C\qquad(t\ge0).
$$

It defines

$$
G(t)=(C+\|Bz\|)\|\dot x(t)\|.
$$

Since $\|\dot x\|^2$ is integrable on $[0,\infty)$, the function $G$ is in $L^2([0,\infty))$. The proof also verifies that $F$ is absolutely continuous on every $[0,T]$, using `prop216_inner_ac` for the term $\langle Bz,x(t)-z\rangle$ and the already established absolute continuity of $(\Phi(x(t)))_{\mathbb R}$.

For almost every $t\ge0$, it computes

$$
F'(t)=\langle v(t),\dot x(t)\rangle+\langle Bz,\dot x(t)\rangle.
$$

Using the Cauchy–Schwarz bound $|\langle u,w\rangle|\le\|u\|\|w\|$, this is bounded by

$$
(\|v(t)\|+\|Bz\|)\|\dot x(t)\|
\le (C+\|Bz\|)\|\dot x(t)\|=G(t).
$$

Thus $F'(t)\le G(t)$ almost everywhere on $[0,\infty)$.

Now the proof applies `prop216_limit_zero_of_memLp_deriv_bound_Ici`. That lemma states: if $F\ge0$ on $[0,\infty)$, $F$ is absolutely continuous on every $[0,b]$ with $b>0$, $F\in L^p([0,\infty))$, $G\in L^r([0,\infty))$, $1\le p,r$ and $p\neq\infty$, and $F'\le G$ almost everywhere on $[0,\infty)$, then $F(t)\to0$. Taking $p=1$ and $r=2$, and using that integrability of $F$ is equivalent to $F\in L^1$, gives

$$
F(t)\to0.
$$

This proves the second conclusion.

For the third conclusion, the proof uses the weak limit $x_\infty\in S$ supplied by the hypothesis. It first shows $Bx_\infty=Bz$. Monotonicity of $\partial\Phi$ applied to $-Bx_\infty\in\partial\Phi(x_\infty)$ and $-Bz\in\partial\Phi(z)$ gives

$$
0\le \langle -Bx_\infty+Bz,x_\infty-z\rangle,
$$

hence

$$
\langle x_\infty-z,Bx_\infty-Bz\rangle\le0.
$$

Cocoercivity gives

$$
\beta\|Bx_\infty-Bz\|^2
\le \langle x_\infty-z,Bx_\infty-Bz\rangle\le0.
$$

Since $\beta>0$, this forces $\|Bx_\infty-Bz\|=0$, so $Bx_\infty=Bz$.

Next, `weakConvergence_iff_forall_tendsto_inner_right` converts the assumed weak convergence $x(t)\rightharpoonup x_\infty$ into convergence of all inner products:

$$
\langle x(t),u\rangle\to\langle x_\infty,u\rangle
$$

for every $u\in H$. Taking $u=Bz$ and using symmetry of the real inner product gives

$$
\langle Bz,x(t)-z\rangle\to\langle Bz,x_\infty-z\rangle
$$

and also

$$
\langle Bz,x(t)-x_\infty\rangle\to0.
$$

The proof then applies the subgradient inequality twice. From $-Bz\in\partial\Phi(z)$ and $x_\infty\in\mathrm{dom}\Phi$,

$$
(\Phi(x_\infty))_{\mathbb R}
\ge (\Phi z)_{\mathbb R}-\langle Bz,x_\infty-z\rangle.
$$

From $-Bx_\infty\in\partial\Phi(x_\infty)$ and $z\in\mathrm{dom}\Phi$, together with the already proved $Bx_\infty=Bz$,

$$
(\Phi z)_{\mathbb R}
\ge (\Phi(x_\infty))_{\mathbb R}+\langle Bz,x_\infty-z\rangle.
$$

These two inequalities force

$$
(\Phi(x_\infty))_{\mathbb R}-(\Phi z)_{\mathbb R}
+\langle Bz,x_\infty-z\rangle=0.
$$

Since $F(t)\to0$ and $\langle Bz,x(t)-z\rangle\to\langle Bz,x_\infty-z\rangle$, the expression

$$
F(t)+(\Phi z)_{\mathbb R}-\langle Bz,x(t)-z\rangle
$$

converges to

$$
(\Phi z)_{\mathbb R}-\langle Bz,x_\infty-z\rangle
=(\Phi(x_\infty))_{\mathbb R}.
$$

But by the definition of $F$,

$$
F(t)+(\Phi z)_{\mathbb R}-\langle Bz,x(t)-z\rangle
=(\Phi(x(t)))_{\mathbb R}
$$

for every $t$. Therefore

$$
(\Phi(x(t)))_{\mathbb R}\to(\Phi(x_\infty))_{\mathbb R}.
$$

Combining this with the weak convergence $x(t)\rightharpoonup x_\infty$ and $x_\infty\in S$ gives the final existential conclusion.

Throughout the proof, `filter_upwards` is used to combine several almost-everywhere statements into one exceptional set of measure zero; `rw`, `simp`, and `simpa` replace definitions and algebraic identities by equivalent forms; `convert` identifies limits or derivatives up to a pointwise equality; `rcases` and `refine` decompose and assemble conjunctions and existential statements; and `linarith` or `nlinarith` close the final scalar inequalities after all analytic hypotheses have been converted into explicit inequalities.

