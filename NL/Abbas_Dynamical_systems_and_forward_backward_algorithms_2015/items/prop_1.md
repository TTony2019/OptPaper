## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/prop_1.lean`

## Lean statement
```lean
theorem proposition_2_12 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (z : H)
    (lam mu beta : ℝ) (_ : S.Nonempty) (hz : z ∈ S)
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
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi) :
    AntitoneOn (fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))) (Set.Ici 0) ∧
    (∃ l, Tendsto (fun t ↦ (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))) atTop (nhds l)) ∧
    Integrable (fun t ↦ ‖B (x t) - B z‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    (∃ C : ℝ, ∀ t, 0 ≤ t → ‖x t‖ ≤ C) ∧
    Integrable (fun t ↦ ‖deriv x t‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    Integrable (fun t ↦ ‖deriv v t + v t + B z‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    Integrable (fun t ↦ ‖deriv v t‖ ^ 2) (volume.restrict (Set.Ici 0)) ∧
    (∃ C : ℝ, ∀ t, 0 ≤ t → ‖v t‖ ≤ C) ∧
    ∃ l, Tendsto (fun t ↦ (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) atTop (nhds l)
```

## Statement explanation
Let \(H\) be a real Hilbert space (a complete normed additive commutative group with a real inner product). Let \(S\subseteq H\). Let \(\Phi\) be an extended-real-valued function on \(H\), represented as a map from \(H\) into the subtype of extended reals strictly greater than the bottom element, and assume \(\Phi\) belongs to the class `ERealFunction.gammaZero H`. Let \(B:H\to H\), let \(x,v:\mathbb R\to H\), and let \(z\in H\). Let \(\lambda,\mu,\beta\in\mathbb R\).

The assumptions are as follows.

- \(S\) is nonempty and \(z\in S\).
- \(\lambda,\mu,\beta\) are positive, and \(\mu\lambda=1\).
- \(B\) is \(\beta\)-cocoercive on the whole space \(H\): for all \(u,w\in H\), \(\beta\|B(u)-B(w)\|^2 \le \langle u-w, B(u)-B(w)\rangle\).
- The trajectories \(x\) and \(v\) are absolutely continuous on every interval \([0,b]\), \(b>0\).
- On every interval \([0,T]\), almost everywhere, \(x\) and \(v\) have derivatives \(\operatorname{deriv}x(t)\) and \(\operatorname{deriv}v(t)\), respectively.
- For every \(t\ge 0\), \(v(t)\) belongs to the subdifferential of \(\Phi\) at \(x(t)\).
- Locally on every interval \([0,b]\), \(v\) and \(\operatorname{deriv}x\) are \(L^2\).
- Almost everywhere on \([0,\infty)\), \(v(t)\) belongs to the subdifferential of \(\Phi\) at \(x(t)\), and
  \[
  \lambda \operatorname{deriv}x(t)+\operatorname{deriv}v(t)+v(t)+B(x(t))=0.
  \]
- For every \(w\in S\), \(-B(w)\) belongs to the subdifferential of \(\Phi\) at \(w\).
- For every \(t\ge 0\), \(x(t)\) lies in the effective domain of \(\Phi\), and every \(w\in S\) lies in the effective domain of \(\Phi\).

Define
\[
\Gamma(t)=\frac12\|x(t)-z\|^2
+\mu\bigl((\Phi(z))_{\mathbb R}
-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t), v(t)\rangle\bigr),
\]
where \((\Phi(\cdot))_{\mathbb R}\) denotes the real-valued `toReal` part of the extended-real value.

The theorem concludes all of the following:

1. \(\Gamma\) is antitone on \([0,\infty)\).
2. \(\Gamma(t)\) converges to a finite limit as \(t\to\infty\).
3. \(t\mapsto \|B(x(t))-B(z)\|^2\) is integrable on \([0,\infty)\).
4. \(x\) is bounded on \([0,\infty)\).
5. \(t\mapsto \|\operatorname{deriv}x(t)\|^2\) is integrable on \([0,\infty)\).
6. \(t\mapsto \|\operatorname{deriv}v(t)+v(t)+B(z)\|^2\) is integrable on \([0,\infty)\).
7. \(t\mapsto \|\operatorname{deriv}v(t)\|^2\) is integrable on \([0,\infty)\).
8. \(v\) is bounded on \([0,\infty)\).
9. The function
   \[
   t\mapsto (\Phi(x(t)))_{\mathbb R}+\langle x(t), B(z)\rangle
   \]
   converges to a finite limit as \(t\to\infty\).

## Lean proof
```lean
by
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := hsolution z hz
  have hzdom : z ∈ ERealFunction.effectiveDomain Phi := hdom.2 z hz
  have hgap_nonneg : ∀ t, 0 ≤ t →
      0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t) := by
    intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsubgradient t ht) hzdom
    rw [real_inner_comm] at hineq
    linarith
  have hphi_chain : ∀ T, 0 < T →
      AbsolutelyContinuousOnInterval (fun t ↦ (Phi (x t) : EReal).toReal) 0 T ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (Phi (x s) : EReal).toReal) t =
          inner ℝ (v t) (deriv x t) := by
    intro T hT
    apply subgradient_chain_rule Phi hPhi x v T hT (hx_ac T hT)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hsubgradient t ht.1
    · intro t ht
      exact hdom.1 t ht.1
    · exact hx_deriv T hT
    · exact hvL2 T hT
    · exact hdxL2 T hT
  have hlyap : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
          mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
            inner ℝ (z - x s) (v s))) t +
          mu * beta * ‖B (x t) - B z‖ ^ 2 ≤ 0 := by
    intro T hT
    have hderiv_inner : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        0 ≤ inner ℝ (deriv x t) (deriv v t) := by
      have hmonoSub : SetValuedOperator.IsMonotone
          (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
        ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
      have htemp : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
          0 ≤ inner ℝ (deriv x t) (deriv v t) := by
        filter_upwards [
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hx_deriv T hT),
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hv_deriv T hT), ae_restrict_mem measurableSet_Ioc] with t hxt hvt ht
        exact prop212_inner_deriv_nonneg_of_monotone hmonoSub hsubgradient ht.1 hxt hvt
      rw [MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc] at htemp
      exact htemp
    have horbT : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        v t ∈ ERealFunction.subdifferential Phi (x t) ∧
          lam • deriv x t + deriv v t + v t + B (x t) = 0 := by
      have h := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
      exact h
    filter_upwards [hx_deriv T hT, hv_deriv T hT, (hphi_chain T hT).2,
      hderiv_inner, horbT, ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae (hphi_chain T hT).1.ae_differentiableAt] with
      t hxt hvt hphit hinner horb ht hphid
    have hphi : HasDerivAt (fun s ↦ (Phi (x s) : EReal).toReal)
        (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t) t :=
      (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hxt.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hin : HasDerivAt (fun s ↦ inner ℝ (z - x s) (v s))
        (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
      convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1;
        simp [inner_sub_left, real_inner_comm]; ring
    have hterm : HasDerivAt (fun s ↦ mu * ((Phi z : EReal).toReal -
        (Phi (x s) : EReal).toReal - inner ℝ (z - x s) (v s)))
        (-mu * (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t +
          (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)))) t := by
      have hraw :=
        ((((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi).sub hin).const_mul mu)
      convert hraw using 1; simp [sub_eq_add_neg]; ring
    have hG : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
          inner ℝ (z - x s) (v s)))
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      convert hsq.add hterm using 1
      rw [hphit]
      simp [inner_sub_left, real_inner_comm]; ring
    have hmono := ERealFunction.isMonotone_subdifferential
      (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
      (v t) (horb.1) (-B z) hzsub
    have hmono' : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      rw [real_inner_comm]
      simpa [inner_sub_right, inner_add_right, inner_neg_right] using hmono
    have hcoco := hB.ineq ⟨x t, Set.mem_univ _⟩ ⟨z, Set.mem_univ _⟩
    have hcoco' : beta * ‖B (x t) - B z‖ ^ 2 ≤
        inner ℝ (x t - z) (B (x t) - B z) := hcoco
    rw [show deriv (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
          inner ℝ (z - x s) (v s))) t =
        inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t) by
      exact hG.deriv]
    have horb' := prop212_orbit_inner_identity lam mu hmu_lam (x t - z)
      (deriv x t) (deriv v t) (v t + B (x t)) (by simpa [add_assoc] using horb.2)
    rw [inner_sub_right] at hcoco'
    rw [inner_add_right] at hmono'
    have hsplit : inner ℝ (x t - z) (v t + B (x t)) =
        inner ℝ (x t - z) (v t + B z) +
          inner ℝ (x t - z) (B (x t) - B z) := by
      rw [show B (x t) = B z + (B (x t) - B z) by abel]
      simp only [inner_add_right]
      abel_nf
    have horb_scalar : inner ℝ (x t - z) (deriv x t) +
        mu * inner ℝ (x t - z) (deriv v t) +
        mu * inner ℝ (x t - z) (v t + B (x t)) = 0 := by
      rw [inner_add_right] at horb'
      simpa [mul_add, add_assoc] using horb'
    rw [hsplit] at horb_scalar
    have hmono_exp : 0 ≤ inner ℝ (x t - z) (v t + B z) := by
      simpa [inner_add_right] using hmono'
    have hmono_mu : 0 ≤ mu * inner ℝ (x t - z) (v t + B z) :=
      mul_nonneg hmu.le hmono_exp
    have hcoco_mu := mul_le_mul_of_nonneg_left hcoco' hmu.le
    have hcoco_mu' : mu * beta * ‖B (x t) - B z‖ ^ 2 ≤
        mu * (inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z)) := by
      simpa [mul_assoc] using hcoco_mu
    have hinnerB : inner ℝ (x t - z) (B (x t) - B z) =
        inner ℝ (x t - z) (B (x t)) - inner ℝ (x t - z) (B z) := by
      rw [inner_sub_right]
    have hcoco_mu'' : mu * beta * ‖B (x t) - B z‖ ^ 2 ≤
        mu * inner ℝ (x t - z) (B (x t) - B z) := by
      rw [hinnerB]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hcoco' hmu.le
    linarith [horb_scalar, hmono_mu, hcoco_mu'', hinnerB]
  let Gamma : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 +
      mu * ((Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (z - x t) (v t))
  have hBcont : Continuous B :=
    (lipschitzWith_of_cocoercive hB).continuous.comp
      (continuous_id.subtype_mk fun _ => Set.mem_univ _)
  have hGamma_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval (Gamma) 0 T := by
    intro T hT
    have hx0 : AbsolutelyContinuousOnInterval x 0 T := hx_ac T hT
    have hv0 : AbsolutelyContinuousOnInterval v 0 T := hv_ac T hT
    have hconstx : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hconstp : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => (Phi z : EReal).toReal) 0 T :=
      contDiffOn_const.absolutelyContinuousOnInterval
    have hi : AbsolutelyContinuousOnInterval
        (fun t => inner ℝ (z - x t) (v t)) 0 T := by
      have hi' := prop212_inner_absolutelyContinuousOnInterval (hx0.sub hconstx) hv0
      convert hi'.neg using 1
      funext t
      simp [inner_sub_left]
    have ht : AbsolutelyContinuousOnInterval
        (fun t => (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
          inner ℝ (z - x t) (v t)) 0 T :=
      (hconstp.sub (hphi_chain T hT).1).sub hi
    simpa [Gamma] using
      (prop212_sqdist_absolutelyContinuousOnInterval hx0 z).add (ht.const_mul mu)
  have hq_local : ∀ T, 0 < T →
      IntegrableOn (fun t => mu * beta * ‖B (x t) - B z‖ ^ 2) (Set.Ioc 0 T) := by
    intro T hT
    have hxc : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le hT.le] using (hx_ac T hT).continuousOn
    have hbc : ContinuousOn (fun t => B (x t)) (Set.Icc 0 T) :=
      hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)
    have hqc : ContinuousOn (fun t => mu * beta * ‖B (x t) - B z‖ ^ 2)
        (Set.Icc 0 T) :=
      continuousOn_const.mul ((hbc.sub continuousOn_const).norm.pow 2)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (hqc.intervalIntegrable_of_Icc hT.le)
  have hGamma_pkg := prop212_dissipation_on_Ici
    (F := Gamma) (q := fun t => mu * beta * ‖B (x t) - B z‖ ^ 2) (L := 0)
    hGamma_ac hq_local
    (fun t ht => mul_nonneg (mul_nonneg hmu.le hbeta.le) (sq_nonneg _))
    (fun t ht => by
      have hg := hgap_nonneg t ht
      dsimp [Gamma]
      nlinarith [sq_nonneg (‖x t - z‖)])
    (fun T hT => by simpa [Gamma] using hlyap T hT)
  have hGamma_anti : AntitoneOn Gamma (Set.Ici 0) := hGamma_pkg.1
  have hGamma_lim : ∃ l, Tendsto Gamma atTop (nhds l) := hGamma_pkg.2.1
  have hBsq : Integrable (fun t => ‖B (x t) - B z‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    have h := hGamma_pkg.2.2
    have h' := h.const_mul (mu * beta)⁻¹
    change Integrable (fun t => (mu * beta)⁻¹ *
      (mu * beta * ‖B (x t) - B z‖ ^ 2)) (volume.restrict (Set.Ici 0)) at h'
    convert h' using 1
    funext t
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hmu.ne' hbeta.ne'), one_mul]
  have hx_bound : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖x t‖ ≤ C := by
    refine ⟨‖z‖ + 2 * Gamma 0 + 1, ?_⟩
    intro t ht
    have hanti := hGamma_anti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hdist : ‖x t - z‖ ^ 2 ≤ 2 * Gamma 0 := by
      have hgap := hgap_nonneg t ht
      dsimp [Gamma] at hanti
      dsimp [Gamma]
      nlinarith [sq_nonneg (‖x t - z‖), sq_nonneg (‖x 0 - z‖)]
    have hdist' : ‖x t - z‖ ≤ 2 * Gamma 0 + 1 := by
      nlinarith [norm_nonneg (x t - z), sq_nonneg (‖x t - z‖)]
    calc
      ‖x t‖ ≤ ‖x t - z‖ + ‖z‖ := by
        calc
          ‖x t‖ = ‖(x t - z) + z‖ := by congr 1; abel
          _ ≤ ‖x t - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + 2 * Gamma 0 + 1 := by linarith
  let E : ℝ → ℝ := fun t => Gamma t +
      2 * beta * ((Phi (x t) : EReal).toReal + inner ℝ (x t) (B z))
  have hE_ac : ∀ T, 0 < T → AbsolutelyContinuousOnInterval E 0 T := by
    intro T hT
    have hi := prop212_inner_const_absolutelyContinuousOnInterval (hx_ac T hT) (B z)
    have hp := (hphi_chain T hT).1
    convert (hGamma_ac T hT).add ((hp.add hi).const_mul (2 * beta)) using 1;
      simp only [E, Gamma, real_inner_comm, add_comm]
    · funext t
      dsimp
      ring
  have hE_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        deriv E t + beta * lam * ‖deriv x t‖ ^ 2 +
          mu * beta * ‖deriv v t + v t + B z‖ ^ 2 ≤ 0 := by
    intro T hT
    have hderiv_inner : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        0 ≤ inner ℝ (deriv x t) (deriv v t) := by
      have hmonoSub : SetValuedOperator.IsMonotone
          (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
        ERealFunction.isMonotone_subdifferential
        (fun y : H ↦ (Phi y : EReal)) (ERealFunction.isProper_of_mem_gammaZero hPhi)
      have htemp : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
          0 ≤ inner ℝ (deriv x t) (deriv v t) := by
        filter_upwards [
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hx_deriv T hT),
          MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
            (hv_deriv T hT), ae_restrict_mem measurableSet_Ioc] with t hxt hvt ht
        exact prop212_inner_deriv_nonneg_of_monotone hmonoSub hsubgradient ht.1 hxt hvt
      rw [MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc] at htemp
      exact htemp
    have horbT : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        v t ∈ ERealFunction.subdifferential Phi (x t) ∧
          lam • deriv x t + deriv v t + v t + B (x t) = 0 :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
    filter_upwards [hx_deriv T hT, hv_deriv T hT, (hphi_chain T hT).2,
      hderiv_inner, horbT, ae_restrict_mem measurableSet_Icc,
      MeasureTheory.ae_restrict_of_ae (hphi_chain T hT).1.ae_differentiableAt,
      hlyap T hT] with
      t hxt hvt hphit hinner horb ht hphid hgamma
    have hphi' : HasDerivAt (fun s ↦ (Phi (x s) : EReal).toReal)
        (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t) t :=
      (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
    have hsq : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2)
        (inner ℝ (x t - z) (deriv x t)) t := by
      simpa [one_div, real_inner_comm] using
        ((hxt.sub_const z).norm_sq.const_mul (1 / 2 : ℝ))
    have hin : HasDerivAt (fun s ↦ inner ℝ (z - x s) (v s))
        (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
      convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1;
        simp [inner_sub_left, real_inner_comm]; ring
    have hG0 : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖x s - z‖ ^ 2 +
        mu * ((Phi z : EReal).toReal - (Phi (x s) : EReal).toReal -
          inner ℝ (z - x s) (v s)))
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      have hterm :=
        ((((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi').sub hin).const_mul mu)
      convert hsq.add hterm using 1
      simp only [sub_eq_add_neg, inner_add_right, inner_neg_right, real_inner_comm, hphit]
      ring
    have hG : HasDerivAt Gamma
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t)) t := by
      simpa [Gamma] using hG0
    have hI : HasDerivAt (fun s ↦ inner ℝ (x s) (B z))
        (inner ℝ (deriv x t) (B z)) t :=
      by simpa using hxt.inner ℝ (hasDerivAt_const (x := t) (B z))
    have hGd' : deriv Gamma t =
        inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t) := hG.deriv
    have hId' : deriv (fun s ↦ inner ℝ (x s) (B z)) t =
        inner ℝ (deriv x t) (B z) := hI.deriv
    have haug := prop212_augmented_dissipation_algebra lam mu beta
      (deriv Gamma t) (inner ℝ (deriv x t) (v t))
      (inner ℝ (deriv x t) (B z)) (deriv x t) (deriv v t) (v t) (B (x t)) (B z)
      hmu_lam hbeta.le hinner horb.2 rfl rfl hgamma
    have hEhas : HasDerivAt E
        (inner ℝ (x t - z) (deriv x t) + mu * inner ℝ (x t - z) (deriv v t) +
          2 * beta *
            (deriv (fun s ↦ (Phi (x s) : EReal).toReal) t +
              inner ℝ (deriv x t) (B z))) t := by
      have hh := hG.add ((hphi'.add hI).const_mul (2 * beta))
      convert hh using 1
    rw [hEhas.deriv]
    rw [hGd'] at haug
    have hphit' : inner ℝ (deriv x t) (v t) = deriv (fun s ↦ (Phi (x s) : EReal).toReal) t := by
      rw [real_inner_comm, hphit]
    rw [hphit'] at haug
    simpa [real_inner_comm, add_assoc, add_left_comm, add_comm] using haug
  let r : ℝ → H := fun t => deriv v t + v t + B z
  let q : ℝ → ℝ := fun t => beta * lam * ‖deriv x t‖ ^ 2 + mu * beta * ‖r t‖ ^ 2
  have hq_local : ∀ T, 0 < T → IntegrableOn q (Set.Ioc 0 T) := by
    intro T hT
    have hdx_sq : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm
        (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
    have hxc : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le hT.le] using (hx_ac T hT).continuousOn
    have hbdc : ContinuousOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).norm.pow 2
    have hbd_sq : IntegrableOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      hbdc.integrableOn_Icc
    have hbdv : AEStronglyMeasurable (fun t => B (x t) - B z)
        (volume.restrict (Set.Icc 0 T)) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).aestronglyMeasurable measurableSet_Icc
    let R : ℝ → H := fun t => -(lam • deriv x t + (B (x t) - B z))
    have hR_sq : IntegrableOn (fun t => ‖R t‖ ^ 2) (Set.Icc 0 T) := by
      apply Integrable.mono' ((hdx_sq.const_mul (2 * lam ^ 2)).add
        (hbd_sq.const_mul 2))
      · exact (((hdxL2 T hT).aestronglyMeasurable.const_smul lam).add hbdv).neg.norm.pow 2
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        dsimp [R]
        rw [norm_neg]
        have h := norm_add_le (lam • deriv x t) (B (x t) - B z)
        rw [abs_of_nonneg (sq_nonneg _)]
        have hs : ‖lam • deriv x t‖ = lam * ‖deriv x t‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        rw [hs] at h
        have hsquare := (sq_le_sq₀ (norm_nonneg (lam • deriv x t + (B (x t) - B z)))
          (by positivity)).mpr h
        have hbound : (lam * ‖deriv x t‖ + ‖B (x t) - B z‖) ^ 2 ≤
            2 * lam ^ 2 * ‖deriv x t‖ ^ 2 + 2 * ‖B (x t) - B z‖ ^ 2 := by
          nlinarith [sq_nonneg (lam * ‖deriv x t‖ - ‖B (x t) - B z‖)]
        exact hsquare.trans hbound
    have hreq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        ‖r t‖ ^ 2 = ‖R t‖ ^ 2 := by
      have ho := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
      filter_upwards [ho] with t ht
      have hzero : (lam • deriv x t + deriv v t + v t) + B (x t) = 0 := by
        simpa [add_assoc] using ht.2
      have hbx : B (x t) = -(lam • deriv x t + deriv v t + v t) :=
        eq_neg_of_add_eq_zero_right hzero
      dsimp [r, R]
      rw [hbx]
      congr 1
      abel_nf
    have hres_sq : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) := by
      apply hR_sq.congr
      filter_upwards [hreq] with t ht
      exact ht.symm
    have hqIcc : IntegrableOn q (Set.Icc 0 T) := by
      dsimp [q]
      exact (hdx_sq.const_mul (beta * lam)).add (hres_sq.const_mul (mu * beta))
    exact hqIcc.mono_set Set.Ioc_subset_Icc_self
  have hres_local : ∀ T, 0 < T →
      IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Ioc 0 T) := by
    intro T hT
    have hdx_sq : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm
        (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
    have hxc : ContinuousOn x (Set.Icc 0 T) := by
      simpa [Set.uIcc_of_le hT.le] using (hx_ac T hT).continuousOn
    have hbdc : ContinuousOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).norm.pow 2
    have hbd_sq : IntegrableOn (fun t => ‖B (x t) - B z‖ ^ 2) (Set.Icc 0 T) :=
      hbdc.integrableOn_Icc
    have hbdv : AEStronglyMeasurable (fun t => B (x t) - B z)
        (volume.restrict (Set.Icc 0 T)) :=
      ((hBcont.continuousOn.comp hxc (Set.mapsTo_univ x _)).sub
        continuousOn_const).aestronglyMeasurable measurableSet_Icc
    let R : ℝ → H := fun t => -(lam • deriv x t + (B (x t) - B z))
    have hR_sq : IntegrableOn (fun t => ‖R t‖ ^ 2) (Set.Icc 0 T) := by
      apply Integrable.mono' ((hdx_sq.const_mul (2 * lam ^ 2)).add
        (hbd_sq.const_mul 2))
      · exact (((hdxL2 T hT).aestronglyMeasurable.const_smul lam).add hbdv).neg.norm.pow 2
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        dsimp [R]
        rw [norm_neg]
        have h := norm_add_le (lam • deriv x t) (B (x t) - B z)
        rw [abs_of_nonneg (sq_nonneg _)]
        have hs : ‖lam • deriv x t‖ = lam * ‖deriv x t‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        rw [hs] at h
        have hsquare := (sq_le_sq₀ (norm_nonneg (lam • deriv x t + (B (x t) - B z)))
          (by positivity)).mpr h
        have hbound : (lam * ‖deriv x t‖ + ‖B (x t) - B z‖) ^ 2 ≤
            2 * lam ^ 2 * ‖deriv x t‖ ^ 2 + 2 * ‖B (x t) - B z‖ ^ 2 := by
          nlinarith [sq_nonneg (lam * ‖deriv x t‖ - ‖B (x t) - B z‖)]
        exact hsquare.trans hbound
    have hreq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
        ‖r t‖ ^ 2 = ‖R t‖ ^ 2 := by
      have ho := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (show Set.Icc 0 T ⊆ Set.Ici 0 from fun t ht => ht.1) horbit
      filter_upwards [ho] with t ht
      have hzero : (lam • deriv x t + deriv v t + v t) + B (x t) = 0 := by
        simpa [add_assoc] using ht.2
      have hbx : B (x t) = -(lam • deriv x t + deriv v t + v t) :=
        eq_neg_of_add_eq_zero_right hzero
      dsimp [r, R]
      rw [hbx]
      congr 1
      abel_nf
    have hres_sq : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) := by
      apply hR_sq.congr
      filter_upwards [hreq] with t ht
      exact ht.symm
    exact hres_sq.mono_set Set.Ioc_subset_Icc_self
  have hq_nonneg : ∀ t, 0 ≤ t → 0 ≤ q t := by
    intro t ht
    dsimp [q]
    positivity
  have hE_pkg := prop212_dissipation_on_Ici
    (F := E) (q := q)
    (L := 2 * beta * ((Phi z : EReal).toReal + inner ℝ z (B z)))
    hE_ac hq_local hq_nonneg
    (fun t ht => by
      dsimp [E, Gamma]
      have hg := hgap_nonneg t ht
      have hminor := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi hzsub
        (hdom.1 t ht)
      have hminor' : (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z) ≥
          (Phi z : EReal).toReal + inner ℝ z (B z) := by
        rw [real_inner_comm] at hminor
        simp only [inner_neg_right] at hminor
        simp only [real_inner_comm, inner_sub_right] at hminor ⊢
        linarith
      nlinarith [sq_nonneg (‖x t - z‖)])
    (by simpa [q, r, add_assoc] using hE_deriv)
  have hE_lim : ∃ l, Tendsto E atTop (nhds l) := hE_pkg.2.1
  have hq_int : Integrable q (volume.restrict (Set.Ici 0)) := hE_pkg.2.2
  have hq_integral_nonneg : 0 ≤ ∫ t in Set.Ici 0, q t := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hq_nonneg t ht
  have hq_global : ∀ T, 0 < T →
      (∫ t in Set.Ioc 0 T, q t) ≤ ∫ t in Set.Ici 0, q t := by
    intro T hT
    apply MeasureTheory.setIntegral_mono_set hq_int
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hq_nonneg t ht
    · exact Filter.Eventually.of_forall (fun t ht => ht.1.le)
  have hdx_int : Integrable (fun t => ‖deriv x t‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound
      (a := 0) (C := (∫ t in Set.Ici 0, q t) / (beta * lam))
    · intro T
      by_cases hT : 0 < T
      · have hdxIcc : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
          (memLp_two_iff_integrable_sq_norm
            (hdxL2 T hT).aestronglyMeasurable).mp (hdxL2 T hT)
        exact hdxIcc.mono_set Set.Ioc_subset_Icc_self
      · simp [Set.Ioc_eq_empty hT]
    · intro s hs
      exact sq_nonneg _
    · intro T hT
      by_cases hT0 : T = 0
      · simp only [hT0, intervalIntegral.integral_same]
        exact div_nonneg hq_integral_nonneg (le_of_lt (mul_pos hbeta hlam))
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hdxIcc : IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Icc 0 T) :=
        (memLp_two_iff_integrable_sq_norm
          (hdxL2 T hTpos).aestronglyMeasurable).mp (hdxL2 T hTpos)
      have hdxIoc := hdxIcc.mono_set Set.Ioc_subset_Icc_self
      have hqIoc := hq_local T hTpos
      have hcmp : ∫ t in Set.Ioc 0 T, (beta * lam) * ‖deriv x t‖ ^ 2 ≤
          ∫ t in Set.Ioc 0 T, q t := by
        apply MeasureTheory.integral_mono_ae (hdxIoc.const_mul (beta * lam)) hqIoc
        filter_upwards with t
        dsimp [q]
        have hn : 0 ≤ mu * beta * ‖r t‖ ^ 2 :=
          mul_nonneg (mul_nonneg hmu.le hbeta.le) (sq_nonneg _)
        linarith
      have hc : 0 < beta * lam := mul_pos hbeta hlam
      have hmul : (beta * lam) * (∫ t in Set.Ioc 0 T, ‖deriv x t‖ ^ 2) ≤
          ∫ t in Set.Ici 0, q t := by
        rw [← MeasureTheory.integral_const_mul]
        exact hcmp.trans (hq_global T hTpos)
      have hdiv : (∫ t in Set.Ioc 0 T, ‖deriv x t‖ ^ 2) ≤
          (∫ t in Set.Ici 0, q t) / (beta * lam) :=
        (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
      rw [intervalIntegral.integral_of_le hT]
      exact hdiv
  have hres_int : Integrable (fun t => ‖r t‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound
      (a := 0) (C := (∫ t in Set.Ici 0, q t) / (mu * beta))
    · intro T
      by_cases hT : 0 < T
      · exact hres_local T hT
      · simp [Set.Ioc_eq_empty hT]
    · intro s hs
      exact sq_nonneg _
    · intro T hT
      by_cases hT0 : T = 0
      · simp only [hT0, intervalIntegral.integral_same]
        exact div_nonneg hq_integral_nonneg (le_of_lt (mul_pos hmu hbeta))
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hresIoc := hres_local T hTpos
      have hqIoc := hq_local T hTpos
      have hcmp : ∫ t in Set.Ioc 0 T, (mu * beta) * ‖r t‖ ^ 2 ≤
          ∫ t in Set.Ioc 0 T, q t := by
        apply MeasureTheory.integral_mono_ae (hresIoc.const_mul (mu * beta)) hqIoc
        filter_upwards with t
        dsimp [q]
        have hn : 0 ≤ beta * lam * ‖deriv x t‖ ^ 2 :=
          mul_nonneg (mul_nonneg hbeta.le hlam.le) (sq_nonneg _)
        linarith
      have hc : 0 < mu * beta := mul_pos hmu hbeta
      have hmul : (mu * beta) * (∫ t in Set.Ioc 0 T, ‖r t‖ ^ 2) ≤
          ∫ t in Set.Ici 0, q t := by
        rw [← MeasureTheory.integral_const_mul]
        exact hcmp.trans (hq_global T hTpos)
      have hdiv : (∫ t in Set.Ioc 0 T, ‖r t‖ ^ 2) ≤
          (∫ t in Set.Ici 0, q t) / (mu * beta) :=
        (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
      rw [intervalIntegral.integral_of_le hT]
      exact hdiv
  have hdv_local : ∀ T, 0 < T →
      IntegrableOn (fun t => ‖deriv v t‖ ^ 2) (Set.Icc 0 T) := by
    intro T hT
    have hresIcc : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) :=
      hres_int.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
    have hv_sq : IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Icc 0 T) :=
      (memLp_two_iff_integrable_sq_norm
        (hvL2 T hT).aestronglyMeasurable).mp (hvL2 T hT)
    have hvplus_sq : IntegrableOn (fun t => ‖v t + B z‖ ^ 2) (Set.Icc 0 T) := by
      have hconst : IntegrableOn (fun _ : ℝ => ‖B z‖ ^ 2) (Set.Icc 0 T) :=
        continuousOn_const.integrableOn_Icc
      apply Integrable.mono' (hv_sq.const_mul 2 |>.add
        (hconst.const_mul 2))
      · exact ((hvL2 T hT).aestronglyMeasurable.add
          (continuousOn_const.aestronglyMeasurable measurableSet_Icc)).norm.pow 2
      · filter_upwards with t
        dsimp
        rw [abs_of_nonneg (sq_nonneg _)]
        have hn := norm_add_le (v t) (B z)
        have hsquare := (sq_le_sq₀ (norm_nonneg (v t + B z))
          (by positivity)).mpr hn
        nlinarith [hsquare, sq_nonneg (‖v t‖ - ‖B z‖)]
    apply Integrable.mono' (hresIcc.const_mul 2 |>.add (hvplus_sq.const_mul 2))
    · exact (aestronglyMeasurable_deriv v (volume.restrict (Set.Icc 0 T))).norm.pow 2
    · filter_upwards with t
      dsimp
      rw [abs_of_nonneg (sq_nonneg _)]
      have heq : deriv v t = r t - (v t + B z) := by
        dsimp [r]
        abel
      rw [heq]
      have hn := norm_sub_le (r t) (v t + B z)
      have hsquare := (sq_le_sq₀ (norm_nonneg (r t - (v t + B z)))
        (by positivity)).mpr hn
      nlinarith [hsquare, sq_nonneg (‖r t‖ - ‖v t + B z‖)]
  have hres_global : ∀ T, 0 < T →
      (∫ t in Set.Ioc 0 T, ‖r t‖ ^ 2) ≤ ∫ t in Set.Ici 0, ‖r t‖ ^ 2 := by
    intro T hT
    apply MeasureTheory.setIntegral_mono_set hres_int
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact sq_nonneg _
    · exact Filter.Eventually.of_forall (fun t ht => ht.1.le)
  have hdv_int : Integrable (fun t => ‖deriv v t‖ ^ 2)
      (volume.restrict (Set.Ici 0)) := by
    have hri : 0 ≤ ∫ t in Set.Ici 0, ‖r t‖ ^ 2 := by
      apply MeasureTheory.integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact sq_nonneg _
    apply prop212_integrableOn_Ici_of_nonneg_interval_bound
      (a := 0) (C := (∫ t in Set.Ici 0, ‖r t‖ ^ 2) + ‖v 0 + B z‖ ^ 2)
    · intro T
      by_cases hT : 0 < T
      · exact (hdv_local T hT).mono_set Set.Ioc_subset_Icc_self
      · simp [Set.Ioc_eq_empty hT]
    · intro s hs
      exact sq_nonneg _
    · intro T hT
      by_cases hT0 : T = 0
      · simp only [hT0, intervalIntegral.integral_same]
        exact add_nonneg hri (sq_nonneg _)
      have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      have hresIcc : IntegrableOn (fun t => ‖r t‖ ^ 2) (Set.Icc 0 T) :=
        hres_int.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
      have hdv_sq := hdv_local T hTpos
      have hr_eq : ∀ᵐ t ∂volume.restrict (Set.Icc 0 T),
          r t = deriv v t + v t + B z := by
        filter_upwards with t
        rfl
      have hend := prop212_residual_endpoint_inequality (v := v) (r := r) (b := B z)
        hTpos (hv_ac T hTpos) (hv_deriv T hTpos) hdv_sq hresIcc hr_eq
      simp_rw [intervalIntegral.integral_of_le hTpos.le] at hend
      have hcmp := hres_global T hTpos
      have hbound : (∫ t in Set.Ioc 0 T, ‖deriv v t‖ ^ 2) + ‖v T + B z‖ ^ 2 ≤
          (∫ t in Set.Ici 0, ‖r t‖ ^ 2) + ‖v 0 + B z‖ ^ 2 := by
        linarith
      rw [intervalIntegral.integral_of_le hT]
      linarith [hbound, sq_nonneg (‖v T + B z‖)]
  have hv_bound : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖v t‖ ≤ C := by
    let C : ℝ := (∫ t in Set.Ici 0, ‖r t‖ ^ 2) + ‖v 0 + B z‖ ^ 2
    refine ⟨‖v 0‖ + ‖B z‖ + C + 1, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      have hri : 0 ≤ ∫ s in Set.Ici 0, ‖r s‖ ^ 2 := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
        exact sq_nonneg _
      dsimp [C]
      nlinarith [hri, norm_nonneg (v 0), norm_nonneg (B z), sq_nonneg (‖v 0 + B z‖)]
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hresIcc : IntegrableOn (fun s => ‖r s‖ ^ 2) (Set.Icc 0 t) :=
        hres_int.mono_measure (Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl)
      have hdv_sq := hdv_local t htpos
      have hr_eq : ∀ᵐ s ∂volume.restrict (Set.Icc 0 t),
          r s = deriv v s + v s + B z := by
        filter_upwards with s
        rfl
      have hend := prop212_residual_endpoint_inequality (v := v) (r := r) (b := B z)
        htpos (hv_ac t htpos) (hv_deriv t htpos) hdv_sq hresIcc hr_eq
      simp_rw [intervalIntegral.integral_of_le htpos.le] at hend
      have hcmp := hres_global t htpos
      have hri : 0 ≤ ∫ s in Set.Ici 0, ‖r s‖ ^ 2 := by
        apply MeasureTheory.integral_nonneg_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
        exact sq_nonneg _
      have hstate : ‖v t + B z‖ ^ 2 ≤ C := by
        dsimp [C]
        have hdi : 0 ≤ ∫ s in Set.Ioc 0 t, ‖deriv v s‖ ^ 2 := by
          apply MeasureTheory.integral_nonneg_of_ae
          filter_upwards with s
          exact sq_nonneg _
        linarith [hend, hcmp, hdi]
      have hstate' : ‖v t + B z‖ ≤ C + 1 := by
        have hC : 0 ≤ C := by
          dsimp [C]
          exact add_nonneg hri (sq_nonneg _)
        nlinarith [hstate, hC, norm_nonneg (v t + B z),
          sq_nonneg (‖v t + B z‖ - (C + 1))]
      calc
        ‖v t‖ ≤ ‖v t + B z‖ + ‖B z‖ := by
          calc
            ‖v t‖ = ‖(v t + B z) - B z‖ := by congr 1; abel
            _ ≤ ‖v t + B z‖ + ‖B z‖ := norm_sub_le _ _
        _ ≤ ‖v 0‖ + ‖B z‖ + C + 1 := by
          linarith [hstate', norm_nonneg (B z), norm_nonneg (v 0)]
  have hscalar_lim : ∃ l, Tendsto
      (fun t => (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) atTop (nhds l) := by
    obtain ⟨lE, hEl⟩ := hE_lim
    obtain ⟨lG, hGl⟩ := hGamma_lim
    have hsub := hEl.sub hGl
    have hscaled := hsub.const_mul ((2 * beta)⁻¹)
    have hF : Tendsto
        (fun t => (Phi (x t) : EReal).toReal + inner ℝ (x t) (B z)) atTop
        (nhds ((2 * beta)⁻¹ * (lE - lG))) := by
      convert hscaled using 1
      funext t
      dsimp [E]
      field_simp [ne_of_gt hbeta]
      ring
    exact ⟨(2 * beta)⁻¹ * (lE - lG), hF⟩
  exact ⟨hGamma_anti, hGamma_lim, hBsq, hx_bound, hdx_int, hres_int,
    hdv_int, hv_bound, hscalar_lim⟩
```

## Proof explanation
The proof is a long sequence of `have` blocks constructing two Lyapunov-type functions,
\[
\Gamma(t)=\frac12\|x(t)-z\|^2+\mu((\Phi(z))_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}-\langle z-x(t),v(t)\rangle)
\]
and
\[
E(t)=\Gamma(t)+2\beta\bigl((\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle\bigr),
\]
and then applying a dissipation lemma twice.

First, the proof records two immediate consequences:
\[
-B(z)\in \operatorname{subdifferential}\Phi(z)
\]
from `hsolution z hz`, and
\[
z\in \operatorname{effectiveDomain}\Phi
\]
from `hdom.2 z hz`.

Using the subgradient inequality lemma
`ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero`, the proof proves
\[
0\le (\Phi(z))_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}-\langle z-x(t),v(t)\rangle
\]
for every \(t\ge 0\). This is the nonnegativity of the term inside \(\Gamma\). The Lean command `rw [real_inner_comm]` rewrites the inner product, and `linarith` closes the resulting linear inequality.

Next, the proof proves a chain-rule statement `hphi_chain`: for every \(T>0\), the function
\[
t\mapsto (\Phi(x(t)))_{\mathbb R}
\]
is absolutely continuous on \([0,T]\), and almost everywhere on \([0,T]\),
\[
\operatorname{deriv}\bigl(t\mapsto (\Phi(x(t)))_{\mathbb R}\bigr)(t)
=\langle v(t),\operatorname{deriv}x(t)\rangle.
\]
This is obtained by applying the lemma `subgradient_chain_rule` to the available assumptions. The proofs of the side conditions use `filter_upwards` to work almost everywhere, `exact` to supply individual hypotheses, and `simpa` to simplify interval membership.

The first main differential inequality is `hlyap`: for every \(T>0\), almost everywhere on \([0,T]\),
\[
\operatorname{deriv}\Gamma(t)+\mu\beta\|B(x(t))-B(z)\|^2\le 0.
\]
To prove this, the proof first establishes that almost everywhere
\[
0\le \langle \operatorname{deriv}x(t),\operatorname{deriv}v(t)\rangle.
\]
This uses monotonicity of the subdifferential of \(\Phi\), the helper lemma
`prop212_inner_deriv_nonneg_of_monotone`, and the almost-everywhere differentiability assumptions. The interval is transformed from \((0,T]\) to \([0,T]\) using
`MeasureTheory.Measure.restrict_congr_set Ioc_ae_eq_Icc`.

Then, at a generic point \(t\), the proof computes derivatives of each term in \(\Gamma\). It uses `HasDerivAt` facts named `hsq`, `hin`, `hterm`, and `hG`. These are obtained from the derivative assumptions for \(x\) and \(v\) and from the chain rule. Algebraic manipulations are done with `convert`, `simp`, `ring`, and `rw`.

The proof then combines three inequalities:

- monotonicity of the subdifferential gives
  \[
  0\le \langle x(t)-z, v(t)+B(z)\rangle;
  \]
- cocoercivity gives
  \[
  \beta\|B(x(t))-B(z)\|^2\le \langle x(t)-z, B(x(t))-B(z)\rangle;
  \]
- the orbit identity, via the helper `prop212_orbit_inner_identity`, gives
  \[
  \langle x(t)-z,\operatorname{deriv}x(t)\rangle
  +\mu\langle x(t)-z,\operatorname{deriv}v(t)\rangle
  +\mu\langle x(t)-z,v(t)+B(x(t))\rangle=0.
  \]

The term \(v(t)+B(x(t))\) is split as
\[
v(t)+B(z)+\bigl(B(x(t))-B(z)\bigr),
\]
and then `linarith` combines the derivative identity, monotonicity, and cocoercivity to obtain the desired inequality.

After defining \(\Gamma\), the proof shows that \(\Gamma\) is absolutely continuous on every \([0,T]\). This uses absolute continuity of \(x\), \(v\), and the constant functions, together with helpers for squared distance and inner products. It also proves local integrability of the dissipation
\[
q(t)=\mu\beta\|B(x(t))-B(z)\|^2
\]
on intervals \((0,T]\). This uses continuity of \(x\) and \(B\) and the fact that continuous functions on compact intervals are interval-integrable.

Then the proof applies the dissipation lemma
`prop212_dissipation_on_Ici` to \(\Gamma\) with dissipation \(q\) and constant lower bound \(0\). The lemma verifies that \(\Gamma\) is nonnegative, using the already proved gap nonnegativity and the square norm term, and that the differential inequality \(d\Gamma/dt+q\le 0\) holds almost everywhere. From this it obtains:

- \(\Gamma\) is antitone on \([0,\infty)\);
- \(\Gamma\) has a finite limit at infinity;
- the dissipation \(q\) is integrable on \([0,\infty)\).

Using `hGamma_pkg.1` and `hGamma_pkg.2.1`, the proof extracts `hGamma_anti` and `hGamma_lim`. Then it proves global integrability of
\[
\|B(x(t))-B(z)\|^2
\]
by multiplying the integrable function \(q\) by \((\mu\beta)^{-1}\). This uses `h.const_mul`, `convert`, and the rewrite
`rw [← mul_assoc, inv_mul_cancel₀ ...]`.

To bound \(x\), the proof uses the antitone property of \(\Gamma\) and the nonnegativity of the gap term. Since
\[
\frac12\|x(t)-z\|^2\le \Gamma(t)\le \Gamma(0),
\]
one obtains a bound on \(\|x(t)-z\|\), and then the triangle inequality gives a uniform bound on \(\|x(t)\|\). The arithmetic is done with `nlinarith`.

Next, the proof introduces the augmented energy
\[
E(t)=\Gamma(t)+2\beta((\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle).
\]
It proves absolute continuity of \(E\) similarly to \(\Gamma\). It also proves a second differential inequality: almost everywhere on \([0,T]\),
\[
\operatorname{deriv}E(t)+\beta\lambda\|\operatorname{deriv}x(t)\|^2
+\mu\beta\|\operatorname{deriv}v(t)+v(t)+B(z)\|^2\le 0.
\]
This is obtained by reusing the derivative computations for \(\Gamma\), the derivative of the scalar term \(\langle x(t),B(z)\rangle\), the inner-product monotonicity
\[
\langle \operatorname{deriv}x(t),\operatorname{deriv}v(t)\rangle\ge 0,
\]
and the helper lemma
`prop212_augmented_dissipation_algebra`. The algebraic rearrangement is completed with `simpa`, `rw`, and `ring`.

The proof defines the residual
\[
r(t)=\operatorname{deriv}v(t)+v(t)+B(z)
\]
and the augmented dissipation
\[
q(t)=\beta\lambda\|\operatorname{deriv}x(t)\|^2+\mu\beta\|r(t)\|^2.
\]

It proves local integrability of \(q\) by comparing \(r\) with
\[
R(t)=-(\lambda\operatorname{deriv}x(t)+(B(x(t))-B(z))).
\]
From the orbit equation, almost everywhere,
\[
B(x(t))=-(\lambda\operatorname{deriv}x(t)+\operatorname{deriv}v(t)+v(t)),
\]
so algebraically \(R(t)=r(t)\). Thus \(\|R(t)\|^2=\|r(t)\|^2\) almost everywhere. The proof shows \(\|R(t)\|^2\) is locally integrable using local \(L^2\) integrability of \(\operatorname{deriv}x\), local integrability of \(\|B(x(t))-B(z)\|^2\), and norm inequalities such as
\[
\|\lambda\operatorname{deriv}x(t)+(B(x(t))-B(z))\|^2
\le 2\lambda^2\|\operatorname{deriv}x(t)\|^2+2\|B(x(t))-B(z)\|^2.
\]
The commands `norm_add_le`, `sq_le_sq₀`, and `nlinarith` are used to derive this bound.

Applying `prop212_dissipation_on_Ici` to \(E\) with dissipation \(q\) and a lower bound
\[
2\beta((\Phi(z))_{\mathbb R}+\langle z,B(z)\rangle)
\]
gives a finite limit for \(E\) and global integrability of \(q\). The lower bound of \(E\) uses the subgradient inequality for \(-B(z)\in \operatorname{subdifferential}\Phi(z)\) and the effective-domain condition for \(x(t)\).

From the global integrability of \(q\), the proof extracts global integrability of
\[
\|\operatorname{deriv}x(t)\|^2
\]
and
\[
\|r(t)\|^2=\|\operatorname{deriv}v(t)+v(t)+B(z)\|^2.
\]
This uses the lemma
`prop212_integrableOn_Ici_of_nonneg_interval_bound`. For \(\operatorname{deriv}x\), the interval bound is obtained by comparing
\[
(\beta\lambda)\|\operatorname{deriv}x(t)\|^2
\]
with \(q(t)\), then dividing by the positive number \(\beta\lambda\) using `le_div_iff₀`. For \(r\), the proof similarly compares \((\mu\beta)\|r(t)\|^2\) with \(q(t)\). The command `by_cases` handles \(T=0\) versus \(T>0\).

To prove global integrability of
\[
\|\operatorname{deriv}v(t)\|^2,
\]
the proof uses the identity
\[
\operatorname{deriv}v(t)=r(t)-(v(t)+B(z)).
\]
It first shows local integrability of \(\|\operatorname{deriv}v(t)\|^2\) using local integrability of \(\|r(t)\|^2\) and local \(L^2\) integrability of \(v\). Then it uses an endpoint inequality
\[
\int_0^T \|\operatorname{deriv}v(t)\|^2\,dt+\|v(T)+B(z)\|^2
\le
\int_0^T \|r(t)\|^2\,dt+\|v(0)+B(z)\|^2
\]
from the helper lemma `prop212_residual_endpoint_inequality`. Combining this with the global integrability of \(\|r(t)\|^2\) gives the desired global integrability.

The boundedness of \(v\) follows from the same endpoint inequality and the global integral of \(\|r(t)\|^2\). The proof treats \(t=0\) separately and for \(t>0\) obtains a uniform bound on \(\|v(t)+B(z)\|^2\), then uses the triangle inequality to bound \(\|v(t)\|\).

Finally, to prove convergence of
\[
(\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle,
\]
the proof observes that
\[
E(t)-\Gamma(t)
=2\beta\bigl((\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle\bigr).
\]
Since both \(E\) and \(\Gamma\) have finite limits at infinity, their difference converges. The proof obtains the limits with `obtain`, subtracts them with `Tendsto.sub`, scales by \((2\beta)^{-1}\), and uses `field_simp` and `ring` to identify the resulting limit as that of
\[
(\Phi(x(t)))_{\mathbb R}+\langle x(t),B(z)\rangle.
\]

The final line assembles all nine conclusions with `exact ⟨...⟩`.

