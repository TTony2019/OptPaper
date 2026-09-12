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
The theorem `proposition_2_12` is set in a complete real inner product space $H$, i.e. a real Hilbert space. It fixes a nonempty set $S\subseteq H$, a function $\Phi:H\to \operatorname{Set.Ioi}(\bot_{\mathrm{EReal}})$ in the library’s $\Gamma_0(H)$ class, a map $B:H\to H$, two curves $x,v:\mathbb R\to H$, a point $z\in S$, and positive real numbers $\lambda,\mu,\beta$ satisfying

$$
\mu\lambda=1.
$$

The function $\Phi$ is extended-real valued but never takes the value $-\infty$; the membership $\Phi\in\Gamma_0(H)$ is used in the proof through properness of $\Phi$, monotonicity of its subdifferential, and the subgradient inequality.

The hypotheses are these. The map $B$ is $\beta$-cocoercive on all of $H$, meaning that for all $u,v\in H$,

$$
\beta\|Bu-Bv\|^2\le \langle u-v,Bu-Bv\rangle .
$$

The curves $x$ and $v$ are locally absolutely continuous on every interval $[0,b]$ with $b>0$, have derivatives almost everywhere on every $[0,T]$ with $T>0$, and the functions $v$ and $x'$ are locally square-integrable on such intervals. For every $t\ge 0$,

$$
v(t)\in \partial\Phi(x(t)).
$$

Almost everywhere on $[0,\infty)$,

$$
v(t)\in \partial\Phi(x(t)),
\qquad
\lambda x'(t)+v'(t)+v(t)+B(x(t))=0 .
$$

For the point $z\in S$, the solution condition says

$$
-Bz\in \partial\Phi(z),
$$

and more generally every $w\in S$ satisfies $-Bw\in\partial\Phi(w)$. The domain hypothesis says that $x(t)$ lies in the effective domain of $\Phi$ for every $t\ge0$, and every $w\in S$, in particular $z$, lies in the effective domain of $\Phi$. Thus the real-valued expressions $\Phi(z)$ and $\Phi(x(t))$ used below are finite and can be obtained from the extended-real values by `.toReal`.

The theorem defines the Lyapunov-type function

$$
\Gamma(t)=\frac12\|x(t)-z\|^2+
\mu\left(\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle\right).
$$

The conclusions are:

$$
\Gamma \text{ is antitone on } [0,\infty),
$$

so $\Gamma(t)\le \Gamma(s)$ whenever $0\le s\le t$;

$$
\exists l,\quad \Gamma(t)\to l \text{ as } t\to\infty;
$$

$$
\int_0^\infty \|B(x(t))-Bz\|^2\,dt<\infty;
$$

there is a constant $C$ such that $\|x(t)\|\le C$ for all $t\ge0$;

$$
\int_0^\infty \|x'(t)\|^2\,dt<\infty;
$$

$$
\int_0^\infty \|v'(t)+v(t)+Bz\|^2\,dt<\infty;
$$

$$
\int_0^\infty \|v'(t)\|^2\,dt<\infty;
$$

there is a constant $C$ such that $\|v(t)\|\le C$ for all $t\ge0$; and finally

$$
\Phi(x(t))+\langle x(t),Bz\rangle
$$

converges as $t\to\infty$. In ordinary terms, the Lyapunov function measuring the distance to the solution $z$ plus the Bregman-type subgradient gap is nonincreasing and convergent, while all the natural energy quantities of the trajectory are globally integrable and both curves are bounded. The nonemptiness assumption on $S$ is part of the statement, but the displayed proof uses only the distinguished point $z\in S$ and the solution condition at points of $S$.

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
The proof begins by extracting two consequences of the solution condition at $z$. From `hsolution z hz` it obtains

$$
-Bz\in\partial\Phi(z),
$$

and from the second part of `hdom` it obtains

$$
z\in\operatorname{dom}\Phi.
$$

The latter is needed because the subgradient inequality is only converted to real values when the point at which $\Phi$ is evaluated lies in the effective domain.

The first substantive step proves the nonnegativity of the Bregman-type gap

$$
G(t)=\Phi(z)-\Phi(x(t))-\langle z-x(t),v(t)\rangle.
$$

For a fixed $t\ge0$, the hypothesis `hsubgradient t ht` gives $v(t)\in\partial\Phi(x(t))$. The lemma `subgradient_ineq_toReal_of_mem_gammaZero` says that if $u\in\partial f(x)$ and $y$ is in the effective domain of $f$, then

$$
f(y)\ge f(x)+\langle u,y-x\rangle
$$

after converting finite extended-real values to real numbers. Applying this with $f=\Phi$, $u=v(t)$, $x=x(t)$, and $y=z$ yields

$$
\Phi(z)\ge \Phi(x(t))+\langle v(t),z-x(t)\rangle.
$$

The proof rewrites the inner product by symmetry, using `real_inner_comm`, to the form $\langle z-x(t),v(t)\rangle$. Then `linarith` proves

$$
0\le G(t).
$$

Thus the second term of $\Gamma$, after multiplication by $\mu>0$, is nonnegative.

Next the proof establishes the chain rule for the extended-real term $\Phi(x(t))$. For every $T>0$, the lemma `subgradient_chain_rule` is applied to $\Phi$, $x$, and $v$. Its hypotheses are precisely that $x$ is absolutely continuous on $[0,T]$, that $v(t)\in\partial\Phi(x(t))$ almost everywhere there, that $x(t)$ lies in the effective domain of $\Phi$, that $x$ is differentiable almost everywhere with derivative `deriv x t`, and that $v$ and `deriv x` are $L^2$ on $[0,T]$. Its conclusion is two-fold: the function

$$
t\mapsto \Phi(x(t))
$$

is absolutely continuous on $[0,T]$, and almost everywhere on $[0,T]$,

$$
\frac{d}{dt}\Phi(x(t))=\langle v(t),x'(t)\rangle.
$$

This result is used both for the absolute continuity of $\Gamma$ and for the differentiation of the $\Phi$-terms in the Lyapunov and augmented energies.

The first Lyapunov inequality is then proved. The proof first records that, almost everywhere on $[0,T]$,

$$
0\le \langle x'(t),v'(t)\rangle.
$$

This comes from the monotonicity of the subdifferential. The lemma `isMonotone_subdifferential` says that if $F$ is proper, then $\partial F$ is monotone as a set-valued operator: if $u\in\partial F(x)$ and $v\in\partial F(y)$, then

$$
0\le \langle u-v,x-y\rangle.
$$

The properness of $\Phi$ is supplied by `isProper_of_mem_gammaZero hPhi`. Then `prop212_inner_deriv_nonneg_of_monotone` is applied with $T=\partial\Phi$, $x=x$, $v=v$, $dx=x'$, and $dv=v'$, using $v(t)\in\partial\Phi(x(t))$ for $t\ge0$. It yields exactly $0\le\langle x'(t),v'(t)\rangle$ at almost every positive $t$. The proof transfers the almost-everywhere statement from $(0,T]$ to $[0,T]$, which is harmless because the two sets differ by one point.

The proof then restricts the global orbit equation to $[0,T]$. The lemma `MeasureTheory.ae_restrict_of_ae_restrict_of_subset` is used to turn an almost-everywhere statement on $[0,\infty)$ into one on the smaller set $[0,T]$. Thus, almost everywhere on $[0,T]$, both

$$
v(t)\in\partial\Phi(x(t))
$$

and

$$
\lambda x'(t)+v'(t)+v(t)+B(x(t))=0.
$$

For almost every $t\in[0,T]$, the proof differentiates the Lyapunov expression. The derivative of $\frac12\|x(t)-z\|^2$ is

$$
\langle x(t)-z,x'(t)\rangle.
$$

The derivative of $\langle z-x(t),v(t)\rangle$ is

$$
\langle z-x(t),v'(t)\rangle-\langle x'(t),v(t)\rangle,
$$

by the product rule for the inner product. Using the chain rule for $\Phi(x(t))$, the derivative of the whole bracket in $\Gamma$ simplifies, and the derivative of $\Gamma$ becomes

$$
\Gamma'(t)=\langle x(t)-z,x'(t)\rangle
+\mu\langle x(t)-z,v'(t)\rangle.
$$

The algebra is handled by `simp`, `ring`, and rewriting with the chain-rule identity.

At this same almost-everywhere point, two inequalities are combined. First, monotonicity of $\partial\Phi$ applied to $v(t)\in\partial\Phi(x(t))$ and $-Bz\in\partial\Phi(z)$ gives

$$
0\le \langle v(t)-(-Bz),x(t)-z\rangle
=\langle v(t)+Bz,x(t)-z\rangle.
$$

After inner-product symmetry this becomes

$$
0\le \langle x(t)-z,v(t)+Bz\rangle.
$$

Second, cocoercivity of $B$ gives

$$
\beta\|B(x(t))-Bz\|^2
\le \langle x(t)-z,B(x(t))-Bz\rangle.
$$

Finally, the orbit identity `prop212_orbit_inner_identity` is applied to the vector $x(t)-z$, the derivatives $x'(t)$, $v'(t)$, and the remainder $v(t)+B(x(t))$. Since

$$
\lambda x'(t)+v'(t)+v(t)+B(x(t))=0
$$

and $\mu\lambda=1$, that lemma gives

$$
\langle x(t)-z,x'(t)\rangle
+\mu\langle x(t)-z,v'(t)+v(t)+B(x(t))\rangle=0.
$$

Splitting $v(t)+B(x(t))$ as $(v(t)+Bz)+(B(x(t))-Bz)$ and using the two inequalities above, `linarith` proves

$$
\Gamma'(t)+\mu\beta\|B(x(t))-Bz\|^2\le0
$$

almost everywhere on $[0,T]$. This is the first dissipation inequality.

The abstract lemma `prop212_dissipation_on_Ici` is now applied. It states that if $F$ is locally absolutely continuous on each $[0,T]$, $q$ is locally integrable on each $(0,T]$, $q\ge0$, $F$ is bounded below by some constant $L$, and almost everywhere on every $[0,T]$,

$$
F'(t)+q(t)\le0,
$$

then $F$ is antitone on $[0,\infty)$, $F$ has a limit at infinity, and $q$ is integrable on $[0,\infty)$. The proof applies this with

$$
F=\Gamma,\qquad q(t)=\mu\beta\|B(x(t))-Bz\|^2,\qquad L=0.
$$

The lower bound $L=0$ follows because $\frac12\|x(t)-z\|^2\ge0$ and $G(t)\ge0$. The derivative inequality is exactly the first dissipation inequality. Therefore $\Gamma$ is antitone, $\Gamma$ has a limit at infinity, and $q$ is globally integrable. Since $\mu\beta>0$, multiplying the integrability of $q$ by $(\mu\beta)^{-1}$ gives the conclusion

$$
\int_0^\infty\|B(x(t))-Bz\|^2\,dt<\infty.
$$

The antitonicity of $\Gamma$, together with $G(t)\ge0$, also bounds $x$. Indeed,

$$
\frac12\|x(t)-z\|^2\le \Gamma(t)\le\Gamma(0),
$$

so $\|x(t)-z\|^2\le 2\Gamma(0)$. Hence $\|x(t)-z\|$ is bounded, and then

$$
\|x(t)\|\le\|x(t)-z\|+\|z\|
$$

is bounded. The proof chooses the explicit bound $\|z\|+2\Gamma(0)+1$. This gives the boundedness conclusion for $x$.

The proof then introduces the augmented energy

$$
E(t)=\Gamma(t)+2\beta\left(\Phi(x(t))+\langle x(t),Bz\rangle\right).
$$

The absolute continuity of $E$ on compact intervals is obtained by assembling absolute continuity of its pieces. The function $\Gamma$ is already locally absolutely continuous. The function $t\mapsto \Phi(x(t))$ is absolutely continuous by `subgradient_chain_rule`. The function $t\mapsto \langle x(t),Bz\rangle$ is absolutely continuous by `prop212_inner_const_absolutelyContinuousOnInterval`, which says that pairing an absolutely continuous curve with a fixed vector preserves absolute continuity. The remaining quadratic terms use the same lemmas for inner products and squared distances. Thus $E$ is locally absolutely continuous.

The derivative inequality for $E$ is the second main dissipation step. For almost every $t\in[0,T]$, the proof again has the chain-rule identity for $\Phi(x(t))$, the derivative of $\langle x(t),Bz\rangle$,

$$
\frac{d}{dt}\langle x(t),Bz\rangle=\langle x'(t),Bz\rangle,
$$

and the derivative of $\Gamma$ as above. Hence

$$
E'(t)=\Gamma'(t)+2\beta\left(\langle v(t),x'(t)\rangle+\langle x'(t),Bz\rangle\right).
$$

At such a point, the algebraic lemma `prop212_augmented_dissipation_algebra` is applied. Its content is this: given scalars $\lambda,\mu,\beta$, vectors $dx,dv,vv,bx,bz$, and real numbers $d\Gamma,d\Phi,d\operatorname{Inner}$, if

$$
\mu\lambda=1,\qquad \beta\ge0,\qquad 0\le\langle dx,dv\rangle,
$$

if the orbit equation

$$
\lambda dx+dv+vv+bx=0
$$

holds, if

$$
d\Phi=\langle dx,vv\rangle,\qquad d\operatorname{Inner}=\langle dx,bz\rangle,
$$

and if

$$
d\Gamma+\mu\beta\|bx-bz\|^2\le0,
$$

then

$$
d\Gamma+2\beta(d\Phi+d\operatorname{Inner})+\beta\lambda\|dx\|^2
+\mu\beta\|dv+vv+bz\|^2\le0.
$$

The proof specializes it to

$$
d\Gamma=\Gamma'(t),\quad d\Phi=\langle x'(t),v(t)\rangle,\quad
d\operatorname{Inner}=\langle x'(t),Bz\rangle,
$$

$$
dx=x'(t),\quad dv=v'(t),\quad vv=v(t),\quad bx=B(x(t)),\quad bz=Bz.
$$

The hypothesis $0\le\langle dx,dv\rangle$ is the almost-everywhere inequality $0\le\langle x'(t),v'(t)\rangle$ proved earlier. The orbit equation is the a.e. differential inclusion. The inequality $d\Gamma+\mu\beta\|bx-bz\|^2\le0$ is exactly the first dissipation inequality for $\Gamma$. The lemma therefore yields

$$
\Gamma'(t)+2\beta\bigl(\langle x'(t),v(t)\rangle+\langle x'(t),Bz\rangle\bigr)
+\beta\lambda\|x'(t)\|^2+\mu\beta\|v'(t)+v(t)+Bz\|^2\le0.
$$

Using $\langle v(t),x'(t)\rangle=\langle x'(t),v(t)\rangle$, this is rewritten as

$$
E'(t)+\beta\lambda\|x'(t)\|^2
+\mu\beta\|v'(t)+v(t)+Bz\|^2\le0
$$

almost everywhere on $[0,T]$. This is the second dissipation inequality.

Next the proof defines

$$
r(t)=v'(t)+v(t)+Bz,\qquad
q(t)=\beta\lambda\|x'(t)\|^2+\mu\beta\|r(t)\|^2.
$$

It proves that $q$ is locally integrable on each $(0,T]$. The term $\|x'(t)\|^2$ is locally integrable because $x'\in L^2$ on each compact interval, using `memLp_two_iff_integrable_sq_norm`. The term $\|r(t)\|^2$ is locally integrable because the orbit equation rewrites $r(t)$ as

$$
r(t)=-\bigl(\lambda x'(t)+B(x(t))-Bz\bigr),
$$

and this is dominated on compact intervals by

$$
2\lambda^2\|x'(t)\|^2+2\|B(x(t))-Bz\|^2.
$$

The first term is integrable from the $L^2$ hypothesis on $x'$, and the second is continuous because $B$ is continuous. The continuity of $B$ comes from `lipschitzWith_of_cocoercive`: a $\beta$-cocoercive map is Lipschitz with constant $1/\beta$, hence continuous. Thus $q$ is locally integrable.

To apply `prop212_dissipation_on_Ici` to $E$ and $q$, the proof also needs a lower bound for $E$. The subgradient inequality is applied again, now to $-Bz\in\partial\Phi(z)$ and $x(t)\in\operatorname{dom}\Phi$. It gives

$$
\Phi(x(t))\ge \Phi(z)+\langle -Bz,x(t)-z\rangle.
$$

Rearranging and using inner-product symmetry yields

$$
\Phi(x(t))+\langle x(t),Bz\rangle
\ge \Phi(z)+\langle z,Bz\rangle.
$$

Together with $G(t)\ge0$ and $\frac12\|x(t)-z\|^2\ge0$, this shows

$$
E(t)\ge 2\beta\bigl(\Phi(z)+\langle z,Bz\rangle\bigr).
$$

Therefore `prop212_dissipation_on_Ici` applies with

$$
F=E,\qquad q(t)=\beta\lambda\|x'(t)\|^2+\mu\beta\|r(t)\|^2,
\qquad L=2\beta(\Phi(z)+\langle z,Bz\rangle).
$$

It follows that $E$ has a limit at infinity and that $q$ is globally integrable on $[0,\infty)$. Although the lemma also gives antitonicity of $E$, the proof only extracts the limit and the global integrability of $q$.

The global integrability of $q$ is then separated into integrability of its two summands. The lemma `prop212_integrableOn_Ici_of_nonneg_interval_bound` says that if $g$ is locally integrable, $g\ge0$, and there is a constant $C$ such that

$$
\int_0^T g(s)\,ds\le C
$$

for every $T\ge0$, then $g$ is integrable on $[0,\infty)$. The proof applies this first to

$$
g(t)=\|x'(t)\|^2.
$$

Since

$$
q(t)=\beta\lambda\|x'(t)\|^2+\mu\beta\|r(t)\|^2
$$

and $\mu\beta\|r(t)\|^2\ge0$, one has

$$
\beta\lambda\int_0^T\|x'(t)\|^2\,dt
\le \int_0^T q(t)\,dt
\le \int_0^\infty q(t)\,dt.
$$

Dividing by $\beta\lambda>0$ gives the uniform interval bound, hence

$$
\int_0^\infty\|x'(t)\|^2\,dt<\infty.
$$

The same argument with $\mu\beta$ in place of $\beta\lambda$ gives

$$
\int_0^\infty\|r(t)\|^2\,dt
=\int_0^\infty\|v'(t)+v(t)+Bz\|^2\,dt<\infty.
$$

The tactics `setIntegral_mono_set`, `integral_const_mul`, and `le_div_iff₀` are the tools used here to compare integrals and divide by the positive constants.

The proof next derives global integrability of $\|v'(t)\|^2$ and boundedness of $v$. Since

$$
r(t)=v'(t)+v(t)+Bz,
$$

one has

$$
v'(t)=r(t)-(v(t)+Bz).
$$

The function $r$ is locally square-integrable by the previous step, and $v(t)+Bz$ is locally square-integrable because $v$ is locally $L^2$ and $Bz$ is constant. Therefore $v'$ is locally square-integrable; the proof uses the domination

$$
\|v'(t)\|^2\le 2\|r(t)\|^2+2\|v(t)+Bz\|^2
$$

and `Integrable.mono'`.

To obtain global integrability, the proof invokes `prop212_residual_endpoint_inequality`. This lemma says that if $v$ is absolutely continuous on $[0,T]$, differentiable almost everywhere there, if $\|v'\|^2$ and $\|r\|^2$ are integrable on $[0,T]$, and if almost everywhere

$$
r(t)=v'(t)+v(t)+Bz,
$$

then

$$
\int_0^T\|v'(t)\|^2\,dt+\|v(T)+Bz\|^2
\le
\int_0^T\|r(t)\|^2\,dt+\|v(0)+Bz\|^2.
$$

Mathematically this is the energy inequality obtained by integrating the identity $r=(v+Bz)'+(v+Bz)$. It bounds both the derivative energy and the endpoint value. Since $\|r\|^2$ is globally integrable, the proof bounds

$$
\int_0^T\|r(t)\|^2\,dt
\le \int_0^\infty\|r(t)\|^2\,dt.
$$

Therefore

$$
\int_0^T\|v'(t)\|^2\,dt
\le \int_0^\infty\|r(t)\|^2\,dt+\|v(0)+Bz\|^2,
$$

so `prop212_integrableOn_Ici_of_nonneg_interval_bound` again applies and gives

$$
\int_0^\infty\|v'(t)\|^2\,dt<\infty.
$$

The same endpoint inequality also gives a uniform bound

$$
\|v(T)+Bz\|^2\le \int_0^\infty\|r(t)\|^2\,dt+\|v(0)+Bz\|^2.
$$

Thus $v(T)+Bz$ is bounded, and since

$$
\|v(T)\|\le\|v(T)+Bz\|+\|Bz\|,
$$

the curve $v$ is bounded.

Finally, the proof proves convergence of the scalar expression

$$
\Phi(x(t))+\langle x(t),Bz\rangle.
$$

By this point it has shown that both $E$ and $\Gamma$ converge as $t\to\infty$. Their difference therefore converges. But by definition,

$$
E(t)-\Gamma(t)
=
2\beta\bigl(\Phi(x(t))+\langle x(t),Bz\rangle\bigr).
$$

Since $2\beta>0$, multiplying the convergent difference by $(2\beta)^{-1}$ yields a limit for $\Phi(x(t))+\langle x(t),Bz\rangle$. The tactic `Tendsto.sub` handles the convergence of $E-\Gamma$, and `Tendsto.const_mul` handles the division by $2\beta$.

Throughout the proof, `intro` introduces the time variables and hypotheses such as $t\ge0$ or $T>0$. The tactic `filter_upwards` combines several almost-everywhere statements into a single almost-everywhere goal. Rewriting commands `rw`, `simp`, and `simpa` replace derivatives by their known formulas and use inner-product identities. The arithmetic tactics `linarith` and `nlinarith` close the scalar inequalities coming from monotonicity, cocoercivity, and the energy identities. The command `convert` is used when a goal is equal up to a change of function representation, for example when replacing $-\langle x-z,v\rangle$ by $\langle z-x,v\rangle$. The cases `by_cases` handle degenerate cases such as $T=0$. The algebraic tactics `ring`, `abel`, and `field_simp` normalize expressions, while `positivity` proves nonnegativity of squares and products of positive constants. Finally, the last `exact` assembles all proved components into the conjunction stated by the theorem.

