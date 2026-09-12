## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/prop_1.lean`

## Lean statement
```lean
theorem epsilon_din_uniform_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (x₀ v₀ : H) (xε : ℝ → ℝ → H) (x : ℝ → H)
    (hΦ : AssumptionH H Φ)
    (hcoercive : ∀ A : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ z : H, Φ z ≤ A → ‖z‖ < R)
    (hstrong : StronglyMonotoneOnBoundedSubsets H (gradient Φ))
    (hε : ∀ ε : ℝ, 0 < ε → IsEpsilonDINTrajectory ε Φ x₀ v₀ (xε ε))
    (hcn : IsContinuousNewtonTrajectory x₀ x Φ)
    (hεreg : ∀ ε : ℝ, 0 < ε → Differentiable ℝ (xε ε) ∧ Differentiable ℝ (deriv (xε ε)))
    (hx : Differentiable ℝ x) :
    (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      ‖xε ε t - x t‖ ≤ C * Real.sqrt ε) ∧
    TendstoUniformlyOn xε x (nhdsWithin 0 (Set.Ioi 0)) (Set.Ici 0)
```

## Statement explanation
The declaration is stated for a complete real inner product space \(H\), a function \(\Phi:H\to\mathbb R\), two initial vectors \(x_0,v_0\in H\), a two-parameter family of curves \(x_\epsilon(t)=xε\,\epsilon\,t\), and a curve \(x:\mathbb R\to H\). It assumes:

- `AssumptionH H Φ`: a package of hypotheses on \(\Phi\). The proof uses from it that \(\Phi\) is twice continuously differentiable and that \(\Phi\) is bounded below, so there exists \(m\in\mathbb R\) with \(m\le \Phi(z)\) for all \(z\in H\).
- `hcoercive`: for every real level \(A\), there is \(R>0\) such that every \(z\) with \(\Phi(z)\le A\) satisfies \(\|z\|<R\). Thus sublevel sets of \(\Phi\) are bounded.
- `hstrong`: the gradient \(\nabla\Phi\) is strongly monotone on bounded subsets of \(H\). In the proof this is used on a ball of radius \(R\): for some \(\beta>0\), any two points \(u,v\) with \(\max(\|u\|,\|v\|)<R\) satisfy
  \[
  \beta\|u-v\|^2\le \langle \nabla\Phi(u)-\nabla\Phi(v),u-v\rangle .
  \]
- `hε`: for every \(\epsilon>0\), the curve \(x_\epsilon=xε\,\epsilon\) is an \(\epsilon\)-DIN trajectory. The proof extracts from this that \(x_\epsilon(0)=x_0\), \(\dot x_\epsilon(0)=v_0\), and, writing \(v_\epsilon=\dot x_\epsilon\) and \(a_\epsilon=\ddot x_\epsilon\), that for every \(s>0\),
  \[
  \epsilon a_\epsilon(s)+\operatorname{Hess}\Phi(x_\epsilon(s))v_\epsilon(s)+\nabla\Phi(x_\epsilon(s))=0.
  \]
- `hcn`: \(x\) is a continuous Newton trajectory. The proof extracts \(x(0)=x_0\) and the Newton equation
  \[
  \operatorname{Hess}\Phi(x(s))\dot x(s)+\nabla\Phi(x(s))=0
  \qquad(s>0).
  \]
- `hεreg` and `hx`: differentiability assumptions ensuring that \(x_\epsilon\), its derivative, and \(x\) have the derivatives used in the proof.

The conclusion has two parts. First, there exists a constant \(C>0\) such that for every \(\epsilon\) with \(0<\epsilon\le1\) and every \(t\ge0\),
\[
\|x_\epsilon(t)-x(t)\|\le C\sqrt{\epsilon}.
\]
Second, the family \(x_\epsilon\) converges uniformly to \(x\) on \([0,\infty)\) as \(\epsilon\to0^+\), i.e. in the filter `nhdsWithin 0 (Set.Ioi 0)`. Thus the \(\epsilon\)-DIN trajectories approximate the continuous Newton trajectory with uniform error \(O(\sqrt{\epsilon})\).

## Lean proof
```lean
by
  let gradΦ : H → H := gradient Φ
  let hessΦ : H → H →L[ℝ] H := fderiv ℝ (gradient Φ)
  have hΦC1 : ContDiff ℝ 1 Φ :=
    hΦ.twice_continuously_differentiable.of_le (by norm_num)
  have hgradC1 : ContDiff ℝ 1 gradΦ := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by
          simpa using hΦ.twice_continuously_differentiable)).2.2
    simpa [gradΦ, gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgrad : ∀ z, HasGradientAt Φ (gradΦ z) z := by
    intro z
    simpa [gradΦ, gradient, Function.comp_def] using
      ((hΦC1.differentiable (by norm_num) z).hasGradientAt)
  have hess_deriv : ∀ z, HasFDerivAt gradΦ (hessΦ z) z := by
    intro z
    exact (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  let vε : ℝ → ℝ → H := fun ε s => deriv (xε ε) s
  let aε : ℝ → ℝ → H := fun ε s => deriv (deriv (xε ε)) s
  have hεdata : ∀ ε : ℝ, 0 < ε →
      0 < ε ∧ xε ε 0 = x₀ ∧ vε ε 0 = v₀ ∧
        (∀ s, HasDerivAt (xε ε) (vε ε s) s) ∧
        (∀ s, HasDerivAt (vε ε) (aε ε s) s) ∧
        ∀ s, 0 < s →
          ε • aε ε s + hessΦ (xε ε s) (vε ε s) + gradΦ (xε ε s) = 0 := by
    intro ε hεpos
    rcases hε ε hεpos with ⟨hεpos', hxε0, hvε0, _⟩
    rcases hεreg ε hεpos with ⟨hxε, hvε⟩
    refine ⟨hεpos', hxε0, ?_, ?_, ?_, ?_⟩
    · simpa [vε] using hvε0
    · intro s
      exact (hxε s).hasDerivAt
    · intro s
      simpa [vε, aε] using (hvε s).hasDerivAt
    · intro s hs
      rcases hε ε hεpos with ⟨_, _, _, heqε⟩
      simpa [vε, aε, hessΦ, gradΦ] using heqε s hs
  have hess_nonneg : ∀ z w : H, 0 ≤ inner ℝ ((fderiv ℝ (gradient Φ)) z w) w :=
    fun z w =>
    strong_mono_hessian_nonneg (gradient Φ) (fderiv ℝ (gradient Φ)) hstrong hess_deriv z w
  rcases hcn with ⟨hx0, hcn_eq_from_hcn⟩
  let v : ℝ → H := fun s => deriv x s
  have hxv : ∀ s, HasDerivAt x (v s) s := by
    intro s
    simpa [v] using (hx s).hasDerivAt
  have heq : ∀ s, 0 < s → hessΦ (x s) (deriv x s) + gradΦ (x s) = 0 := by
    intro s hs
    simpa [hessΦ, gradΦ] using hcn_eq_from_hcn s hs
  have henergy : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t →
      ε / 2 * ‖vε ε t‖ ^ 2 + Φ (xε ε t) ≤ ε / 2 * ‖v₀‖ ^ 2 + Φ x₀ := by
    intro ε hεpos t ht
    rcases hεdata ε hεpos with ⟨_, hxε0, hvε0, hxε, hvε, heqε⟩
    let U : ℝ → ℝ := fun s => ε / 2 * ‖vε ε s‖ ^ 2 + Φ (xε ε s)
    have hUanti : AntitoneOn U (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro s hs
        have hxεcont : Continuous (xε ε) :=
          continuous_iff_continuousAt.mpr (fun r => (hxε r).continuousAt)
        have hvεcont : Continuous (vε ε) :=
          continuous_iff_continuousAt.mpr (fun r => (hvε r).continuousAt)
        have hkincont : Continuous (fun r => ε / 2 * ‖vε ε r‖ ^ 2) := by
          exact continuous_const.mul ((continuous_norm.comp hvεcont).pow 2)
        have hpotcont : Continuous (fun r => Φ (xε ε r)) :=
          hΦC1.continuous.comp hxεcont
        simpa [U] using (hkincont.add hpotcont).continuousAt.continuousWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        simpa [U] using
          (epsilon_energy_deriv Φ gradΦ hessΦ ε (xε ε) (vε ε) (aε ε) hgrad hxε hvε
            heqε s hspos).differentiableAt.differentiableWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        have hder := epsilon_energy_deriv Φ gradΦ hessΦ ε (xε ε) (vε ε) (aε ε)
          hgrad hxε hvε heqε s hspos
        simpa [U, hder.deriv] using neg_nonpos.mpr (hess_nonneg _ _)
    have := hUanti (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 0)) (Set.mem_Ici.mpr ht) ht
    simpa [U, hxε0, hvε0] using this
  let α : ℝ := ‖v₀‖ ^ 2 / 2 + Φ x₀
  rcases hΦ.bounded_below with ⟨m, hm⟩
  have hpert : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      Φ (xε ε t) ≤ α ∧ ε * ‖vε ε t‖ ≤ Real.sqrt (2 * ε * (α - m)) := by
    intro ε hεpos hεone t ht
    have hE := henergy ε hεpos t ht
    have hα : ε / 2 * ‖v₀‖ ^ 2 + Φ x₀ ≤ α := by
      dsimp [α]
      nlinarith [sq_nonneg ‖v₀‖]
    have hEα : ε / 2 * ‖vε ε t‖ ^ 2 + Φ (xε ε t) ≤ α := hE.trans hα
    have hphi : Φ (xε ε t) ≤ α := by
      nlinarith [sq_nonneg ‖vε ε t‖, hεpos.le]
    have hgap : 0 ≤ α - m := by linarith [hm (xε ε t)]
    have hvelsq : (ε * ‖vε ε t‖) ^ 2 ≤ 2 * ε * (α - m) := by
      nlinarith [hm (xε ε t)]
    have hrad : 0 ≤ 2 * ε * (α - m) := mul_nonneg (mul_nonneg (by norm_num) hεpos.le) hgap
    have hsqrt : (Real.sqrt (2 * ε * (α - m))) ^ 2 = 2 * ε * (α - m) :=
      Real.sq_sqrt hrad
    refine ⟨hphi, ?_⟩
    nlinarith [mul_nonneg hεpos.le (norm_nonneg (vε ε t)), Real.sqrt_nonneg (2 * ε * (α - m))]
  have hcont : ∀ t : ℝ, 0 ≤ t → Φ (x t) ≤ Φ x₀ := by
    intro t ht
    let V : ℝ → ℝ := fun s => Φ (x s)
    have hVcont : Continuous V := hΦC1.continuous.comp hx.continuous
    have hVderiv : ∀ s : ℝ, 0 < s →
        HasDerivAt V (-inner ℝ (hessΦ (x s) (v s)) (v s)) s := by
      intro s hs
      have hd := (hgrad (x s)).hasFDerivAt.comp_hasDerivAt s (hxv s)
      have hd' : HasDerivAt V (inner ℝ (gradΦ (x s)) (v s)) s := by
        simpa [V, Function.comp_def, InnerProductSpace.toDual_apply_apply] using hd
      convert hd' using 1
      have hi := congrArg (fun q : H => inner ℝ q (v s)) (heq s hs)
      simp [inner_add_left] at hi
      linarith
    have hVanti : AntitoneOn V (Set.Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · intro s hs
        simpa [V] using hVcont.continuousAt.continuousWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        simpa [V] using (hVderiv s hspos).differentiableAt.differentiableWithinAt
      · intro s hs
        have hspos : 0 < s := by simpa using hs
        simpa [V, (hVderiv s hspos).deriv] using neg_nonpos.mpr (hess_nonneg _ _)
    have := hVanti (Set.mem_Ici.mpr (by norm_num : (0 : ℝ) ≤ 0)) (Set.mem_Ici.mpr ht) ht
    simpa [V, hx0] using this
  rcases hcoercive α with ⟨R, hRpos, hsub⟩
  have hball : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      max ‖xε ε t‖ ‖x t‖ < R := by
    intro ε hεpos hεone t ht
    apply max_lt
    · exact hsub _ (hpert ε hεpos hεone t ht).1
    · apply hsub
      have hα0 : Φ x₀ ≤ α := by
        dsimp [α]
        nlinarith [sq_nonneg ‖v₀‖]
      exact (hcont t ht).trans hα0
  rcases hstrong R hRpos with ⟨β, hβpos, hmono⟩
  have hdist : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      β * ‖xε ε t - x t‖ ≤ ‖gradΦ (xε ε t) - gradΦ (x t)‖ := by
    intro ε hεpos hεone t ht
    apply distance_le_grad_difference
    exact hmono _ _ (hball ε hεpos hεone t ht)
  have hgrad_diff : ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t →
      gradΦ (xε ε t) - gradΦ (x t) =
        Real.exp (-t) • (ε • v₀) - ε • vε ε t +
          ∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r) := by
    intro ε hεpos t ht
    rcases hεdata ε hεpos with ⟨_, hxε0, hvε0, hxε, hvε, heqε⟩
    have hq : ∀ r : ℝ, 0 < r →
        HasDerivAt (fun s => gradΦ (x s)) (-gradΦ (x r)) r := by
      intro r hr
      have hd := (hess_deriv (x r)).comp_hasDerivAt r (hxv r)
      have hH : hessΦ (x r) (v r) = -gradΦ (x r) :=
        eq_neg_of_add_eq_zero_left (heq r hr)
      simpa [Function.comp_def, hH] using hd
    have hqcont : Continuous (fun s => gradΦ (x s)) :=
      hgradC1.continuous.comp hx.continuous
    have hqsol := variation_of_constants (fun s => gradΦ (x s)) (fun _ : ℝ => (0 : H))
      continuous_const hqcont (fun r hr => by simpa using hq r hr) t ht
    have hfε : Continuous (fun s : ℝ => ε • vε ε s) :=
      continuous_const.smul (continuous_iff_continuousAt.mpr fun s => (hvε s).continuousAt)
    let ω : ℝ → H := fun s => ε • vε ε s + gradΦ (xε ε s)
    have hω : ∀ r : ℝ, 0 < r → HasDerivAt ω (-ω r + ε • vε ε r) r := by
      intro r hr
      have hv' := (hvε r).const_smul ε
      have hx' := (hess_deriv (xε ε r)).comp_hasDerivAt r (hxε r)
      have hd := hv'.add hx'
      have hsum : ε • aε ε r + hessΦ (xε ε r) (vε ε r) = -gradΦ (xε ε r) :=
        eq_neg_of_add_eq_zero_left (heqε r hr)
      convert hd using 1
      rw [hsum]
      dsimp [ω]
      abel
    have hωcont : Continuous ω := by
      have hxεcont : Continuous (xε ε) :=
        continuous_iff_continuousAt.mpr (fun r => (hxε r).continuousAt)
      have hgradcomp : Continuous (fun s => gradΦ (xε ε s)) :=
        hgradC1.continuous.comp hxεcont
      simpa [ω] using hfε.add hgradcomp
    have hωsol := variation_of_constants ω (fun s : ℝ => ε • vε ε s) hfε hωcont hω t ht
    have hqsol' : gradΦ (x t) = Real.exp (-t) • gradΦ x₀ := by
      simpa [hx0] using hqsol
    have hω0 : ω 0 = ε • v₀ + gradΦ x₀ := by simp [ω, hxε0, hvε0]
    rw [hω0] at hωsol
    calc
      gradΦ (xε ε t) - gradΦ (x t) = (ω t - ε • vε ε t) - gradΦ (x t) := by
        dsimp [ω]
        abel
      _ = Real.exp (-t) • (ε • v₀) - ε • vε ε t +
          ∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r) := by
        rw [hωsol, hqsol']
        rw [smul_add]
        abel
  have hgrad_bound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      ‖gradΦ (xε ε t) - gradΦ (x t)‖ ≤
        ε * ‖v₀‖ + 2 * Real.sqrt (2 * ε * (α - m)) := by
    intro ε hεpos hεone t ht
    let B : ℝ := Real.sqrt (2 * ε * (α - m))
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    have hinit : ‖Real.exp (-t) • (ε • v₀)‖ ≤ ε * ‖v₀‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Real.norm_eq_abs, abs_of_pos hεpos]
      have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      exact mul_le_of_le_one_left (mul_nonneg hεpos.le (norm_nonneg _)) he
    have hinst : ‖ε • vε ε t‖ ≤ B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
      exact (hpert ε hεpos hεone t ht).2
    have hkernel : ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ ≤ B := by
      have hecont : Continuous (fun r : ℝ => Real.exp (-(t - r))) :=
        Real.continuous_exp.comp ((continuous_const.sub continuous_id).neg)
      have hvcont : Continuous (fun r : ℝ => ε • vε ε r) := by
        rcases hεdata ε hεpos with ⟨_, _, _, _, hvε', _⟩
        exact continuous_const.smul
          (continuous_iff_continuousAt.mpr fun r => (hvε' r).continuousAt)
      have hfint : IntervalIntegrable (fun r : ℝ => ‖Real.exp (-(t - r)) • (ε • vε ε r)‖)
          MeasureTheory.volume 0 t := (hecont.smul hvcont).norm.intervalIntegrable 0 t
      have hgint : IntervalIntegrable (fun r : ℝ => Real.exp (-(t - r)) * B)
          MeasureTheory.volume 0 t := (hecont.mul continuous_const).intervalIntegrable 0 t
      have hmono := intervalIntegral.integral_mono_on ht hfint hgint (fun r hr => by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.norm_eq_abs, abs_of_pos hεpos]
        exact mul_le_mul_of_nonneg_left (hpert ε hεpos hεone r hr.1).2 (Real.exp_pos _).le)
      have hscalar : (∫ r in (0)..t, Real.exp (-(t - r)) * B) =
          B * (1 - Real.exp (-t)) := by
        calc
          (∫ r in (0)..t, Real.exp (-(t - r)) * B) =
              B * Real.exp (-t) * (∫ r in (0)..t, Real.exp r) := by
            rw [show (fun r : ℝ => Real.exp (-(t - r)) * B) =
              fun r => (B * Real.exp (-t)) * Real.exp r by
                funext r
                rw [show -(t - r) = -t + r by ring, Real.exp_add]
                ring]
            rw [intervalIntegral.integral_const_mul, mul_assoc]
          _ = B * (1 - Real.exp (-t)) := by
            rw [integral_exp, Real.exp_zero]
            have heq : Real.exp (-t) * Real.exp t = 1 := by
              rw [← Real.exp_add]
              simp
            calc
              B * Real.exp (-t) * (Real.exp t - 1) =
                  B * (Real.exp (-t) * Real.exp t - Real.exp (-t)) := by ring
              _ = B * (1 - Real.exp (-t)) := by rw [heq]
      calc
        ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ ≤
            ∫ r in (0)..t, ‖Real.exp (-(t - r)) • (ε • vε ε r)‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
        _ ≤ ∫ r in (0)..t, Real.exp (-(t - r)) * B := hmono
        _ = B * (1 - Real.exp (-t)) := hscalar
        _ ≤ B := by
          have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
          nlinarith [Real.exp_pos (-t)]
    rw [hgrad_diff ε hεpos t ht]
    calc
      ‖Real.exp (-t) • (ε • v₀) - ε • vε ε t +
          ∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ ≤
          ‖Real.exp (-t) • (ε • v₀)‖ + ‖ε • vε ε t‖ +
            ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ := by
              calc
                _ ≤ ‖Real.exp (-t) • (ε • v₀) - ε • vε ε t‖ +
                    ‖∫ r in (0)..t, Real.exp (-(t - r)) • (ε • vε ε r)‖ := norm_add_le _ _
                _ ≤ _ := by gcongr; exact norm_sub_le _ _
      _ ≤ ε * ‖v₀‖ + 2 * B := by linarith
      _ = ε * ‖v₀‖ + 2 * Real.sqrt (2 * ε * (α - m)) := rfl
  let K : ℝ := ‖v₀‖ + 2 * Real.sqrt (2 * (α - m))
  let C : ℝ := (K + 1) / β
  have hgap : 0 ≤ α - m := by
    dsimp [α]
    linarith [hm x₀, sq_nonneg ‖v₀‖]
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (by linarith) hβpos
  have herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℝ, 0 ≤ t →
      ‖xε ε t - x t‖ ≤ C * Real.sqrt ε := by
    intro ε hεpos hεone t ht
    have hsqrteps : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
    have hsqrteps_sq : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hεpos.le
    have hsqrteps_le_one : Real.sqrt ε ≤ 1 := by
      rw [← sq_le_sq₀ hsqrteps (by norm_num : (0 : ℝ) ≤ 1)]
      simpa [hsqrteps_sq] using hεone
    have heps_le_sqrt : ε ≤ Real.sqrt ε := by
      nlinarith
    have hsqrtfac : Real.sqrt (2 * ε * (α - m)) =
        Real.sqrt ε * Real.sqrt (2 * (α - m)) := by
      rw [show 2 * ε * (α - m) = ε * (2 * (α - m)) by ring,
        Real.sqrt_mul hεpos.le]
    have hgrad := hgrad_bound ε hεpos hεone t ht
    rw [hsqrtfac] at hgrad
    have hgradK : ε * ‖v₀‖ + 2 * (Real.sqrt ε * Real.sqrt (2 * (α - m))) ≤
        Real.sqrt ε * K := by
      dsimp [K]
      nlinarith [norm_nonneg v₀, Real.sqrt_nonneg (2 * (α - m))]
    have hβdist : β * ‖xε ε t - x t‖ ≤ Real.sqrt ε * K :=
      (hdist ε hεpos hεone t ht).trans (hgrad.trans hgradK)
    have hdiv : ‖xε ε t - x t‖ ≤ (Real.sqrt ε * K) / β :=
      (le_div_iff₀ hβpos).mpr (by simpa [mul_comm] using hβdist)
    calc
      ‖xε ε t - x t‖ ≤ (Real.sqrt ε * K) / β := hdiv
      _ ≤ ((K + 1) / β) * Real.sqrt ε := by
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff_of_pos_right hβpos).mpr
        have : Real.sqrt ε * K ≤ Real.sqrt ε * (K + 1) := by
          gcongr
          linarith
        nlinarith
      _ = C * Real.sqrt ε := rfl
  refine ⟨⟨C, hCpos, herror⟩, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  let η : ℝ := min 1 ((δ / C) ^ 2)
  have hδC : 0 < δ / C := div_pos hδ hCpos
  have hη : 0 < η := by
    dsimp [η]
    exact (lt_min_iff).mpr ⟨by norm_num, sq_pos_of_pos hδC⟩
  filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
  intro t ht
  have hεpos : 0 < ε := hε.1
  have hεη : ε < η := hε.2
  have hεη' : ε < min 1 ((δ / C) ^ 2) := by simpa [η] using hεη
  have hεone : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεη' (min_le_left _ _))
  have hεsq : ε < (δ / C) ^ 2 := lt_of_lt_of_le hεη' (min_le_right _ _)
  have hsqrt_lt : Real.sqrt ε < δ / C := (Real.sqrt_lt' hδC).mpr hεsq
  have hrate := herror ε hεpos hεone t ht
  rw [dist_eq_norm, norm_sub_rev]
  calc
    ‖xε ε t - x t‖ ≤ C * Real.sqrt ε := hrate
    _ < C * (δ / C) := mul_lt_mul_of_pos_left hsqrt_lt hCpos
    _ = δ := by field_simp [ne_of_gt hCpos]
```

## Proof explanation
The proof first fixes abbreviations
\[
\operatorname{grad}\Phi=\nabla\Phi,\qquad
\operatorname{hess}\Phi=D(\nabla\Phi),
\]
where the derivative is the Fréchet derivative over \(\mathbb R\). From `AssumptionH`, the proof obtains that \(\Phi\) is \(C^1\). It also shows that \(\nabla\Phi\) is \(C^1\): the derivative \(D\Phi\) is \(C^1\) because \(\Phi\) is \(C^2\), and the gradient is obtained from \(D\Phi\) through the Riesz isomorphism \(H\to H^*\). Consequently, for every \(z\), \(\Phi\) has gradient \(\nabla\Phi(z)\) at \(z\), and
\[
D(\nabla\Phi)(z)=\operatorname{hess}\Phi(z)
\]
as a continuous linear map \(H\to H\). These facts are used later to apply the energy and variation-of-constants lemmas.

Next the proof unfolds the trajectory hypotheses. For each \(\epsilon>0\), it defines
\[
v_\epsilon(s)=\dot x_\epsilon(s),\qquad a_\epsilon(s)=\ddot x_\epsilon(s).
\]
From `hε` and `hεreg` it records
\[
x_\epsilon(0)=x_0,\qquad v_\epsilon(0)=v_0,
\]
that \(x_\epsilon'=v_\epsilon\) and \(v_\epsilon'=a_\epsilon\), and the second-order equation
\[
\epsilon a_\epsilon(s)+\operatorname{hess}\Phi(x_\epsilon(s))v_\epsilon(s)
+\nabla\Phi(x_\epsilon(s))=0
\]
for \(s>0\). From `hcn` it records
\[
x(0)=x_0,\qquad
\operatorname{hess}\Phi(x(s))\dot x(s)+\nabla\Phi(x(s))=0
\]
for \(s>0\). Here `intro`, `rcases`, and `exact` are used to expose and specialize these hypotheses; `simpa` rewrites definitions such as \(v_\epsilon=\dot x_\epsilon\).

A key consequence of strong monotonicity is then established. The cited result `strong_mono_hessian_nonneg` says that if \(\nabla\Phi\) is strongly monotone on bounded subsets and \(\operatorname{hess}\Phi\) is its derivative, then for all \(z,w\in H\),
\[
0\le \langle \operatorname{hess}\Phi(z)w,w\rangle .
\]
The proof applies this with \(z\) and \(w\) arbitrary, using `hstrong` and the previously proved derivative formula for \(\nabla\Phi\). This nonnegativity is the source of the monotonicity of the energy and potential below.

For the \(\epsilon\)-trajectory, define the energy
\[
U_\epsilon(s)=\frac{\epsilon}{2}\|v_\epsilon(s)\|^2+\Phi(x_\epsilon(s)).
\]
The cited lemma `epsilon_energy_deriv` applies to \(\Phi\), \(\nabla\Phi\), \(\operatorname{hess}\Phi\), the trajectory \(x_\epsilon\), its velocity \(v_\epsilon\), its acceleration \(a_\epsilon\), and the \(\epsilon\)-DIN equation. It states that for every \(s>0\),
\[
\frac{d}{ds}U_\epsilon(s)
=
-\left\langle \operatorname{hess}\Phi(x_\epsilon(s))v_\epsilon(s),v_\epsilon(s)\right\rangle .
\]
By the Hessian nonnegativity just proved, this derivative is \(\le0\). The proof also checks continuity of \(U_\epsilon\) and differentiability on the interior of \([0,\infty)\), then invokes `antitoneOn_of_deriv_nonpos`, which says that a continuous function on a convex interval whose derivative is nonpositive on the interior is antitone there. Hence \(U_\epsilon\) is nonincreasing on \([0,\infty)\). Evaluating at \(0\) and \(t\) gives
\[
\frac{\epsilon}{2}\|v_\epsilon(t)\|^2+\Phi(x_\epsilon(t))
\le
\frac{\epsilon}{2}\|v_0\|^2+\Phi(x_0).
\]

The same idea is applied to the Newton trajectory with
\[
V(s)=\Phi(x(s)).
\]
The chain rule gives
\[
V'(s)=\langle \nabla\Phi(x(s)),\dot x(s)\rangle .
\]
Using the Newton equation,
\[
\operatorname{hess}\Phi(x(s))\dot x(s)=-\nabla\Phi(x(s)),
\]
so
\[
V'(s)=-\langle \operatorname{hess}\Phi(x(s))\dot x(s),\dot x(s)\rangle\le0.
\]
Thus \(V\) is nonincreasing on \([0,\infty)\), and therefore
\[
\Phi(x(t))\le \Phi(x_0)
\qquad(t\ge0).
\]

Next the proof introduces
\[
\alpha=\frac{\|v_0\|^2}{2}+\Phi(x_0).
\]
Since \(\epsilon\le1\),
\[
\frac{\epsilon}{2}\|v_0\|^2+\Phi(x_0)\le\alpha,
\]
so the energy inequality yields
\[
\Phi(x_\epsilon(t))\le\alpha.
\]
Using the lower bound \(m\le\Phi\), this also gives
\[
(\epsilon\|v_\epsilon(t)\|)^2\le 2\epsilon(\alpha-m),
\]
hence
\[
\epsilon\|v_\epsilon(t)\|\le \sqrt{2\epsilon(\alpha-m)}.
\]
The coercivity hypothesis `hcoercive` is then applied at level \(\alpha\). It supplies \(R>0\) such that \(\Phi(z)\le\alpha\) implies \(\|z\|<R\). Using the bound for \(x_\epsilon(t)\) and the monotonicity \(\Phi(x(t))\le\Phi(x_0)\le\alpha\), the proof obtains
\[
\max(\|x_\epsilon(t)\|,\|x(t)\|)<R
\]
for all \(0<\epsilon\le1\) and \(t\ge0\). Thus both curves remain in the ball where strong monotonicity is available.

Applying `hstrong` to radius \(R\) gives \(\beta>0\) such that
\[
\beta\|u-v\|^2\le
\langle \nabla\Phi(u)-\nabla\Phi(v),u-v\rangle
\]
for \(u,v\) in that ball. The cited lemma `distance_le_grad_difference` then says that if
\[
\beta\|d\|^2\le \langle g,d\rangle,
\]
then
\[
\beta\|d\|\le \|g\|.
\]
It is applied with
\[
d=x_\epsilon(t)-x(t),\qquad
g=\nabla\Phi(x_\epsilon(t))-\nabla\Phi(x(t)).
\]
Therefore
\[
\beta\|x_\epsilon(t)-x(t)\|
\le
\|\nabla\Phi(x_\epsilon(t))-\nabla\Phi(x(t))\|.
\]

The next main step is an exact integral representation of the gradient difference. The cited lemma `variation_of_constants` states that if \(q\) and \(f\) are continuous and
\[
q'(r)=-q(r)+f(r)\qquad(r>0),
\]
then for every \(s\ge0\),
\[
q(s)=e^{-s}q(0)+\int_0^s e^{-(s-r)}f(r)\,dr.
\]
The proof first applies it to
\[
q(s)=\nabla\Phi(x(s)),\qquad f=0.
\]
The Newton equation gives \(q'(r)=-\nabla\Phi(x(r))=-q(r)\). Hence
\[
\nabla\Phi(x(t))=e^{-t}\nabla\Phi(x_0).
\]
Then it defines
\[
\omega(s)=\epsilon v_\epsilon(s)+\nabla\Phi(x_\epsilon(s)).
\]
Using the \(\epsilon\)-DIN equation,
\[
\omega'(r)
=\epsilon a_\epsilon(r)+\operatorname{hess}\Phi(x_\epsilon(r))v_\epsilon(r)
=-\nabla\Phi(x_\epsilon(r))
=-\omega(r)+\epsilon v_\epsilon(r).
\]
So variation of constants with \(f(r)=\epsilon v_\epsilon(r)\) gives
\[
\omega(t)
=e^{-t}\omega(0)+\int_0^t e^{-(t-r)}\epsilon v_\epsilon(r)\,dr,
\]
and \(\omega(0)=\epsilon v_0+\nabla\Phi(x_0)\). Subtracting
\[
\nabla\Phi(x(t))=e^{-t}\nabla\Phi(x_0)
\]
and rearranging with `abel` yields
\[
\nabla\Phi(x_\epsilon(t))-\nabla\Phi(x(t))
=
e^{-t}(\epsilon v_0)-\epsilon v_\epsilon(t)
+\int_0^t e^{-(t-r)}\epsilon v_\epsilon(r)\,dr.
\]

This representation is then bounded. Put
\[
B=\sqrt{2\epsilon(\alpha-m)}.
\]
The first term satisfies
\[
\|e^{-t}(\epsilon v_0)\|\le \epsilon\|v_0\|
\]
because \(e^{-t}\le1\). The second term satisfies
\[
\|\epsilon v_\epsilon(t)\|\le B
\]
by the velocity estimate. For the integral, the proof uses the norm-integral inequality
\[
\left\|\int_0^t F(r)\,dr\right\|\le \int_0^t \|F(r)\|\,dr,
\]
then `integral_mono_on` with the pointwise bound
\[
\|e^{-(t-r)}\epsilon v_\epsilon(r)\|
\le e^{-(t-r)}B.
\]
The scalar integral is computed as
\[
\int_0^t e^{-(t-r)}B\,dr
=
B(1-e^{-t})\le B.
\]
Therefore
\[
\|\nabla\Phi(x_\epsilon(t))-\nabla\Phi(x(t))\|
\le
\epsilon\|v_0\|+2\sqrt{2\epsilon(\alpha-m)}.
\]

Now set
\[
K=\|v_0\|+2\sqrt{2(\alpha-m)},\qquad
C=\frac{K+1}{\beta}.
\]
Since \(\beta>0\), one has \(C>0\). Combining the strong-monotonicity lower bound with the gradient bound gives
\[
\beta\|x_\epsilon(t)-x(t)\|
\le
\epsilon\|v_0\|+2\sqrt{2\epsilon(\alpha-m)}.
\]
Using
\[
\sqrt{2\epsilon(\alpha-m)}
=
\sqrt{\epsilon}\sqrt{2(\alpha-m)}
\]
and \(\epsilon\le\sqrt{\epsilon}\) for \(0<\epsilon\le1\), the right-hand side is at most
\[
\sqrt{\epsilon}\,K.
\]
Hence
\[
\|x_\epsilon(t)-x(t)\|
\le
\frac{\sqrt{\epsilon}K}{\beta}
\le
\frac{K+1}{\beta}\sqrt{\epsilon}
=
C\sqrt{\epsilon}.
\]
This proves the first conjunct, the uniform \(O(\sqrt{\epsilon})\) error estimate. The arithmetic inequalities here are handled by `nlinarith` and `linarith`.

Finally, the proof proves uniform convergence. It rewrites the goal using `Metric.tendstoUniformlyOn_iff`, which says that \(x_\epsilon\to x\) uniformly on \([0,\infty)\) as \(\epsilon\to0^+\) is equivalent to: for every \(\delta>0\), eventually for \(\epsilon\) near \(0\) from the right and for every \(t\ge0\),
\[
\|x_\epsilon(t)-x(t)\|<\delta.
\]
Given \(\delta>0\), choose
\[
\eta=\min\left(1,\left(\frac{\delta}{C}\right)^2\right)>0.
\]
Eventually \(\epsilon\in(0,\eta)\). Then \(\epsilon\le1\) and
\[
\epsilon<\left(\frac{\delta}{C}\right)^2,
\]
so
\[
\sqrt{\epsilon}<\frac{\delta}{C}.
\]
Using the already proved estimate,
\[
\|x_\epsilon(t)-x(t)\|
\le
C\sqrt{\epsilon}
<
C\frac{\delta}{C}
=
\delta.
\]
Thus the required uniform convergence holds, completing the proof. In Lean, `filter_upwards` implements the “eventually” quantifier over the right-neighborhood of \(0\), `rw` and `simp` unfold the metric characterization, and `field_simp` finishes the division by \(C>0\).

