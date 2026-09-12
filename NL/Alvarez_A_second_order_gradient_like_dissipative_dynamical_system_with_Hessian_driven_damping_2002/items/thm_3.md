## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_3.lean`

## Lean statement
```lean
theorem din_weakly_converges_to_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H)
    (hΦ : AssumptionH H Φ)
    (hx : ContDiff ℝ 2 x)
    (hconvex : ConvexOn ℝ Set.univ Φ)
    (hmin : (Optimization.argminSet Φ).Nonempty)
    (hsol : IsDINTrajectory H Φ α β x) :
    (∀ z, z ∈ Optimization.argminSet Φ → ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d)) ∧
      ∃ z, z ∈ Optimization.argminSet Φ ∧
        Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The declaration `din_weakly_converges_to_argmin` is a theorem about a real Hilbert space \(H\), a real-valued function \(\Phi:H\to\mathbb R\), two real parameters \(\alpha,\beta\), and a curve \(x:\mathbb R\to H\). The hypotheses are:

- \(H\) is a complete real inner-product space, i.e. a real Hilbert space.
- \(\Phi\) satisfies the standing assumption `AssumptionH H Φ`; in the proof the concrete consequences used are that \(\Phi\) is twice continuously differentiable and bounded below.
- \(x\) is twice continuously differentiable, \(x\in C^2(\mathbb R,H)\).
- \(\Phi\) is convex on all of \(H\), in the usual real-valued sense.
- The global argmin set
  \[
  \operatorname{argminSet}\Phi=\{\,y\in H\mid \forall p,\ \Phi(y)\le \Phi(p)\,\}
  \]
  is nonempty.
- \(x\) is a trajectory of the DIN second-order gradient-like dissipative system with parameters \(\alpha,\beta\). In particular, \(\alpha>0\), \(\beta>0\), and for every \(t\ge0\),
  \[
  x''(t)=-\alpha x'(t)-\beta\,\bigl(D\nabla\Phi(x(t))\bigr)x'(t)-\nabla\Phi(x(t)).
  \]
  Here \(D\nabla\Phi(x(t))\) denotes the Fréchet derivative of \(\nabla\Phi\) at \(x(t)\), i.e. the Hessian operator.

The conclusion is a conjunction:

\[
\Bigl(\forall z,\ z\in\operatorname{argminSet}\Phi
\ \Rightarrow\ \exists d\in\mathbb R,\ 
\|x(t)-z\|\to d\Bigr)
\]
and
\[
\exists z,\ z\in\operatorname{argminSet}\Phi
\ \wedge\ x(t)\rightharpoonup z
\]
where the weak convergence is written in Lean as convergence of \(t\mapsto \operatorname{toWeakSpace}_{\mathbb R,H}(x(t))\) to \(\operatorname{toWeakSpace}_{\mathbb R,H}(z)\).

In ordinary language: along every global minimizer \(z\) of \(\Phi\), the distance from the trajectory \(x(t)\) to \(z\) converges to a finite limit as \(t\to\infty\); moreover, the trajectory converges weakly to some global minimizer of \(\Phi\).

## Lean proof
```lean
by
  have hα : 0 < α := hsol.1
  have hβ : 0 < β := hsol.2.1
  have hαβ : 0 < α * β + 1 := by positivity
  have hΦC2 : ContDiff ℝ 2 Φ := hΦ.twice_continuously_differentiable
  have hΦC1 : ContDiff ℝ 1 Φ := hΦC2.of_le (by norm_num)
  have hgradF : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using
      ((hΦC1.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt)
  have hgrad_zero : ∀ z, z ∈ Optimization.argminSet Φ → gradient Φ z = 0 := by
    intro z hz
    have hzlocal : IsLocalMin Φ z := by
      exact Filter.Eventually.of_forall (fun y => hz y)
    have hstat : fderiv ℝ Φ z = 0 := hzlocal.fderiv_eq_zero
    have hdual : innerSL ℝ (gradient Φ z) = 0 := by
      rw [← (hgradF z).fderiv]
      exact hstat
    apply (innerSL_inj (𝕜 := ℝ) (E := H)).mp
    simpa only [map_zero] using hdual
  have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by simpa using hΦC2)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hΦderivC1
  have hgradDeriv : ∀ z, HasFDerivAt (gradient Φ)
      (fderiv ℝ (gradient Φ) z) z := by
    intro z
    exact (hgradC1.differentiable (by norm_num) z).hasFDerivAt
  have hgradCompC1 : ContDiff ℝ 1 (fun t => gradient Φ (x t)) := by
    simpa [Function.comp_def] using hgradC1.comp (hx.of_le (by norm_num))
  have hglobal := din_forward_internal Φ hΦ α β hα hβ (x 0) (deriv x 0)
  obtain ⟨xg, vg, accg, hxg0, hvg0, hforward, huniq, henergy, hvl2, hgl2,
    hphil, hres, hbounded, hderivg⟩ := hglobal
  have hxdata := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) x by simpa using hx)
  have hvC1 : ContDiff ℝ 1 (deriv x) := by simpa using hxdata.2.2
  have hvdata := contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (0 + 1) (deriv x) by simpa using hvC1)
  have heq := huniq x (by rfl) (by rfl) hsol hx
  have hxg_eq : ∀ t, 0 ≤ t → xg t = x t := fun t ht => (heq t ht).1.symm
  have hvg_eq : ∀ t, 0 ≤ t → vg t = deriv x t := fun t ht => (heq t ht).2.symm
  have hphi_x : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := by
    rcases hphil with ⟨l, hl⟩
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hxg_eq t ht]
  have hres_x : Tendsto (fun t => deriv x t + β • gradient Φ (x t)) atTop (nhds 0) := by
    apply hres.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hvg_eq t ht, hxg_eq t ht]
  let E : ℝ → ℝ := fun t => (α * β + 1) * Φ (x t) +
    (1 / 2) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2
  have hE_lim : ∃ l : ℝ, Tendsto E atTop (nhds l) := by
    rcases hphi_x with ⟨l, hl⟩
    have hpot : Tendsto (fun t => (α * β + 1) * Φ (x t)) atTop
        (nhds ((α * β + 1) * l)) :=
      tendsto_const_nhds.mul hl
    have hsq : Tendsto (fun t => ‖deriv x t + β • gradient Φ (x t)‖ ^ 2) atTop
        (nhds (‖(0 : H)‖ ^ 2)) := hres_x.norm.pow 2
    have hkin : Tendsto (fun t => (1 / 2 : ℝ) *
        ‖deriv x t + β • gradient Φ (x t)‖ ^ 2) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hsq)
    refine ⟨(α * β + 1) * l, ?_⟩
    simpa [E] using hpot.add hkin
  have hdist : ∀ z, z ∈ Optimization.argminSet Φ →
      ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d) := by
    intro z hz
    have hzgrad : gradient Φ z = 0 := hgrad_zero z hz
    have hgrad_inner : ∀ y : H, 0 ≤ inner ℝ (gradient Φ y) (y - z) := by
      intro y
      let u : H := y - z
      let line : ℝ → H := fun s => z + s • u
      let f : ℝ → ℝ := fun s => Φ (line s)
      have hline : ∀ s, HasDerivAt line u s := by
        intro s
        simpa [line] using (hasDerivAt_id s).smul_const u |>.const_add z
      have hfderiv : ∀ s, HasDerivAt f (inner ℝ (gradient Φ (line s)) u) s := by
        intro s
        simpa [f, Function.comp_def, innerSL_apply_apply] using
          (hgradF (line s)).comp_hasDerivAt s (hline s)
      have hfconvex : ConvexOn ℝ Set.univ f := by
        have hcomp := hconvex.comp_affineMap (AffineMap.lineMap z y)
        have hline_eq : line = AffineMap.lineMap z y := by
          funext s
          simp [line, u, AffineMap.lineMap_apply]
          module
        simpa [f, hline_eq, Function.comp_def] using hcomp
      have hfmono : Monotone (deriv f) := by
        simpa only [monotoneOn_univ] using hfconvex.monotoneOn_deriv
          (fun s _ => (hfderiv s).differentiableAt)
      have hmono := hfmono (show (0 : ℝ) ≤ 1 by norm_num)
      rw [(hfderiv 0).deriv, (hfderiv 1).deriv] at hmono
      simpa [line, u, hzgrad] using hmono
    let v : ℝ → H := deriv x
    let g : ℝ → H := fun t => gradient Φ (x t)
    let r : ℝ → H := fun t => v t + β • g t
    let u : ℝ → H := fun t => x t - z
    let ε : ℝ := min 1 (α / (4 * (β + 1)))
    have hε : 0 < ε := by
      dsimp [ε]
      exact lt_min (by norm_num) (div_pos hα (by positivity))
    have hεone : ε ≤ 1 := min_le_left _ _
    have hεfrac : ε ≤ α / (4 * (β + 1)) := min_le_right _ _
    have hβ1 : 0 < β + 1 := by linarith
    have hεα : ε / α ≤ 1 / 4 := by
      apply (div_le_iff₀ hα).2
      have hprod : ε * (β + 1) ≤ α / 4 := by
        calc
          ε * (β + 1) ≤ (α / (4 * (β + 1))) * (β + 1) :=
            mul_le_mul_of_nonneg_right hεfrac (by positivity)
          _ = α / 4 := by field_simp
      nlinarith
    have hcoefv : 0 ≤ α - ε - ε * β / 2 := by
      have htmp : ε * (1 + β / 2) ≤ α := by
        have h1 : 1 + β / 2 ≤ β + 1 := by linarith
        have hmul := mul_le_mul_of_nonneg_left h1 hε.le
        have hprod : ε * (β + 1) ≤ α / 4 := by
          calc
            ε * (β + 1) ≤ (α / (4 * (β + 1))) * (β + 1) :=
              mul_le_mul_of_nonneg_right hεfrac (by positivity)
            _ = α / 4 := by field_simp
        nlinarith
      nlinarith
    have hcoefg : 0 ≤ β * (1 - ε / 2) := by
      have : 0 ≤ 1 - ε / 2 := by linarith
      positivity
    have hgrad_at (t : ℝ) : HasDerivAt g
        ((fderiv ℝ (gradient Φ) (x t)) (v t)) t := by
      dsimp [g, v]
      simpa [Function.comp_def] using
        (hgradDeriv (x t)).comp_hasDerivAt t ((hx.differentiable (by norm_num) t).hasDerivAt)
    have hr_at (t : ℝ) (ht : 0 ≤ t) : HasDerivAt r (-α • v t - g t) t := by
      have hv_at : HasDerivAt v (deriv (deriv x) t) t := by
        simpa [v] using (hx.differentiable_deriv_two t).hasDerivAt
      have hraw := (hv_at.add ((hgrad_at t).const_smul β))
      have heq := hsol.2.2 t ht
      convert hraw using 1
      dsimp [r]
      rw [show deriv (deriv x) t =
          -(α • deriv x t + β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) +
            gradient Φ (x t)) by
          exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using heq)]
      simp only [neg_smul]
      module
    have hu_at (t : ℝ) : HasDerivAt u (v t) t := by
      dsimp [u, v]
      simpa using ((hx.differentiable (by norm_num) t).hasDerivAt.sub_const z)
    have hE_at (t : ℝ) (ht : 0 ≤ t) : HasDerivAt E
        (-α * ‖v t‖ ^ 2 - β * ‖g t‖ ^ 2) t := by
      have hp := (hgradF (x t)).comp_hasDerivAt t
        ((hx.differentiable (by norm_num) t).hasDerivAt)
      have hp' : HasDerivAt (fun s => Φ (x s)) (inner ℝ (g t) (v t)) t := by
        simpa [g, v, Function.comp_def, innerSL_apply_apply] using hp
      have hk := ((hr_at t ht).norm_sq.const_mul (1 / 2 : ℝ))
      have he := (hp'.const_smul (α * β + 1)).add hk
      have hinner : inner ℝ (v t) (g t) = inner ℝ (g t) (v t) := real_inner_comm _ _
      convert he using 1
      dsimp [E, r, v, g]
      simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
        real_inner_self_eq_norm_sq]
      simp [real_inner_comm]
      ring_nf
    let haux : ℝ → ℝ := fun t => E t + ε *
      (α / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t))
    have haux_at (t : ℝ) (ht : 0 ≤ t) : HasDerivAt haux
        (-(α - ε) * ‖v t‖ ^ 2 - β * ‖g t‖ ^ 2
          - ε * inner ℝ (g t) (u t) + ε * β * inner ℝ (g t) (v t)) t := by
      have hu := hu_at t
      have hk := (hu.norm_sq.const_mul (α / 2))
      have hi := (hr_at t ht).inner ℝ (hu_at t)
      have hi' := (hk.add hi).const_smul ε
      have he := (hE_at t ht).add hi'
      change HasDerivAt (fun t => E t + ε *
        (α / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t))) _ _
      convert he using 1
      simp only [smul_eq_mul]
      have hi1 : inner ℝ (-α • v t - g t) (u t) =
          -(α * inner ℝ (v t) (u t)) - inner ℝ (g t) (u t) := by
        rw [inner_sub_left, inner_smul_left]
        norm_num
      have hi2 : inner ℝ (v t + β • g t) (v t) =
          ‖v t‖ ^ 2 + β * inner ℝ (g t) (v t) := by
        rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
        simp
      rw [hi1, hi2]
      rw [real_inner_comm (u t) (v t)]
      ring_nf
    have haux_deriv_nonpos : ∀ t, 0 ≤ t → deriv haux t ≤ 0 := by
      intro t ht
      rw [(haux_at t ht).deriv]
      have hy := real_inner_le_norm (g t) (v t)
      have hy' : -‖g t‖ * ‖v t‖ ≤ inner ℝ (g t) (v t) := by
        have h := real_inner_le_norm (-(g t)) (v t)
        rw [inner_neg_left, norm_neg] at h
        linarith
      have hyoung : ε * β * inner ℝ (g t) (v t) ≤
          ε * β / 2 * (‖g t‖ ^ 2 + ‖v t‖ ^ 2) := by
        have hs := sq_nonneg (‖g t‖ - ‖v t‖)
        have hp : 0 ≤ ε * β := mul_nonneg hε.le hβ.le
        nlinarith
      have hgu : 0 ≤ inner ℝ (g t) (u t) := by
        simpa [g, u] using hgrad_inner (x t)
      nlinarith [hcoefv, hcoefg, hyoung]
    have haux_cont : ContinuousOn haux (Set.Ici 0) := by
      intro t ht
      exact (haux_at t ht).continuousAt.continuousWithinAt
    have haux_diff : DifferentiableOn ℝ haux (interior (Set.Ici 0)) := by
      intro t ht
      have ht' : t ∈ Set.Ioi (0 : ℝ) := by simpa [interior_Ici] using ht
      exact (haux_at t (le_of_lt ht')).differentiableAt.differentiableWithinAt
    have haux_anti : AntitoneOn haux (Set.Ici 0) :=
      antitoneOn_of_deriv_nonpos (convex_Ici 0) haux_cont haux_diff
        (fun t ht => haux_deriv_nonpos t (le_of_lt (by simpa [interior_Ici] using ht)))
    rcases hΦ.bounded_below with ⟨m, hm⟩
    have hE_lower : ∀ t, 0 ≤ t → (α * β + 1) * m ≤ E t := by
      intro t ht
      dsimp [E]
      have := hm (x t)
      nlinarith [sq_nonneg ‖deriv x t + β • gradient Φ (x t)‖]
    have haux_lower : ∀ t, 0 ≤ t →
        (α * β + 1) * m + ε * α / 4 * ‖u t‖ ^ 2 ≤ haux t := by
      intro t ht
      have hcross := real_inner_le_norm (-(r t)) (u t)
      rw [inner_neg_left, norm_neg] at hcross
      have hcross' : -‖r t‖ * ‖u t‖ ≤ inner ℝ (r t) (u t) := by linarith
      have hs := sq_nonneg (‖r t‖ - α * ‖u t‖)
      have hsq : ‖r t‖ ^ 2 ≤ 2 * (E t - (α * β + 1) * m) := by
        dsimp [E, r]
        have := hm (x t)
        nlinarith [sq_nonneg ‖deriv x t + β • gradient Φ (x t)‖]
      have hA := hE_lower t ht
      have hepscoef : 0 ≤ 1 - ε / α := by linarith
      dsimp [haux]
      have hαne : α ≠ 0 := ne_of_gt hα
      have hinv : α * (1 / α) = 1 := by field_simp
      have hcross_param : -(α / 4) * ‖u t‖ ^ 2 - (1 / α) * ‖r t‖ ^ 2 ≤
          inner ℝ (r t) (u t) := by
        nlinarith [sq_nonneg (‖r t‖ - (α / 2) * ‖u t‖)]
      have hratio : 2 * (ε / α) ≤ 1 / 2 := by linarith
      have hdiv : (1 / α) * ‖r t‖ ^ 2 ≤
          (1 / α) * (2 * (E t - (α * β + 1) * m)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have hcoef2 : 0 ≤ 1 - 2 * (ε / α) := by linarith
      have hprod2 : 0 ≤ (1 - 2 * (ε / α)) *
          (E t - (α * β + 1) * m) :=
        mul_nonneg hcoef2 (sub_nonneg.mpr hA)
      have hEcomb : (α * β + 1) * m ≤ E t -
          2 * (ε / α) * (E t - (α * β + 1) * m) := by
        nlinarith [hprod2]
      have hcross2 : E t + ε * (α / 2 * ‖u t‖ ^ 2 +
          inner ℝ (r t) (u t)) ≥ E t + ε *
          (α / 4 * ‖u t‖ ^ 2 - (1 / α) * ‖r t‖ ^ 2) := by
        have h := add_le_add_left hcross_param (α / 2 * ‖u t‖ ^ 2)
        have h' := mul_le_mul_of_nonneg_left h hε.le
        linarith
      have hcross3 : E t + ε * (α / 4 * ‖u t‖ ^ 2 -
          (1 / α) * ‖r t‖ ^ 2) ≥ E t + ε *
          (α / 4 * ‖u t‖ ^ 2 - (1 / α) *
            (2 * (E t - (α * β + 1) * m))) := by
        have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hdiv 0) hε.le
        linarith
      have hqnonneg : 0 ≤ ε * α / 4 * ‖u t‖ ^ 2 := by positivity
      have hstep : (α * β + 1) * m + ε * α / 4 * ‖u t‖ ^ 2 ≤
          E t + ε * (α / 4 * ‖u t‖ ^ 2 -
            (1 / α) * (2 * (E t - (α * β + 1) * m))) := by
        have h := add_le_add_right hEcomb (ε * α / 4 * ‖u t‖ ^ 2)
        convert h using 1 <;> field_simp [hαne] <;> ring
      have hstep' : (α * β + 1) * m + ε * α / 4 * ‖u t‖ ^ 2 ≤
          E t + ε * (α / 4 * ‖u t‖ ^ 2 - (1 / α) * ‖r t‖ ^ 2) :=
        hstep.trans hcross3
      have hfinal : (α * β + 1) * m + ε * α / 4 * ‖u t‖ ^ 2 ≤
          E t + ε * (α / 2 * ‖u t‖ ^ 2 + inner ℝ (r t) (u t)) :=
        hstep'.trans hcross2
      exact hfinal
    let q : ℝ → ℝ := fun t => haux (max t 0)
    have hqanti : Antitone q := by
      intro s t hst
      exact haux_anti (le_max_right s 0) (le_max_right t 0)
        (max_le_max_right 0 hst)
    have hq_lower : BddBelow (Set.range q) := by
      refine ⟨(α * β + 1) * m, ?_⟩
      rintro y ⟨t, rfl⟩
      exact (le_add_of_nonneg_right (by positivity)).trans
        (haux_lower (max t 0) (le_max_right t 0))
    have haux_lim : ∃ l : ℝ, Tendsto haux atTop (nhds l) := by
      refine ⟨⨅ t, q t, ?_⟩
      apply (tendsto_atTop_ciInf hqanti hq_lower).congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp [q, max_eq_left ht]
    rcases haux_lim with ⟨laux, hlaux⟩
    have hdist_sq_lim : ∃ l : ℝ, Tendsto (fun t => ‖u t‖ ^ 2) atTop (nhds l) := by
      have hupper : ∀ t, 0 ≤ t → haux t ≤ haux 0 := by
        intro t ht
        exact haux_anti (by simp) (by exact ht) ht
      let Q : ℝ := 4 * (haux 0 - (α * β + 1) * m) / (ε * α)
      have hQ : 0 ≤ Q := by
        have h0 := haux_lower 0 (by norm_num)
        have hpos : 0 < ε * α := mul_pos hε hα
        have hnum : 0 ≤ haux 0 - (α * β + 1) * m := by
          nlinarith [sq_nonneg ‖u 0‖]
        dsimp [Q]
        positivity
      have hQbound : ∀ t, 0 ≤ t → ‖u t‖ ^ 2 ≤ Q := by
        intro t ht
        have hl := haux_lower t ht
        have hu := hupper t ht
        have hpos : 0 < ε * α := mul_pos hε hα
        dsimp [Q]
        apply (le_div_iff₀ hpos).2
        nlinarith
      have hCbound : ∃ C : ℝ, ∀ t, 0 ≤ t → ‖u t‖ ≤ C := by
        refine ⟨Real.sqrt Q, ?_⟩
        intro t ht
        have hq := hQbound t ht
        have hsqrt : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
        nlinarith [Real.sqrt_nonneg Q, norm_nonneg (u t)]
      have hu_bounded : Bornology.IsBounded (u '' Set.Ici (0 : ℝ)) := by
        rcases hCbound with ⟨C, hC⟩
        apply isBounded_iff_forall_norm_le.mpr
        exact ⟨C, by rintro q ⟨t, ht, rfl⟩; exact hC t ht⟩
      have hrnorm : Tendsto (fun t => ‖r t‖) atTop (nhds 0) := by
        simpa [r] using hres_x.norm
      have hinner_lim : Tendsto (fun t => inner ℝ (r t) (u t)) atTop (nhds 0) := by
        have hbound : ∀ᶠ t in atTop, ‖inner ℝ (r t) (u t)‖ ≤
            Real.sqrt Q * ‖r t‖ := by
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          rw [Real.norm_eq_abs]
          have hnormu : ‖u t‖ ≤ Real.sqrt Q := by
            have hq := hQbound t ht
            have hsqrt : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
            nlinarith [Real.sqrt_nonneg Q, norm_nonneg (u t)]
          exact (abs_real_inner_le_norm (r t) (u t)).trans
            (by
              calc
                ‖r t‖ * ‖u t‖ ≤ ‖r t‖ * Real.sqrt Q :=
                  mul_le_mul_of_nonneg_left hnormu (norm_nonneg (r t))
                _ = Real.sqrt Q * ‖r t‖ := by ring)
        have hprod : Tendsto (fun t => Real.sqrt Q * ‖r t‖) atTop (nhds 0) := by
          simpa using (tendsto_const_nhds.mul hrnorm)
        exact squeeze_zero_norm' hbound hprod
      rcases hE_lim with ⟨lE, hlE⟩
      have hdiff : Tendsto (fun t => haux t - E t) atTop
          (nhds (laux - lE)) := hlaux.sub hlE
      have hsub := hdiff.sub (hinner_lim.const_mul ε)
      have hscale := hsub.const_mul (2 / (ε * α))
      have hscale' : Tendsto (fun t => 2 / (ε * α) *
          (haux t - E t - ε * inner ℝ (r t) (u t))) atTop
          (nhds ((2 / (ε * α)) * (laux - lE))) := by
        simpa using hscale
      refine ⟨(2 / (ε * α)) * (laux - lE), ?_⟩
      convert hscale' using 1
      funext t
      dsimp [haux]
      field_simp [ne_of_gt (mul_pos hε hα)]
      ring
    rcases hdist_sq_lim with ⟨lq, hlq⟩
    have hlq_nonneg : 0 ≤ lq :=
      ge_of_tendsto hlq (Filter.Eventually.of_forall (fun t => sq_nonneg ‖u t‖))
    have hnorm_lim : Tendsto (fun t => ‖u t‖) atTop (nhds (Real.sqrt lq)) := by
      have hs : Tendsto (fun y : ℝ => Real.sqrt y) (nhds lq)
          (nhds (Real.sqrt lq)) := Real.continuous_sqrt.continuousAt
      have hs := hs.comp hlq
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs
    refine ⟨Real.sqrt lq, ?_⟩
    simpa [u] using hnorm_lim
  have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    rcases hmin with ⟨z₀, hz₀⟩
    rcases hdist z₀ hz₀ with ⟨d₀, hd₀⟩
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hd₀) 1 zero_lt_one
    let T₀ : ℝ := max T 0
    have htail : ∀ t, T₀ ≤ t → ‖x t - z₀‖ ≤ |d₀| + 1 := by
      intro t ht
      have hdist' : dist (‖x t - z₀‖) d₀ < 1 := by
        simpa [Real.dist_eq] using hT t (le_trans (le_max_left T 0) ht)
      have habs : |‖x t - z₀‖ - d₀| < 1 := by simpa [Real.dist_eq] using hdist'
      have hle : ‖x t - z₀‖ - d₀ ≤ |‖x t - z₀‖ - d₀| := le_abs_self _
      have hnormd : ‖x t - z₀‖ ≤ d₀ + 1 := by nlinarith
      exact hnormd.trans (by linarith [le_abs_self d₀])
    have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
      exact isCompact_Icc.image_of_continuousOn hx.continuous.continuousOn
    rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨max R₀ (|d₀| + 1 + ‖z₀‖), ?_⟩
    rintro q ⟨t, ht, rfl⟩
    by_cases hle : t ≤ T₀
    · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
    · have hge : T₀ ≤ t := le_of_not_ge hle
      have htri : ‖x t‖ ≤ ‖x t - z₀‖ + ‖z₀‖ := by
        calc
          ‖x t‖ = ‖(x t - z₀) + z₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖x t - z₀‖ + ‖z₀‖ := norm_add_le _ _
      have htri' : ‖x t - z₀‖ + ‖z₀‖ ≤ (|d₀| + 1) + ‖z₀‖ :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right (htail t hge) ‖z₀‖)
      exact (htri.trans htri').trans (le_max_right _ _)
  have hxg_bounded : Bornology.IsBounded (xg '' Set.Ici (0 : ℝ)) := by
    apply hx_bounded.subset
    rintro q ⟨t, ht, rfl⟩
    rw [hxg_eq t ht]
    exact ⟨t, ht, rfl⟩
  obtain ⟨_, _, _, _, _, _, hgradlim⟩ := hbounded hxg_bounded
  have hgrad_at_top : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := by
    apply hgradlim.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hxg_eq t ht]
  have hgrad_at (y : H) : HasGradientAt Φ (gradient Φ y) y := by
    exact (hΦC1.differentiable (by norm_num) y).hasGradientAt
  have hsupport : ∀ y p : H,
      Φ y + inner ℝ (gradient Φ y) (p - y) ≤ Φ p := by
    intro y p
    exact convex_supporting_baillon_haddad Φ (gradient Φ) hconvex hgrad_at y p
  have hinner_zero_of_strong_bounded : ∀ (a b : ℕ → H),
      Tendsto a atTop (nhds 0) → Bornology.IsBounded (Set.range b) →
        Tendsto (fun n => inner ℝ (a n) (b n)) atTop (nhds 0) := by
    intro a b ha hb
    rcases isBounded_iff_forall_norm_le.mp hb with ⟨C, hC⟩
    let M : ℝ := max C 0
    have hbM : ∀ n, ‖b n‖ ≤ M := by
      intro n
      exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)
    have hanorm : Tendsto (fun n => ‖a n‖) atTop (nhds 0) := by
      simpa using ha.norm
    have hbound : ∀ n, |inner ℝ (a n) (b n)| ≤ ‖a n‖ * M := by
      intro n
      calc
        |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (a n) (b n)
        _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left (hbM n) (norm_nonneg _)
    have hmajor : Tendsto (fun n => ‖a n‖ * M) atTop (nhds 0) := by
      simpa [zero_mul] using hanorm.mul tendsto_const_nhds
    have habs : Tendsto (fun n => |inner ℝ (a n) (b n)|) atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hbound hmajor
    have hneg : Tendsto (fun n => -|inner ℝ (a n) (b n)|) atTop (nhds 0) := by
      simpa using habs.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
      (fun _ => neg_abs_le _) (fun _ => le_abs_self _)
  have hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ Optimization.argminSet Φ := by
    intro s hs z hweak
    rcases hphi_x with ⟨l, hl⟩
    have hgrad_seq : Tendsto (fun n => gradient Φ (x (s n))) atTop (nhds 0) :=
      hgrad_at_top.comp hs
    have hxseq_bounded : Bornology.IsBounded (Set.range (fun n => x (s n))) :=
      bounded_range_of_tendsto_weakly hweak
    have hinner_x : Tendsto
        (fun n => inner ℝ (gradient Φ (x (s n))) (x (s n))) atTop (nhds 0) :=
      hinner_zero_of_strong_bounded _ _ hgrad_seq hxseq_bounded
    have hineq_limit : ∀ p : H, l ≤ Φ p := by
      intro p
      have hlseq : Tendsto (fun n => Φ (x (s n))) atTop (nhds l) := hl.comp hs
      have hinner_p : Tendsto
          (fun n => inner ℝ (gradient Φ (x (s n))) p) atTop (nhds 0) := by
        simpa using hinner_zero_of_strong_bounded _ (fun _ => p) hgrad_seq
          (by simp)
      have hinner_diff : Tendsto
          (fun n => inner ℝ (gradient Φ (x (s n))) (p - x (s n))) atTop (nhds 0) := by
        simpa [inner_sub_right] using hinner_p.sub hinner_x
      have hsum : Tendsto
          (fun n => Φ (x (s n)) + inner ℝ (gradient Φ (x (s n)))
            (p - x (s n))) atTop (nhds l) := by
        simpa using hlseq.add hinner_diff
      apply le_of_tendsto hsum
      exact Filter.Eventually.of_forall (fun n => hsupport (x (s n)) p)
    let f : H → EReal := fun y => (Φ y : EReal)
    have hf_lsc : LowerSemicontinuous f := by
      simpa [f] using (continuous_coe_real_ereal.comp hΦC2.continuous).lowerSemicontinuous
    have hf_quasi : QuasiconvexOn ℝ Set.univ f := by
      rw [ERealFunction.quasiconvexOn_univ_iff_convex_lowerLevelSet f]
      intro ξ
      apply (convex_iff_forall_pos).2
      intro a ha b hb wa wb hwa hwb hwab
      have haE := (ERealFunction.mem_lowerLevelSet_iff f ξ a).1 ha
      have hbE := (ERealFunction.mem_lowerLevelSet_iff f ξ b).1 hb
      change (Φ a : EReal) ≤ (ξ : EReal) at haE
      change (Φ b : EReal) ≤ (ξ : EReal) at hbE
      have ha' : Φ a ≤ ξ := by exact_mod_cast haE
      have hb' : Φ b ≤ ξ := by exact_mod_cast hbE
      have hconv := hconvex.2 (Set.mem_univ a) (Set.mem_univ b) hwa.le hwb.le hwab
      have hconv' : Φ (wa • a + wb • b) ≤ wa * Φ a + wb * Φ b := by
        simpa [smul_eq_mul] using hconv
      have hweighted : wa * Φ a + wb * Φ b ≤ ξ := by
        calc
          wa * Φ a + wb * Φ b ≤ wa * ξ + wb * ξ := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ha' hwa.le)
              (mul_le_mul_of_nonneg_left hb' hwb.le)
          _ = ξ := by rw [← add_mul, hwab, one_mul]
      have hcombo : Φ (wa • a + wb • b) ≤ ξ := hconv'.trans hweighted
      apply (ERealFunction.mem_lowerLevelSet_iff f ξ (wa • a + wb • b)).2
      change (Φ (wa • a + wb • b) : EReal) ≤ (ξ : EReal)
      exact_mod_cast hcombo
    have hfweak_lsc := ERealFunction.weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
    have hlseq : Tendsto (fun n => Φ (x (s n))) atTop (nhds l) := hl.comp hs
    have hlseqE : Tendsto (fun n => f (x (s n))) atTop (nhds (l : EReal)) := by
      simpa [f] using (continuous_coe_real_ereal.tendsto l).comp hlseq
    have hz_le_l : f z ≤ (l : EReal) := by
      calc
        f z = (f ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H z) := by simp
        _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm)
            (nhds (toWeakSpace ℝ H z)) := hfweak_lsc.le_liminf _
        _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm)
            (Filter.map (fun n => toWeakSpace ℝ H (x (s n))) atTop) :=
          Filter.liminf_le_liminf_of_le hweak
        _ = liminf (f ∘ (fun n => x (s n))) atTop := by
          rw [← Filter.liminf_comp]
          congr 1
        _ = (l : EReal) := hlseqE.liminf_eq
    have hz_le_l_real : Φ z ≤ l := by
      change (Φ z : EReal) ≤ (l : EReal) at hz_le_l
      exact_mod_cast hz_le_l
    have hl_le_z := hineq_limit z
    have hz_eq : Φ z = l := le_antisymm hz_le_l_real hl_le_z
    intro y
    have hl_le_y := hineq_limit y
    rw [hz_eq]
    exact hl_le_y
  exact ⟨hdist, Alvarez2002.opial_continuous_time x (Optimization.argminSet Φ) hmin hcluster hdist⟩
```

## Proof explanation
The proof begins by extracting the positivity of the parameters and the differential equation from the hypothesis `hsol : IsDINTrajectory H Φ α β x`. The terms `hsol.1` and `hsol.2.1` give \(0<\alpha\) and \(0<\beta\). Later, `hsol.2.2 t ht` is used as the second-order equation
\[
x''(t)=-\alpha x'(t)-\beta\,\bigl(D\nabla\Phi(x(t))\bigr)x'(t)-\nabla\Phi(x(t)),
\]
for \(t\ge0\).

The proof then records differentiability facts. From `hΦ` it obtains that \(\Phi\) is \(C^2\), hence also \(C^1\). For every \(z\in H\), it obtains
\[
D\Phi(z)=\langle \nabla\Phi(z),\cdot\rangle,
\]
i.e. the Fréchet derivative of \(\Phi\) at \(z\) is the continuous linear functional \(h\mapsto \langle \nabla\Phi(z),h\rangle\). This is the Riesz-representation form of the gradient. The proof also shows that \(\nabla\Phi\) is \(C^1\): since \(\Phi\) is \(C^2\), its Fréchet derivative \(D\Phi\) is \(C^1\), and the Riesz map identifying \(D\Phi\) with \(\nabla\Phi\) preserves smoothness.

Next, the proof establishes that at any global minimizer \(z\) of \(\Phi\), one has
\[
\nabla\Phi(z)=0.
\]
Indeed, a global minimizer is a local minimizer. If \(z\) is a local minimizer of \(\Phi\), then \(D\Phi(z)=0\). Since \(D\Phi(z)=\langle \nabla\Phi(z),\cdot\rangle\), the Riesz map is injective, so \(\nabla\Phi(z)=0\). This fact is used repeatedly.

The main existential theorem `din_forward_internal` is then applied to \(\Phi,\alpha,\beta\) and the initial data \(x(0),x'(0)\). That theorem produces a trajectory \(x_g\), a velocity \(v_g\), and an acceleration \(a_g\) for the same DIN system. The parts used in this proof are:

- \(x_g\) is a DIN trajectory with \(x_g(0)=x(0)\) and \(v_g(0)=x'(0)\).
- Any \(C^2\) DIN trajectory with the same initial position and velocity agrees with \(x_g\), and its derivative agrees with \(v_g\), for all \(t\ge0\).
- \(\Phi(x_g(t))\) converges to some real number \(l\) as \(t\to\infty\).
- \(v_g(t)+\beta\nabla\Phi(x_g(t))\to0\).
- \(v_g\) and \(\nabla\Phi(x_g(\cdot))\) are square-integrable on \((0,\infty)\).
- If \(x_g\) is bounded on \(t\ge0\), then \(v_g,a_g,\nabla\Phi(x_g(\cdot))\), and the Hessian along \(x_g\) are bounded, and \(v_g,a_g,\nabla\Phi(x_g(\cdot))\) all tend to \(0\).

Using the uniqueness clause, the proof identifies \(x_g(t)=x(t)\) and \(v_g(t)=x'(t)\) for all \(t\ge0\). Therefore
\[
\Phi(x(t))\to l
\]
for some \(l\in\mathbb R\), and
\[
x'(t)+\beta\nabla\Phi(x(t))\to0.
\]
The proof then defines the energy
\[
E(t)=(\alpha\beta+1)\Phi(x(t))+\frac12\|x'(t)+\beta\nabla\Phi(x(t))\|^2.
\]
Since \(\Phi(x(t))\) converges and \(x'(t)+\beta\nabla\Phi(x(t))\to0\), the energy \(E(t)\) also converges to a finite limit.

The core of the proof is the distance-convergence statement. Fix \(z\in\operatorname{argminSet}\Phi\). First, \(\nabla\Phi(z)=0\). The proof then derives the convexity inequality
\[
\langle \nabla\Phi(y),y-z\rangle\ge0
\qquad(y\in H).
\]
This is obtained by considering the line \(s\mapsto z+s(y-z)\) and the real function
\[
f(s)=\Phi(z+s(y-z)).
\]
Because \(\Phi\) is convex, \(f\) is convex. For a convex differentiable function on \(\mathbb R\), the derivative is monotone, so \(f'(0)\le f'(1)\). The chain rule gives
\[
f'(0)=\langle \nabla\Phi(z),y-z\rangle=0,
\qquad
f'(1)=\langle \nabla\Phi(y),y-z\rangle.
\]
Hence \(f'(1)\ge0\), which is the displayed inequality.

Now set
\[
v(t)=x'(t),\qquad
g(t)=\nabla\Phi(x(t)),\qquad
r(t)=v(t)+\beta g(t),\qquad
u(t)=x(t)-z.
\]
Choose
\[
\epsilon=\min\left(1,\frac{\alpha}{4(\beta+1)}\right).
\]
Then \(0<\epsilon\), \(\epsilon\le1\), and \(\epsilon\le \alpha/(4(\beta+1))\). These imply the auxiliary coefficient inequalities
\[
\alpha-\epsilon-\frac{\epsilon\beta}{2}\ge0,
\qquad
\beta\left(1-\frac{\epsilon}{2}\right)\ge0.
\]

The proof computes derivatives. From the ODE one gets
\[
r'(t)=-\alpha v(t)-g(t),
\]
because \(r=x'+\beta\nabla\Phi(x)\) and the Hessian terms cancel. Also \(u'(t)=v(t)\). The energy satisfies
\[
E'(t)=-\alpha\|v(t)\|^2-\beta\|g(t)\|^2.
\]
Indeed,
\[
E'=(\alpha\beta+1)\langle g,v\rangle+\langle r,r'\rangle
\]
and substituting \(r=v+\beta g\), \(r'=-\alpha v-g\) gives the displayed cancellation.

The proof then introduces the auxiliary Lyapunov function
\[
h(t)=E(t)+\epsilon\left(\frac{\alpha}{2}\|u(t)\|^2+\langle r(t),u(t)\rangle\right).
\]
A direct differentiation gives
\[
h'(t)=-(\alpha-\epsilon)\|v(t)\|^2-\beta\|g(t)\|^2
-\epsilon\langle g(t),u(t)\rangle
+\epsilon\beta\langle g(t),v(t)\rangle.
\]
The convexity inequality gives \(\langle g(t),u(t)\rangle\ge0\), so the term \(-\epsilon\langle g(t),u(t)\rangle\) is nonpositive. Cauchy–Schwarz and Young’s inequality give
\[
\epsilon\beta\langle g(t),v(t)\rangle
\le \frac{\epsilon\beta}{2}\bigl(\|g(t)\|^2+\|v(t)\|^2\bigr).
\]
Therefore
\[
h'(t)\le
-\left(\alpha-\epsilon-\frac{\epsilon\beta}{2}\right)\|v(t)\|^2
-\beta\left(1-\frac{\epsilon}{2}\right)\|g(t)\|^2\le0.
\]
Thus \(h\) is nonincreasing on \([0,\infty)\), by the standard criterion that a differentiable function with nonpositive derivative on an interval is antitone.

The hypothesis that \(\Phi\) is bounded below gives a real number \(m\) with \(m\le\Phi(y)\) for all \(y\). Hence
\[
E(t)\ge(\alpha\beta+1)m.
\]
Using Cauchy–Schwarz and Young’s inequality again, the proof obtains the lower bound
\[
(\alpha\beta+1)m+\frac{\epsilon\alpha}{4}\|u(t)\|^2\le h(t)
\qquad(t\ge0).
\]
So \(h\) is nonincreasing and bounded below. Defining \(q(t)=h(\max(t,0))\), the function \(q\) is antitone on all of \(\mathbb R\) and bounded below, so it has a limit at \(+\infty\). Therefore \(h(t)\) has a finite limit, say \(l_h\).

Since \(h(t)\le h(0)\) and the lower bound controls \(\|u(t)\|^2\), the curve \(u(t)=x(t)-z\) is bounded. Also \(r(t)\to0\) from the residual convergence. By Cauchy–Schwarz,
\[
\langle r(t),u(t)\rangle\to0.
\]
The identity
\[
h(t)-E(t)-\epsilon\langle r(t),u(t)\rangle
=\frac{\epsilon\alpha}{2}\|u(t)\|^2
\]
then shows that \(\|u(t)\|^2\) has a finite limit. Hence \(\|u(t)\|=\|x(t)-z\|\) has a finite limit. This proves the first conjunct of the theorem.

Next the proof shows that \(x\) is bounded on \(t\ge0\). Choose a minimizer \(z_0\). From the just-proved distance convergence, \(\|x(t)-z_0\|\) converges to some \(d_0\). Hence, for all sufficiently large \(t\),
\[
\|x(t)-z_0\|\le |d_0|+1.
\]
On a compact interval \([0,T_0]\), the continuous image of \(x\) is compact, hence bounded. Combining the compact part with the eventual triangle estimate
\[
\|x(t)\|\le \|x(t)-z_0\|+\|z_0\|
\]
shows that \(x\) is bounded on all of \([0,\infty)\).

Since \(x_g=x\) on \([0,\infty)\), the trajectory \(x_g\) is bounded. Applying the boundedness part of `din_forward_internal` gives
\[
\nabla\Phi(x(t))\to0.
\]

The proof then records the supporting hyperplane inequality for convex differentiable functions. The cited theorem `convex_supporting_baillon_haddad` says that if \(f:H\to\mathbb R\) is convex on all of \(H\) and has gradient \(\nabla f\), then for all \(y,p\in H\),
\[
f(y)+\langle \nabla f(y),p-y\rangle\le f(p).
\]
Applied to \(\Phi\), this gives
\[
\Phi(y)+\langle \nabla\Phi(y),p-y\rangle\le\Phi(p)
\]
for all \(y,p\in H\).

A small closure lemma is proved: if \(a_n\to0\) strongly and \(b_n\) is bounded, then
\[
\langle a_n,b_n\rangle\to0.
\]
This follows from Cauchy–Schwarz, \(| \langle a_n,b_n\rangle|\le \|a_n\|\,\|b_n\|\), and the squeeze theorem.

These tools are used to prove that every weak cluster point is a minimizer. Let \(s_n\to\infty\) be a sequence of times and suppose
\[
x(s_n)\rightharpoonup z
\]
weakly. The range of the sequence \(x(s_n)\) is bounded by `bounded_range_of_tendsto_weakly`, because weakly convergent sequences in a Hilbert space are bounded. Since \(\nabla\Phi(x(t))\to0\), also
\[
\nabla\Phi(x(s_n))\to0.
\]
Therefore
\[
\langle \nabla\Phi(x(s_n)),x(s_n)\rangle\to0
\]
and, for each fixed \(p\),
\[
\langle \nabla\Phi(x(s_n)),p\rangle\to0.
\]
Applying the supporting inequality with \(y=x(s_n)\) gives
\[
\Phi(x(s_n))+\langle \nabla\Phi(x(s_n)),p-x(s_n)\rangle\le\Phi(p).
\]
Letting \(n\to\infty\), and using \(\Phi(x(s_n))\to l\), yields
\[
l\le\Phi(p)
\]
for every \(p\in H\). Thus \(l\) is a global lower bound for \(\Phi\).

To show that \(z\) is itself a minimizer, the proof uses weak lower semicontinuity. It defines \(f(y)=(\Phi(y):\mathbb R_{\pm\infty})\). Since \(\Phi\) is continuous and convex, \(f\) is lower semicontinuous in the norm topology. It is also quasiconvex: by `quasiconvexOn_univ_iff_convex_lowerLevelSet`, quasiconvexity on all of \(H\) is equivalent to convexity of every lower level set
\[
\{y\mid f(y)\le \xi\}.
\]
Using `mem_lowerLevelSet_iff`, membership in this set is equivalent to \(\Phi(y)\le\xi\). Since \(\Phi\) is convex, the set \(\{y\mid \Phi(y)\le\xi\}\) is convex. Hence \(f\) is quasiconvex. The cited result `weaklyLowerSemicontinuous_of_quasiconvexOn_univ` then gives that \(f\), transported to the weak topology, is weakly lower semicontinuous.

Because \(x(s_n)\rightharpoonup z\) weakly and \(f(x(s_n))\to l\), weak lower semicontinuity gives
\[
f(z)\le \liminf_n f(x(s_n))=l.
\]
Thus \(\Phi(z)\le l\). Together with \(l\le\Phi(z)\), this gives \(\Phi(z)=l\). Since \(l\le\Phi(p)\) for every \(p\), it follows that
\[
\Phi(z)\le\Phi(p)
\]
for every \(p\). Therefore \(z\in\operatorname{argminSet}\Phi\). This proves the hypothesis needed for Opial’s theorem.

Finally, the proof applies `opial_continuous_time`. That theorem states that if \(x:\mathbb R\to H\), \(S\subseteq H\) is nonempty, every sequence of weak cluster points of \(x\) along times tending to \(+\infty\) lies in \(S\), and for every \(z\in S\) the distance \(\|x(t)-z\|\) converges, then there exists \(z\in S\) such that \(x(t)\) converges weakly to \(z\). Here \(S=\operatorname{argminSet}\Phi\), nonemptiness is `hmin`, the cluster-point condition is `hcluster`, and the distance-convergence condition is `hdist`. The conclusion gives some \(z\in\operatorname{argminSet}\Phi\) with \(x(t)\rightharpoonup z\). Together with the already-proved distance convergence for every minimizer, this proves the stated conjunction.

Throughout the proof, Lean tactics play concrete mathematical roles. Commands such as `intro` introduce the variables and hypotheses of a subgoal; `obtain` and `rcases` destruct existential or conjunctive hypotheses; `rw` rewrites using definitions such as the ODE, the definitions of \(E,h,u,r\), or algebraic identities; `simp` and `simpa` perform definitional and algebraic simplification; `exact` closes a goal by supplying a theorem or previously proved fact; `apply` reduces a goal to the hypotheses of a lemma; `linarith` and `nlinarith` solve linear and nonlinear arithmetic inequalities; `positivity` proves nonnegativity of expressions; `field_simp` clears denominators; `ring` and `ring_nf` normalize polynomial and rational identities; `module` solves linear equalities in the vector space; `convert` changes a goal to an equivalent form; and `filter_upwards` handles “for all sufficiently large \(t\)” statements. The limit arguments use `tendsto_atTop_ciInf` for the limit of an antitone bounded-below function, `squeeze_zero` and `squeeze_zero_norm'` for limits forced between bounds, and `isBounded_iff_forall_norm_le` for converting boundedness into a uniform norm bound.

