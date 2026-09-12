## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_8.lean`

## Lean statement
```lean
theorem constrained_din_weakly_converges_to_argmin {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (Φ : H → ℝ)
  (hC : ConstrainedHypothesis C Φ)
  (β a b : ℝ) (hβ : 0 < β) (ha : a ≠ 0) (hb : 0 < b) (hab : 0 < b + a)
  (x₀ y₀ : H) (x y : ℝ → H)
  (hxy : IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y)
  (hreg : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
  (hconvex : ConvexOn ℝ C Φ)
    (hmin : (Optimization.argminSet Φ ∩ C).Nonempty) :
    ∃ z, z ∈ C ∧ (z ∈ Optimization.argminSet Φ) ∧
      Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The theorem `constrained_din_weakly_converges_to_argmin` is stated for a complete real inner product space \(H\), a set \(C\subseteq H\), and a function \(\Phi:H\to\mathbb R\). The hypothesis `hC : ConstrainedHypothesis C Φ` supplies, as used in the proof, that \(C\) is nonempty, closed, and convex, that \(\Phi\) is continuously differentiable on some open neighborhood of \(C\), and that \(\Phi\) is bounded below on \(C\). The parameters satisfy \(\beta>0\), \(a\ne0\), \(b>0\), and \(b+a>0\). The hypothesis `hconvex : ConvexOn ℝ C Φ` says that \(C\) is convex and that \(\Phi\) is convex on \(C\); in particular, the restriction of \(\Phi\) to every segment inside \(C\) is convex. The hypothesis `hmin` says that \(\operatorname{argminSet}\Phi\cap C\ne\varnothing\), where by definition
\[
\operatorname{argminSet}\Phi=\{x\mid \forall y,\ \Phi(x)\le \Phi(y)\}.
\]
Thus there is at least one global minimizer of \(\Phi\) lying in \(C\).

The data \(x_0,y_0\in H\) and \(x,y:\mathbb R\to H\) satisfy `IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y`. The parts of this predicate used below are that \(x_0\in C\) and that, for \(t\ge0\),
\[
\dot x(t)+x(t)=P_C\bigl(x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t)\bigr),
\qquad
\dot y(t)+a x(t)+b y(t)=0,
\]
where \(P_C\) is the constrained projection associated with \(C\) and \(\Phi\). The regularity hypothesis `hreg` says that \(x\) is \(C^1\) on \([0,\infty)\) and \(y\) is \(C^2\) on \([0,\infty)\).

The conclusion is that there exists \(z\in H\) such that
\[
z\in C,\qquad z\in\operatorname{argminSet}\Phi,
\]
and
\[
x(t)\rightharpoonup z \quad\text{weakly as }t\to\infty,
\]
formally,
\[
\operatorname{Tendsto}\bigl(t\mapsto \operatorname{toWeakSpace}_{\mathbb R,H}(x(t))\bigr)\ \operatorname{atTop}\ \bigl(\operatorname{nhds}(\operatorname{toWeakSpace}_{\mathbb R,H}(z))\bigr).
\]
So the trajectory \(x\) converges weakly to some global minimizer of \(\Phi\) that lies in \(C\).

## Lean proof
```lean
by
  classical
  have hx₀C : x₀ ∈ C := hxy.2.2.2.2.2.1
  obtain ⟨xg, yg, hsolg, hregxg, hregyg, hviable, huniq⟩ :=
    constrained_din_global_properties_part_i C Φ hC β a b hβ ha hb hab x₀ y₀ hx₀C
  have hxy_eq : Set.EqOn x xg (Set.Ici 0) ∧ Set.EqOn y yg (Set.Ici 0) :=
    huniq x y hxy hreg
  have hxC : ∀ t, 0 ≤ t → x t ∈ C := by
    intro t ht
    rw [hxy_eq.1 ht]
    exact hviable t ht
  have hglobal := constrained_din_global_properties_part_ii C Φ hC β a b hβ ha hb hab x₀ y₀ x y hxy hreg
  have hphi : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) := hglobal.2.2.2.1
  have hydot : Tendsto (deriv y) atTop (nhds 0) := hglobal.2.2.2.2
  obtain ⟨z₀, hz₀global, hz₀C⟩ := hmin
  rcases hC.continuously_differentiable_on_neighborhood with ⟨U, hUopen, hCU, hΦU⟩
  have hgrad : ∀ q : H, q ∈ C → HasGradientAt Φ (gradient Φ q) q := by
    intro q hq
    have hdiffWithin := hΦU.differentiableOn (by norm_num) q (hCU hq)
    have hdiff : DifferentiableAt ℝ Φ q :=
      hdiffWithin.differentiableAt (hUopen.mem_nhds (hCU hq))
    exact hdiff.hasGradientAt
  have hdx : ∀ t : ℝ, 0 < t → HasDerivAt x (deriv x t) t := by
    intro t ht
    exact (hreg.1.differentiableOn (by norm_num) t ht.le
      |>.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
  have hdy : ∀ t : ℝ, 0 < t → HasDerivAt y (deriv y t) t := by
    intro t ht
    exact (hreg.2.differentiableOn (by norm_num) t ht.le
      |>.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
  let Y : ℝ → H × H := fun t => (x t, y t)
  have hE0 : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => constrainedEnergy Φ a b (β * (a + 2 * b)) (x s) (y s))
        (β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (deriv x t) -
          a * inner ℝ (deriv x t) (deriv y t) - b * ‖deriv y t‖ ^ 2) t ∧
      (β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (deriv x t) -
          a * inner ℝ (deriv x t) (deriv y t) - b * ‖deriv y t‖ ^ 2) +
        (a + b) * ‖deriv x t‖ ^ 2 + b * ‖deriv x t - deriv y t‖ ^ 2 ≤ 0 := by
    intro t ht
    have hpair : HasDerivAt Y (deriv x t, deriv y t) t :=
      (hdx t ht).prodMk (hdy t ht)
    have hPx : constrainedDINProjection C Φ hC (x t) = x t :=
      constrainedDINProjection_eq_self C Φ hC (hxC t ht.le)
    have heq := hxy.2.2.2.2.2.2.2 t ht.le
    have hxvel : deriv x t = constrainedDINProjection C Φ hC
        (x t - β • gradient Φ (x t) - a • x t - b • y t) - x t := by
      apply eq_sub_of_add_eq
      simpa [constrainedDINProjection] using sub_eq_zero.mp heq.1
    have hyvel : deriv y t = -(a • x t + b • y t) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using heq.2)
    have hfield : constrainedDINPhaseField C Φ hC β a b (Y t) =
        (deriv x t, deriv y t) := by
      apply Prod.ext
      · change constrainedDINProjection C Φ hC
          (x t - β • gradient Φ (constrainedDINProjection C Φ hC (x t)) -
            a • x t - b • y t) - x t = deriv x t
        rw [hPx]
        exact hxvel.symm
      · change -(a • x t) - b • y t = deriv y t
        calc
          -(a • x t) - b • y t = -(a • x t + b • y t) := by
            simpa [sub_eq_add_neg] using (neg_add (a • x t) (b • y t)).symm
          _ = deriv y t := hyvel.symm
    have hY : HasDerivAt Y (constrainedDINPhaseField C Φ hC β a b (Y t)) t := by
      rw [hfield]
      exact hpair
    have h := constrainedDIN_energy_dissipation_at C Φ hC β a b hβ hb hab Y hY (hxC t ht.le)
    simpa [Y, constrainedEnergy, hfield] using h
  have hc : 0 < a + b := by linarith
  have hκ : 0 < β * (a + 2 * b) := by
    exact mul_pos hβ (by linarith)
  have hsqrtb : (Real.sqrt b) ^ 2 = b := by
    exact Real.sq_sqrt (le_of_lt hb)
  have hsqrta : (Real.sqrt (b + a)) ^ 2 = b + a := by
    exact Real.sq_sqrt (by linarith)
  have hκlo : β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤
      β * (a + 2 * b) := by
    have hprod : 0 ≤ Real.sqrt b * Real.sqrt (b + a) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hκhi : β * (a + 2 * b) ≤
      β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2 := by
    have hprod : 0 ≤ Real.sqrt b * Real.sqrt (b + a) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  obtain ⟨lE, hEanti, hEbelow, hElim⟩ := hglobal.1 (β * (a + 2 * b)) hκlo hκhi
  let q : ℝ → H := fun t => a • x t + b • y t
  let u : ℝ → H := fun t => x t - z₀
  let v : ℝ → H := deriv x
  let w : ℝ → H := deriv y
  have hqv : ∀ t, 0 < t → q t = -w t := by
    intro t ht
    have heq := hxy.2.2.2.2.2.2.2 t ht.le
    apply eq_neg_iff_add_eq_zero.mpr
    dsimp [q, w]
    simpa [add_comm, add_left_comm, add_assoc] using heq.2
  have hsupport_local : ∀ p, p ∈ C → ∀ r, r ∈ C →
      Φ p + inner ℝ (gradient Φ p) (r - p) ≤ Φ r := by
    intro p hp r hr
    let g : ℝ →ᵃ[ℝ] H := AffineMap.lineMap p r
    let φ : ℝ → ℝ := Φ ∘ g
    have hmaps : Set.MapsTo g (Set.Icc (0 : ℝ) 1) C := by
      rw [Set.mapsTo_iff_image_subset]
      simpa only [g, ← segment_eq_image_lineMap] using
        hconvex.1.segment_subset hp hr
    have hφconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
      exact (hconvex.comp_affineMap g).subset hmaps (convex_Icc 0 1)
    have hg : HasDerivAt g (r - p) 0 := by
      simpa [g] using
        (AffineMap.hasDerivAt_lineMap (a := p) (b := r) (x := (0 : ℝ)))
    have houter : HasFDerivAt Φ (InnerProductSpace.toDual ℝ H (gradient Φ p)) (g 0) := by
      simpa [g] using (hgrad p hp).hasFDerivAt
    have hφ' : HasDerivAt φ (inner ℝ (gradient Φ p) (r - p)) 0 := by
      simpa [φ, Function.comp_def, g, AffineMap.lineMap_apply,
        InnerProductSpace.toDual_apply_apply] using
        (houter.comp 0 hg).hasDerivAt
    have hs := hφconv.le_slope_of_hasDerivAt
      (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
      (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) zero_lt_one hφ'
    have hs' : inner ℝ (gradient Φ p) (r - p) ≤ Φ r - Φ p := by
      simpa [φ, g, slope, Function.comp_def, AffineMap.lineMap_apply] using hs
    linarith
  have hsupport : ∀ t, 0 < t →
      Φ (x t) + inner ℝ (gradient Φ (x t)) (z₀ - x t) ≤ Φ z₀ := by
    intro t ht
    exact hsupport_local (x t) (hxC t ht.le) z₀ hz₀C
  have hchar : ∀ t, 0 < t →
      inner ℝ (z₀ - (x t + v t))
        (x t - β • gradient Φ (x t) - a • x t - b • y t - (x t + v t)) ≤ 0 := by
    intro t ht
    let P := constrainedDINProjection C Φ hC
    have hp : P (x t - β • gradient Φ (x t) - a • x t - b • y t) = x t + v t := by
      have heq := hxy.2.2.2.2.2.2.2 t ht.le
      have heq' := sub_eq_zero.mp heq.1
      calc
        P (x t - β • gradient Φ (x t) - a • x t - b • y t) = deriv x t + x t := by
          simpa [P, constrainedDINProjection] using heq'.symm
        _ = x t + v t := by dsimp [v]; module
    have hpchar :=
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC.nonempty hC.closed hC.convex).mp
        (show x t + v t = constrainedDINProjection C Φ hC
          (x t - β • gradient Φ (x t) - a • x t - b • y t) from hp.symm)
    have := hpchar.2 z₀ hz₀C
    simpa [P] using this
  have hineq : ∀ t, 0 < t →
      inner ℝ (z₀ - x t) (w t - v t) +
          β * inner ℝ (v t) (gradient Φ (x t)) ≤
        β * inner ℝ (z₀ - x t) (gradient Φ (x t)) +
          inner ℝ (v t) (w t) - ‖v t‖ ^ 2 := by
    intro t ht
    have hh := hchar t ht
    have hform : x t - β • gradient Φ (x t) - a • x t - b • y t -
          (x t + v t) = w t - v t - β • gradient Φ (x t) := by
      have hq := hqv t ht
      dsimp [q] at hq
      calc
        x t - β • gradient Φ (x t) - a • x t - b • y t - (x t + v t) =
            x t - β • gradient Φ (x t) - (a • x t + b • y t) -
              (x t + v t) := by module
        _ = w t - v t - β • gradient Φ (x t) := by rw [hq]; module
    rw [hform] at hh
    simp only [inner_sub_left, inner_sub_right, inner_add_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at hh ⊢
    ring_nf at hh ⊢
    nlinarith
  let F : ℝ → ℝ := fun t =>
    inner ℝ (z₀ - x t) (q t) + ((a + b) / 2) * ‖z₀ - x t‖ ^ 2 +
      b * β * Φ (x t)
  have hF_at : ∀ t, 0 < t →
      HasDerivAt F
        (b * (inner ℝ (z₀ - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t))) + inner ℝ (v t) (w t)) t := by
    intro t ht
    have hxt := hdx t ht
    have hyt := hdy t ht
    have hqt : HasDerivAt q (a • v t + b • w t) t := by
      simpa [q, v, w] using (hxt.const_smul a).add (hyt.const_smul b)
    have hdt : HasDerivAt (fun s => z₀ - x s) (-v t) t := by
      convert (hxt.sub_const z₀).neg using 1
      ext s
      simp [sub_eq_add_neg]
    have hpt : HasDerivAt (fun s => Φ (x s))
        (inner ℝ (gradient Φ (x t)) (v t)) t := by
      simpa [v] using
        ((hgrad (x t) (hxC t ht.le)).hasFDerivAt.comp t hxt.hasFDerivAt).hasDerivAt
    have h1 := hdt.inner ℝ hqt
    have h2 := (hdt.norm_sq.const_mul ((a + b) / 2))
    have h3 := (hpt.const_mul (b * β))
    have hs := (h1.add h2).add h3
    change HasDerivAt (fun s =>
      inner ℝ (z₀ - x s) (q s) + ((a + b) / 2) * ‖z₀ - x s‖ ^ 2 +
        b * β * Φ (x s)) _ t at hs
    convert hs using 1
    rw [hqv t ht]
    simp only [inner_neg_left, inner_neg_right, inner_add_right, real_inner_smul_right]
    rw [inner_sub_right]
    rw [real_inner_comm (gradient Φ (x t)) (v t)]
    ring_nf
  have hFbound : ∀ t, 0 < t →
      deriv F t ≤ ((b + 3) / 2) * ‖v t‖ ^ 2 + ((b + 1) / 2) * ‖w t - v t‖ ^ 2 := by
    intro t ht
    rw [(hF_at t ht).deriv]
    have hg0 : inner ℝ (gradient Φ (x t)) (z₀ - x t) ≤ 0 := by
      have hmin' := hz₀global (x t)
      have hs := hsupport t ht
      linarith
    have hcross := real_inner_le_norm (v t) (w t - v t)
    have hyoung : 2 * inner ℝ (v t) (w t - v t) ≤
        ‖v t‖ ^ 2 + ‖w t - v t‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v t‖ - ‖w t - v t‖)]
    have hvw : inner ℝ (v t) (w t) =
        inner ℝ (v t) (w t - v t) + ‖v t‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    have hrev : ‖v t - w t‖ ^ 2 = ‖w t - v t‖ ^ 2 := by
      rw [norm_sub_rev]
    rw [hvw]
    have hi := hineq t ht
    have hgd : β * inner ℝ (z₀ - x t) (gradient Φ (x t)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hβ.le
      simpa [real_inner_comm] using hg0
    nlinarith
  let ε : ℝ := min ((a + b) / (2 * (b + 3))) (b / (2 * (b + 1)))
  have hε : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · positivity
    · positivity
  have hεc : ε * (b + 3) ≤ a + b := by
    have h := min_le_left ((a + b) / (2 * (b + 3))) (b / (2 * (b + 1)))
    dsimp [ε]
    calc
      min ((a + b) / (2 * (b + 3))) (b / (2 * (b + 1))) * (b + 3) ≤
          ((a + b) / (2 * (b + 3))) * (b + 3) :=
        mul_le_mul_of_nonneg_right h (by linarith)
      _ = (a + b) / 2 := by field_simp
      _ ≤ a + b := by linarith
  have hεb : ε * (b + 1) ≤ b := by
    have h := min_le_right ((a + b) / (2 * (b + 3))) (b / (2 * (b + 1)))
    dsimp [ε]
    calc
      min ((a + b) / (2 * (b + 3))) (b / (2 * (b + 1))) * (b + 1) ≤
          (b / (2 * (b + 1))) * (b + 1) :=
        mul_le_mul_of_nonneg_right h (by linarith)
      _ = b / 2 := by field_simp
      _ ≤ b := by linarith
  let A : ℝ → ℝ := fun t => constrainedEnergy Φ a b (β * (a + 2 * b)) (x t) (y t)
  let Haux : ℝ → ℝ := fun t => A t + ε * F t
  have hA_at : ∀ t, 0 < t → HasDerivAt A
      (β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (v t) -
        a * inner ℝ (v t) (w t) - b * ‖w t‖ ^ 2) t := by
    intro t ht
    simpa [A, v, w] using (hE0 t ht).1
  have hH_at : ∀ t, 0 < t → HasDerivAt Haux
      ((β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (v t) -
        a * inner ℝ (v t) (w t) - b * ‖w t‖ ^ 2) +
        ε * (b * (inner ℝ (z₀ - x t) (w t - v t) +
          β * inner ℝ (v t) (gradient Φ (x t))) + inner ℝ (v t) (w t))) t := by
    intro t ht
    simpa [Haux] using (hA_at t ht).add ((hF_at t ht).const_mul ε)
  have hH_deriv_nonpos : ∀ t, 0 < t → deriv Haux t ≤ 0 := by
    intro t ht
    rw [(hH_at t ht).deriv]
    have hA : β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (v t) -
        a * inner ℝ (v t) (w t) - b * ‖w t‖ ^ 2 +
        (a + b) * ‖v t‖ ^ 2 + b * ‖w t - v t‖ ^ 2 ≤ 0 := by
      simpa [v, w, norm_sub_rev] using (hE0 t ht).2
    have hF := hFbound t ht
    rw [(hF_at t ht).deriv] at hF
    have hFscaled := mul_le_mul_of_nonneg_left hF hε.le
    have hcross := real_inner_le_norm (v t) (w t - v t)
    have hyoung : 2 * inner ℝ (v t) (w t - v t) ≤
        ‖v t‖ ^ 2 + ‖w t - v t‖ ^ 2 := by
      nlinarith [sq_nonneg (‖v t‖ - ‖w t - v t‖)]
    have hvw : inner ℝ (v t) (w t) =
        inner ℝ (v t) (w t - v t) + ‖v t‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    rw [hvw] at hA ⊢
    nlinarith [hFscaled]
  have hΦcont : ContinuousOn (fun t => Φ (x t)) (Set.Ici (0 : ℝ)) := by
    apply hΦU.continuousOn.comp hreg.1.continuousOn
    intro t ht
    exact hCU (hxC t ht)
  have hqcont : ContinuousOn q (Set.Ici (0 : ℝ)) := by
    simpa [q] using (hreg.1.continuousOn.const_smul a).add
      (hreg.2.continuousOn.const_smul b)
  have hdcont : ContinuousOn (fun t => z₀ - x t) (Set.Ici (0 : ℝ)) := by
    simpa using continuousOn_const.sub hreg.1.continuousOn
  have hFcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    simpa [F] using
      ((hdcont.inner hqcont).add
        ((hdcont.norm.pow 2).const_mul ((a + b) / 2))).add
        (hΦcont.const_mul (b * β))
  have hAcont : ContinuousOn A (Set.Ici (0 : ℝ)) := by
    simpa [A, constrainedEnergy, q] using
      (hΦcont.const_mul (β * (a + 2 * b))).add
        ((hqcont.norm.pow 2).const_mul (1 / 2 : ℝ))
  have hHcont : ContinuousOn Haux (Set.Ici (0 : ℝ)) :=
    hAcont.add (hFcont.const_mul ε)
  have hHdiff : DifferentiableOn ℝ Haux (interior (Set.Ici (0 : ℝ))) := by
    intro t ht
    have ht' : 0 < t := by simpa [interior_Ici] using ht
    exact (hH_at t ht').differentiableAt.differentiableWithinAt
  have hHanti : AntitoneOn Haux (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hHcont hHdiff
      (fun t ht => hH_deriv_nonpos t (by simpa [interior_Ici] using ht))
  obtain ⟨m, hm⟩ := hC.bounded_below
  let Kcoef : ℝ := β * (a + 2 * b) + ε * b * β
  have hKcoef : 0 < Kcoef := by
    dsimp [Kcoef]
    positivity
  have hεcpos : 0 < (a + b) - ε := by
    have hle : ε ≤ (a + b) / (2 * (b + 3)) := min_le_left _ _
    have hfrac : (a + b) / (2 * (b + 3)) < a + b := by
      have : 0 < 2 * (b + 3) := by positivity
      apply (div_lt_iff₀ this).2
      nlinarith [hc]
    have : ε < a + b := lt_of_le_of_lt hle hfrac
    linarith
  have hHlower : ∀ t, 0 ≤ t →
      Kcoef * m + ε * ((a + b) - ε) / 4 * ‖z₀ - x t‖ ^ 2 ≤ Haux t := by
    intro t ht
    have hΦm := hm (x t) (hxC t ht)
    have hinner := real_inner_le_norm (-(z₀ - x t)) (q t)
    rw [inner_neg_left, norm_neg] at hinner
    have hsq := sq_nonneg (‖q t‖ - ε * ‖z₀ - x t‖)
    have hcoef : 0 ≤ ε * ((a + b) - ε) / 4 := by positivity
    dsimp [Haux, A, F, Kcoef, constrainedEnergy]
    nlinarith [mul_le_mul_of_nonneg_left hΦm hKcoef.le,
      mul_nonneg hcoef (sq_nonneg ‖z₀ - x t‖)]
  have hHupper : ∀ t, 0 ≤ t → Haux t ≤ Haux 0 := by
    intro t ht
    exact hHanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hden : 0 < ε * ((a + b) - ε) := mul_pos hε hεcpos
  let Q : ℝ := 4 * (Haux 0 - Kcoef * m) / (ε * ((a + b) - ε))
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    have h0 := hHlower 0 le_rfl
    have hnon : 0 ≤ ε * ((a + b) - ε) / 4 * ‖z₀ - x 0‖ ^ 2 := by positivity
    apply div_nonneg
    · nlinarith
    · positivity
  have hQbound : ∀ t, 0 ≤ t → ‖z₀ - x t‖ ^ 2 ≤ Q := by
    intro t ht
    have hl := hHlower t ht
    have hu := hHupper t ht
    dsimp [Q]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hdist_bounded : ∃ R : ℝ, ∀ t, 0 ≤ t → ‖z₀ - x t‖ ≤ R := by
    refine ⟨Real.sqrt Q, ?_⟩
    intro t ht
    have hsq := hQbound t ht
    have hsqrt : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
    nlinarith [Real.sqrt_nonneg Q, norm_nonneg (z₀ - x t)]
  have hHlim : ∃ l : ℝ, Tendsto Haux atTop (nhds l) := by
    let G : ℝ → ℝ := fun t => Haux (max t 0)
    have hGanti : Antitone G := by
      intro s t hst
      exact hHanti (le_max_right s 0) (le_max_right t 0)
        (max_le_max_right 0 hst)
    have hGlow : BddBelow (Set.range G) := by
      refine ⟨Kcoef * m, ?_⟩
      rintro y ⟨t, rfl⟩
      have hterm : 0 ≤ ε * ((a + b) - ε) / 4 * ‖z₀ - x (max t 0)‖ ^ 2 := by positivity
      exact (le_add_of_nonneg_right hterm).trans
        (by simpa [G] using hHlower (max t 0) (le_max_right _ _))
    refine ⟨⨅ t, G t, ?_⟩
    apply (tendsto_atTop_ciInf hGanti hGlow).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [G, max_eq_left ht]
  have hq_lim : Tendsto q atTop (nhds 0) := by
    have hneg : Tendsto (fun t => -w t) atTop (nhds 0) := by simpa using hydot.neg
    apply hneg.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hqv t ht]
  have hcross_lim : Tendsto (fun t => inner ℝ (z₀ - x t) (q t)) atTop (nhds 0) := by
    rcases hdist_bounded with ⟨R, hR⟩
    have hbound : ∀ᶠ t in atTop,
        ‖inner ℝ (z₀ - x t) (q t)‖ ≤ R * ‖q t‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm (z₀ - x t) (q t)).trans
        (mul_le_mul_of_nonneg_right (hR t ht) (norm_nonneg _))
    have hmajor : Tendsto (fun t => R * ‖q t‖) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hq_lim.norm
    exact squeeze_zero_norm' hbound hmajor
  have hdist_sq_lim : ∃ L : ℝ,
      Tendsto (fun t => ‖z₀ - x t‖ ^ 2) atTop (nhds L) := by
    rcases hHlim with ⟨lH, hlH⟩
    rcases hphi with ⟨lΦ, hlΦ⟩
    have hscaled :=
      (((hlH.sub hElim).sub (hcross_lim.const_mul ε)).sub
        (hlΦ.const_mul (ε * b * β))).const_mul
          (2 / (ε * (a + b)))
    refine ⟨(2 / (ε * (a + b))) *
        (lH - lE - ε * 0 - ε * b * β * lΦ), ?_⟩
    convert hscaled using 1
    funext t
    dsimp [Haux, A, F, constrainedEnergy]
    field_simp [ne_of_gt (mul_pos hε (by linarith : 0 < a + b))]
    ring
  have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    rcases hdist_bounded with ⟨R, hR⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R + ‖z₀‖, ?_⟩
    rintro q ⟨t, ht, rfl⟩
    calc
      ‖x t‖ = ‖(x t - z₀) + z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x t - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ = ‖z₀ - x t‖ + ‖z₀‖ := by rw [norm_sub_rev]
      _ ≤ R + ‖z₀‖ := by
        simpa [add_comm] using add_le_add_right (hR t ht) ‖z₀‖
  obtain ⟨hgrad_bounded, hy_bounded, hv_bounded, hv_lim⟩ :=
    constrained_din_global_properties_part_iii C Φ hC β a b hβ ha hb hab x₀ y₀ x y hxy hreg
      hx_bounded
  rcases isBounded_iff_forall_norm_le.mp hgrad_bounded with ⟨Rg, hRg⟩
  rcases isBounded_iff_forall_norm_le.mp hv_bounded with ⟨Rv, hRv⟩
  have hinner_vg_lim : Tendsto
      (fun t => inner ℝ (v t) (gradient Φ (x t))) atTop (nhds 0) := by
    have hbound : ∀ᶠ t in atTop,
        ‖inner ℝ (v t) (gradient Φ (x t))‖ ≤ Rg * ‖v t‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm (v t) (gradient Φ (x t))).trans
        (by
          have h := mul_le_mul_of_nonneg_left (hRg _ ⟨t, ht, rfl⟩)
            (norm_nonneg (v t))
          simpa [mul_comm] using h)
    have hmajor : Tendsto (fun t => Rg * ‖v t‖) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hv_lim.norm
    exact squeeze_zero_norm' hbound hmajor
  have hinner_vw_lim : Tendsto (fun t => inner ℝ (v t) (w t)) atTop (nhds 0) := by
    have hbound : ∀ᶠ t in atTop,
        ‖inner ℝ (v t) (w t)‖ ≤ Rv * ‖w t‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm (v t) (w t)).trans
        (by
          have h := mul_le_mul_of_nonneg_left (hRv _ ⟨t, Set.mem_Ici.mpr ht, rfl⟩)
            (norm_nonneg (w t))
          simpa [mul_comm] using h)
    have hmajor : Tendsto (fun t => Rv * ‖w t‖) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hydot.norm
    exact squeeze_zero_norm' hbound hmajor
  have hinner_dw_lim : Tendsto
      (fun t => inner ℝ (z₀ - x t) (w t - v t)) atTop (nhds 0) := by
    rcases hdist_bounded with ⟨R, hR⟩
    have hdiff_lim : Tendsto (fun t => w t - v t) atTop (nhds 0) := by
      simpa using hydot.sub hv_lim
    have hbound : ∀ᶠ t in atTop,
        ‖inner ℝ (z₀ - x t) (w t - v t)‖ ≤ R * ‖w t - v t‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm (z₀ - x t) (w t - v t)).trans
        (mul_le_mul_of_nonneg_right (hR t ht) (norm_nonneg _))
    have hmajor : Tendsto (fun t => R * ‖w t - v t‖) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hdiff_lim.norm
    exact squeeze_zero_norm' hbound hmajor
  obtain ⟨lΦ, hlΦ⟩ := hphi
  have hΦz₀_ge : Φ z₀ ≥ lΦ := by
    have hineq_lower : ∀ t, 0 < t →
        Φ (x t) + (1 / β) *
          (inner ℝ (z₀ - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t)) -
            inner ℝ (v t) (w t) + ‖v t‖ ^ 2) ≤ Φ z₀ := by
      intro t ht
      have hs := hsupport t ht
      have hi := hineq t ht
      have hs' : Φ (x t) + inner ℝ (z₀ - x t) (gradient Φ (x t)) ≤ Φ z₀ := by
        simpa [real_inner_comm] using hs
      have hS : (1 / β) *
          (inner ℝ (z₀ - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t)) -
            inner ℝ (v t) (w t) + ‖v t‖ ^ 2) ≤
          inner ℝ (z₀ - x t) (gradient Φ (x t)) := by
        rw [one_div_mul_eq_div]
        apply (div_le_iff₀ hβ).2
        nlinarith [hi]
      linarith
    have hterm : Tendsto (fun t => (1 / β) *
          (inner ℝ (z₀ - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t)) -
            inner ℝ (v t) (w t) + ‖v t‖ ^ 2)) atTop (nhds 0) := by
      have hvn : Tendsto (fun t => ‖v t‖ ^ 2) atTop (nhds 0) := by simpa using hv_lim.norm.pow 2
      have hsum := hinner_dw_lim.add (hinner_vg_lim.const_mul β)
      have hsum := hsum.sub hinner_vw_lim
      have hsum := hsum.add hvn
      simpa [zero_mul, mul_zero] using hsum.const_mul (1 / β)
    have htotal : Tendsto (fun t => Φ (x t) + (1 / β) *
          (inner ℝ (z₀ - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t)) -
            inner ℝ (v t) (w t) + ‖v t‖ ^ 2)) atTop (nhds lΦ) := by
      simpa using hlΦ.add hterm
    refine le_of_tendsto htotal ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hineq_lower t ht
  have hdist : ∀ z, z ∈ Optimization.argminSet Φ ∩ C →
      ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d) := by
    intro z hz
    have hzglobal : z ∈ Optimization.argminSet Φ := hz.1
    have hzC : z ∈ C := hz.2
    have hsupport_z : ∀ t, 0 < t →
        Φ (x t) + inner ℝ (gradient Φ (x t)) (z - x t) ≤ Φ z := by
      intro t ht
      exact hsupport_local (x t) (hxC t ht.le) z hzC
    have hchar_z : ∀ t, 0 < t →
        inner ℝ (z - (x t + v t))
          (x t - β • gradient Φ (x t) - a • x t - b • y t - (x t + v t)) ≤ 0 := by
      intro t ht
      let P := constrainedDINProjection C Φ hC
      have hp : P (x t - β • gradient Φ (x t) - a • x t - b • y t) = x t + v t := by
        have heq := hxy.2.2.2.2.2.2.2 t ht.le
        have heq' := sub_eq_zero.mp heq.1
        calc
          P (x t - β • gradient Φ (x t) - a • x t - b • y t) = deriv x t + x t := by
            simpa [P, constrainedDINProjection] using heq'.symm
          _ = x t + v t := by dsimp [v]; module
      have hpchar :=
          (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC.nonempty hC.closed hC.convex).mp
          (show x t + v t = constrainedDINProjection C Φ hC
            (x t - β • gradient Φ (x t) - a • x t - b • y t) from hp.symm)
      have hh := hpchar.2 z hzC
      simpa [P] using hh
    have hineq_z : ∀ t, 0 < t →
        inner ℝ (z - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t)) ≤
          β * inner ℝ (z - x t) (gradient Φ (x t)) +
            inner ℝ (v t) (w t) - ‖v t‖ ^ 2 := by
      intro t ht
      have hh := hchar_z t ht
      have hform : x t - β • gradient Φ (x t) - a • x t - b • y t -
            (x t + v t) = w t - v t - β • gradient Φ (x t) := by
        have hq := hqv t ht
        dsimp [q] at hq
        calc
          x t - β • gradient Φ (x t) - a • x t - b • y t - (x t + v t) =
              x t - β • gradient Φ (x t) - (a • x t + b • y t) -
                (x t + v t) := by module
          _ = w t - v t - β • gradient Φ (x t) := by rw [hq]; module
      rw [hform] at hh
      simp only [inner_sub_left, inner_sub_right, inner_add_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq] at hh ⊢
      ring_nf at hh ⊢
      nlinarith
    let Fz : ℝ → ℝ := fun t =>
      inner ℝ (z - x t) (q t) + ((a + b) / 2) * ‖z - x t‖ ^ 2 +
        b * β * Φ (x t)
    have hFz_at : ∀ t, 0 < t →
        HasDerivAt Fz
          (b * (inner ℝ (z - x t) (w t - v t) +
              β * inner ℝ (v t) (gradient Φ (x t))) + inner ℝ (v t) (w t)) t := by
      intro t ht
      have hxt := hdx t ht
      have hyt := hdy t ht
      have hqt : HasDerivAt q (a • v t + b • w t) t := by
        simpa [q, v, w] using (hxt.const_smul a).add (hyt.const_smul b)
      have hdt : HasDerivAt (fun s => z - x s) (-v t) t := by
        convert (hxt.sub_const z).neg using 1
        ext s
        simp [sub_eq_add_neg]
      have hpt : HasDerivAt (fun s => Φ (x s))
          (inner ℝ (gradient Φ (x t)) (v t)) t := by
        simpa [v] using
          ((hgrad (x t) (hxC t ht.le)).hasFDerivAt.comp t hxt.hasFDerivAt).hasDerivAt
      have h1 := hdt.inner ℝ hqt
      have h2 := (hdt.norm_sq.const_mul ((a + b) / 2))
      have h3 := (hpt.const_mul (b * β))
      have hs := (h1.add h2).add h3
      change HasDerivAt (fun s =>
        inner ℝ (z - x s) (q s) + ((a + b) / 2) * ‖z - x s‖ ^ 2 +
          b * β * Φ (x s)) _ _
      convert hs using 1
      rw [hqv t ht]
      simp only [inner_neg_left, inner_neg_right, inner_add_right, real_inner_smul_right]
      rw [inner_sub_right]
      rw [real_inner_comm (gradient Φ (x t)) (v t)]
      ring_nf
    have hFzbound : ∀ t, 0 < t →
        deriv Fz t ≤ ((b + 3) / 2) * ‖v t‖ ^ 2 +
          ((b + 1) / 2) * ‖w t - v t‖ ^ 2 := by
      intro t ht
      rw [(hFz_at t ht).deriv]
      have hg0 : inner ℝ (gradient Φ (x t)) (z - x t) ≤ 0 := by
        have hmin' := hzglobal (x t)
        have hs := hsupport_z t ht
        linarith
      have hcross := real_inner_le_norm (v t) (w t - v t)
      have hyoung : 2 * inner ℝ (v t) (w t - v t) ≤
          ‖v t‖ ^ 2 + ‖w t - v t‖ ^ 2 := by
        nlinarith [sq_nonneg (‖v t‖ - ‖w t - v t‖)]
      have hvw : inner ℝ (v t) (w t) =
          inner ℝ (v t) (w t - v t) + ‖v t‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
        ring
      have hrev : ‖v t - w t‖ ^ 2 = ‖w t - v t‖ ^ 2 := by
        rw [norm_sub_rev]
      rw [hvw]
      have hi := hineq_z t ht
      have hgd : β * inner ℝ (z - x t) (gradient Φ (x t)) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos hβ.le
        simpa [real_inner_comm] using hg0
      nlinarith
    let Hauxz : ℝ → ℝ := fun t => A t + ε * Fz t
    have hHz_at : ∀ t, 0 < t → HasDerivAt Hauxz
        ((β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (v t) -
          a * inner ℝ (v t) (w t) - b * ‖w t‖ ^ 2) +
          ε * (b * (inner ℝ (z - x t) (w t - v t) +
            β * inner ℝ (v t) (gradient Φ (x t))) + inner ℝ (v t) (w t))) t := by
      intro t ht
      simpa [Hauxz] using (hA_at t ht).add ((hFz_at t ht).const_mul ε)
    have hHz_deriv_nonpos : ∀ t, 0 < t → deriv Hauxz t ≤ 0 := by
      intro t ht
      rw [(hHz_at t ht).deriv]
      have hA : β * (a + 2 * b) * inner ℝ (gradient Φ (x t)) (v t) -
          a * inner ℝ (v t) (w t) - b * ‖w t‖ ^ 2 +
          (a + b) * ‖v t‖ ^ 2 + b * ‖w t - v t‖ ^ 2 ≤ 0 := by
        simpa [v, w, norm_sub_rev] using (hE0 t ht).2
      have hF := hFzbound t ht
      rw [(hFz_at t ht).deriv] at hF
      have hFscaled := mul_le_mul_of_nonneg_left hF hε.le
      have hcross := real_inner_le_norm (v t) (w t - v t)
      have hyoung : 2 * inner ℝ (v t) (w t - v t) ≤
          ‖v t‖ ^ 2 + ‖w t - v t‖ ^ 2 := by
        nlinarith [sq_nonneg (‖v t‖ - ‖w t - v t‖)]
      have hvw : inner ℝ (v t) (w t) =
          inner ℝ (v t) (w t - v t) + ‖v t‖ ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
        ring
      rw [hvw] at hA ⊢
      nlinarith [hFscaled]
    have hdcont_z : ContinuousOn (fun t => z - x t) (Set.Ici (0 : ℝ)) := by
      simpa using continuousOn_const.sub hreg.1.continuousOn
    have hFzcont : ContinuousOn Fz (Set.Ici (0 : ℝ)) := by
      simpa [Fz] using
        ((hdcont_z.inner hqcont).add
          ((hdcont_z.norm.pow 2).const_mul ((a + b) / 2))).add
          (hΦcont.const_mul (b * β))
    have hHzcont : ContinuousOn Hauxz (Set.Ici (0 : ℝ)) :=
      hAcont.add (hFzcont.const_mul ε)
    have hHzdiff : DifferentiableOn ℝ Hauxz (interior (Set.Ici 0)) := by
      intro t ht
      have ht' : 0 < t := by simpa [interior_Ici] using ht
      exact (hHz_at t ht').differentiableAt.differentiableWithinAt
    have hHzanti : AntitoneOn Hauxz (Set.Ici (0 : ℝ)) :=
      antitoneOn_of_deriv_nonpos (convex_Ici 0) hHzcont hHzdiff
        (fun t ht => hHz_deriv_nonpos t (by simpa [interior_Ici] using ht))
    have hHzlower : ∀ t, 0 ≤ t →
        Kcoef * m + ε * ((a + b) - ε) / 4 * ‖z - x t‖ ^ 2 ≤ Hauxz t := by
      intro t ht
      have hΦm := hm (x t) (hxC t ht)
      have hinner := real_inner_le_norm (-(z - x t)) (q t)
      rw [inner_neg_left, norm_neg] at hinner
      have hsq := sq_nonneg (‖q t‖ - ε * ‖z - x t‖)
      have hcoef : 0 ≤ ε * ((a + b) - ε) / 4 := by positivity
      dsimp [Hauxz, A, Fz, Kcoef, constrainedEnergy]
      nlinarith [mul_le_mul_of_nonneg_left hΦm hKcoef.le,
        mul_nonneg hcoef (sq_nonneg ‖z - x t‖)]
    have hHzupper : ∀ t, 0 ≤ t → Hauxz t ≤ Hauxz 0 := by
      intro t ht
      exact hHzanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hHzden : 0 < ε * ((a + b) - ε) := hden
    let Qz : ℝ := 4 * (Hauxz 0 - Kcoef * m) / (ε * ((a + b) - ε))
    have hQz : 0 ≤ Qz := by
      dsimp [Qz]
      have h0 := hHzlower 0 le_rfl
      have hnon : 0 ≤ ε * ((a + b) - ε) / 4 * ‖z - x 0‖ ^ 2 := by positivity
      apply div_nonneg
      · nlinarith
      · positivity
    have hQzbound : ∀ t, 0 ≤ t → ‖z - x t‖ ^ 2 ≤ Qz := by
      intro t ht
      have hl := hHzlower t ht
      have hu := hHzupper t ht
      dsimp [Qz]
      apply (le_div_iff₀ hHzden).2
      nlinarith
    have hdist_bounded_z : ∃ R : ℝ, ∀ t, 0 ≤ t → ‖z - x t‖ ≤ R := by
      refine ⟨Real.sqrt Qz, ?_⟩
      intro t ht
      have hsq := hQzbound t ht
      have hsqrt : (Real.sqrt Qz) ^ 2 = Qz := Real.sq_sqrt hQz
      nlinarith [Real.sqrt_nonneg Qz, norm_nonneg (z - x t)]
    have hHzlim : ∃ l : ℝ, Tendsto Hauxz atTop (nhds l) := by
      let Gz : ℝ → ℝ := fun t => Hauxz (max t 0)
      have hGzanti : Antitone Gz := by
        intro s t hst
        exact hHzanti (le_max_right s 0) (le_max_right t 0)
          (max_le_max_right 0 hst)
      have hGzlow : BddBelow (Set.range Gz) := by
        refine ⟨Kcoef * m, ?_⟩
        rintro y ⟨t, rfl⟩
        have hterm : 0 ≤ ε * ((a + b) - ε) / 4 * ‖z - x (max t 0)‖ ^ 2 := by positivity
        exact (le_add_of_nonneg_right hterm).trans
          (by simpa [Gz] using hHzlower (max t 0) (le_max_right _ _))
      refine ⟨⨅ t, Gz t, ?_⟩
      apply (tendsto_atTop_ciInf hGzanti hGzlow).congr'
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      simp [Gz, max_eq_left ht]
    have hcross_z : Tendsto (fun t => inner ℝ (z - x t) (q t)) atTop (nhds 0) := by
      rcases hdist_bounded_z with ⟨R, hR⟩
      have hbound : ∀ᶠ t in atTop,
          ‖inner ℝ (z - x t) (q t)‖ ≤ R * ‖q t‖ := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm (z - x t) (q t)).trans
          (mul_le_mul_of_nonneg_right (hR t ht) (norm_nonneg _))
      have hmajor : Tendsto (fun t => R * ‖q t‖) atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul hq_lim.norm
      exact squeeze_zero_norm' hbound hmajor
    have hdist_sq_lim_z : ∃ L : ℝ,
        Tendsto (fun t => ‖z - x t‖ ^ 2) atTop (nhds L) := by
      rcases hHzlim with ⟨lHz, hlHz⟩
      have hscaled :=
        (((hlHz.sub hElim).sub (hcross_z.const_mul ε)).sub
          (hlΦ.const_mul (ε * b * β))).const_mul
            (2 / (ε * (a + b)))
      refine ⟨(2 / (ε * (a + b))) *
          (lHz - lE - ε * 0 - ε * b * β * lΦ), ?_⟩
      convert hscaled using 1
      funext t
      dsimp [Hauxz, A, Fz, constrainedEnergy]
      field_simp [ne_of_gt (mul_pos hε (by linarith : 0 < a + b))]
      ring
    rcases hdist_sq_lim_z with ⟨Lz, hLz⟩
    have hLz_nonneg : 0 ≤ Lz :=
      ge_of_tendsto hLz (Filter.Eventually.of_forall (fun t => sq_nonneg ‖z - x t‖))
    have hnorm_lim : Tendsto (fun t => ‖z - x t‖) atTop
        (nhds (Real.sqrt Lz)) := by
      have hs : Tendsto (fun y : ℝ => Real.sqrt y) (nhds Lz)
          (nhds (Real.sqrt Lz)) := Real.continuous_sqrt.continuousAt
      have hs := hs.comp hLz
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _), norm_sub_rev] using hs
    refine ⟨Real.sqrt Lz, ?_⟩
    simpa [norm_sub_rev] using hnorm_lim
  let S : Set H := Optimization.argminSet Φ ∩ C
  have hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ S := by
    intro s hs z hweak
    let s' : ℕ → ℝ := fun n => max (s n) 0
    have hs' : Tendsto s' atTop atTop := by
      apply Filter.tendsto_atTop_mono (fun n => le_max_left (s n) 0)
      exact hs
    have hweak' : Tendsto (fun n => toWeakSpace ℝ H (x (s' n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      apply hweak.congr'
      filter_upwards [Filter.tendsto_atTop.1 hs 0] with n hn
      simp [s', max_eq_left hn]
    have hxseqC : ∀ n, x (s' n) ∈ C := by
      intro n
      exact hxC (s' n) (le_max_right (s n) 0)
    have hzC : z ∈ C :=
      mem_of_tendsto_weakly_of_isClosed_convex hC.closed hC.convex hxseqC hweak'
    have hinner : Tendsto
        (fun n => inner ℝ (gradient Φ z) (x (s' n) - z)) atTop (nhds 0) := by
      have hinnerx : Tendsto (fun n => inner ℝ (x (s' n)) (gradient Φ z)) atTop
          (nhds (inner ℝ z (gradient Φ z))) := by
        exact ((weakSpace_continuous_inner_right (gradient Φ z)).tendsto
          (toWeakSpace ℝ H z)).comp hweak'
      have hdiff := hinnerx.sub (tendsto_const_nhds (x := inner ℝ z (gradient Φ z)))
      simpa [inner_sub_right, real_inner_comm] using hdiff
    have hz_le_l : Φ z ≤ lΦ := by
      have hsum : Tendsto
          (fun n => Φ z + inner ℝ (gradient Φ z) (x (s' n) - z)) atTop
            (nhds (Φ z)) := by
        simpa using (tendsto_const_nhds (x := Φ z)).add hinner
      have hphi_seq : Tendsto (fun n => Φ (x (s' n))) atTop (nhds lΦ) :=
        hlΦ.comp hs'
      have hle : ∀ n, Φ z + inner ℝ (gradient Φ z) (x (s' n) - z) ≤
          Φ (x (s' n)) := by
        intro n
        have hh := hsupport_local z hzC (x (s' n)) (hxseqC n)
        simpa [real_inner_comm] using hh
      exact le_of_tendsto_of_tendsto hsum hphi_seq
        (Filter.Eventually.of_forall hle)
    have hzglobal : z ∈ Optimization.argminSet Φ := by
      intro p
      have hz0p := hz₀global p
      linarith [hΦz₀_ge, hz_le_l]
    exact ⟨hzglobal, hzC⟩
  have hSnonempty : S.Nonempty := ⟨z₀, hz₀global, hz₀C⟩
  rcases Alvarez2002.opial_continuous_time x S hSnonempty hcluster hdist with
    ⟨z, hzS, hzweak⟩
  exact ⟨z, hzS.2, hzS.1, hzweak⟩
```

## Proof explanation
The proof begins with `classical`, allowing classical logic for the arguments that follow. From the constrained trajectory hypothesis it extracts
\[
x_0\in C
\]
using the component `hxy.2.2.2.2.2.1`. It then applies `constrained_din_global_properties_part_i` to \(C,\Phi,\beta,a,b,x_0,y_0\). That theorem gives the existence of global regular trajectories \(x_g,y_g\), the viability property \(x_g(t)\in C\) for \(t\ge0\), and a uniqueness statement: any other regular constrained DIN trajectory from the same initial data agrees with \(x_g,y_g\) on \([0,\infty)\). Since the given \(x,y\) satisfy the same trajectory and regularity hypotheses, the uniqueness part yields
\[
x(t)=x_g(t),\qquad y(t)=y_g(t)
\]
for all \(t\ge0\). Therefore, by the viability of \(x_g\), the proof obtains
\[
x(t)\in C\qquad(t\ge0).
\]
The Lean steps `intro t ht`, `rw [hxy_eq.1 ht]`, and `exact hviable t ht` are exactly this reduction.

Next the proof applies `constrained_din_global_properties_part_ii`. This theorem says, among other things, that for every real \(\ell\) in the interval
\[
\beta\bigl(\sqrt b-\sqrt{b+a}\bigr)^2\le \ell\le \beta\bigl(\sqrt b+\sqrt{b+a}\bigr)^2,
\]
the constrained energy
\[
E_\ell(t)=\ell\,\Phi(x(t))+\frac12\|a x(t)+b y(t)\|^2
\]
is antitone on \([0,\infty)\), bounded below on its range, and has a limit as \(t\to\infty\). It also gives that \(\dot x\) and \(\dot y\) are square-integrable on \((0,\infty)\), that \(\Phi(x(t))\) has a real limit, and that \(\dot y(t)\to0\). The proof uses the last two facts immediately:
\[
\exists l_\Phi,\quad \Phi(x(t))\to l_\Phi,
\qquad
\dot y(t)\to0.
\]
It then verifies that \(\ell=\beta(a+2b)\) lies in the above interval. Indeed,
\[
\bigl(\sqrt b-\sqrt{b+a}\bigr)^2
= a+2b-2\sqrt b\sqrt{b+a},
\]
and
\[
\bigl(\sqrt b+\sqrt{b+a}\bigr)^2
= a+2b+2\sqrt b\sqrt{b+a},
\]
so the middle term \(a+2b\) lies between them because the product \(\sqrt b\sqrt{b+a}\) is nonnegative. The tactics `nlinarith` and `positivity` are used to verify these inequalities. Hence, with
\[
A(t)=\operatorname{constrainedEnergy}\Phi\,a\,b\,\bigl(\beta(a+2b)\bigr)(x(t),y(t)),
\]
the proof obtains that \(A\) is antitone, bounded below, and convergent to some \(l_E\).

The proof then chooses a minimizer
\[
z_0\in \operatorname{argminSet}\Phi\cap C,
\]
so \(z_0\in C\) and \(\Phi(z_0)\le \Phi(w)\) for every \(w\in H\). From the constrained hypothesis it extracts an open neighborhood \(U\) of \(C\) on which \(\Phi\) is \(C^1\), and proves that for every \(q\in C\),
\[
\Phi \text{ has gradient } \nabla\Phi(q) \text{ at } q,
\]
i.e. `HasGradientAt Φ (gradient Φ q) q`. This is used later to differentiate \(t\mapsto \Phi(x(t))\).

For \(t>0\), the regularity assumptions imply
\[
x'(t)=\dot x(t),\qquad y'(t)=\dot y(t).
\]
The proof sets \(Y(t)=(x(t),y(t))\). Using the trajectory equations and `constrainedDINProjection_eq_self`, which says \(P_C(q)=q\) whenever \(q\in C\), it shows that the constrained DIN phase field at \(Y(t)\) is exactly \((\dot x(t),\dot y(t))\). Therefore
\[
Y'(t)=\text{constrainedDINPhaseField}(Y(t)).
\]
Then it invokes `constrainedDIN_energy_dissipation_at`. Specialized to the present variables, that theorem gives both
\[
A'(t)
=\beta(a+2b)\langle \nabla\Phi(x(t)),\dot x(t)\rangle
-a\langle \dot x(t),\dot y(t)\rangle
-b\|\dot y(t)\|^2
\]
and the dissipation inequality
\[
\beta(a+2b)\langle \nabla\Phi(x(t)),\dot x(t)\rangle
-a\langle \dot x(t),\dot y(t)\rangle
-b\|\dot y(t)\|^2
+(a+b)\|\dot x(t)\|^2
+b\|\dot x(t)-\dot y(t)\|^2\le0.
\]
This is the main energy estimate used to construct the Lyapunov function later.

The proof next establishes a first-order supporting inequality for the convex function \(\Phi\). For \(p,r\in C\), it proves
\[
\Phi(p)+\langle \nabla\Phi(p),r-p\rangle\le \Phi(r).
\]
The argument restricts \(\Phi\) to the line segment \(g(s)=\operatorname{lineMap}(p,r)(s)\), which stays in \(C\) by convexity. Since \(\Phi\) is convex on \(C\), the composite \(s\mapsto \Phi(g(s))\) is convex on \([0,1]\). Its derivative at \(0\) is \(\langle \nabla\Phi(p),r-p\rangle\), and the convexity inequality for derivatives gives
\[
\langle \nabla\Phi(p),r-p\rangle\le \Phi(r)-\Phi(p).
\]
The cited lemma `le_slope_of_hasDerivAt` supplies exactly this derivative-versus-slope inequality. Taking \(p=x(t)\) and \(r=z_0\) gives
\[
\Phi(x(t))+\langle \nabla\Phi(x(t)),z_0-x(t)\rangle\le \Phi(z_0)
\]
for \(t>0\).

The proof also uses the variational characterization of metric projection. The cited theorem `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` states that for a nonempty closed convex set \(C\),
\[
p=P_C(x)
\iff
p\in C \ \text{and}\ \forall y\in C,\ \langle y-p,x-p\rangle\le0.
\]
Applying this to
\[
p=x(t)+\dot x(t),\qquad
x=x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t),
\]
and using the trajectory equation, the proof obtains
\[
\bigl\langle z_0-(x(t)+\dot x(t)),\,
x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t)-(x(t)+\dot x(t))\bigr\rangle\le0.
\]
Using \(a x(t)+b y(t)=-\dot y(t)\), this is rewritten as the key inequality
\[
\langle z_0-x(t),\dot y(t)-\dot x(t)\rangle
+\beta\langle \dot x(t),\nabla\Phi(x(t))\rangle
\le
\beta\langle z_0-x(t),\nabla\Phi(x(t))\rangle
+\langle \dot x(t),\dot y(t)\rangle
-\|\dot x(t)\|^2.
\]

Now the proof defines the auxiliary scalar function
\[
F(t)
=
\langle z_0-x(t),q(t)\rangle
+\frac{a+b}{2}\|z_0-x(t)\|^2
+b\beta\Phi(x(t)),
\]
where \(q(t)=a x(t)+b y(t)=-\dot y(t)\). Differentiating \(F\) and using the key inequality, the Cauchy–Schwarz inequality, and Young’s inequality
\[
2\langle \dot x,\dot y-\dot x\rangle
\le \|\dot x\|^2+\|\dot y-\dot x\|^2,
\]
yields the estimate
\[
F'(t)\le \frac{b+3}{2}\|\dot x(t)\|^2
+\frac{b+1}{2}\|\dot y(t)-\dot x(t)\|^2.
\]
The global minimality of \(z_0\) is used to know
\[
\langle \nabla\Phi(x(t)),z_0-x(t)\rangle\le0.
\]
The tactics `nlinarith` and `ring_nf` close these algebraic inequalities after expanding inner products.

The proof then chooses
\[
\varepsilon=\min\left(\frac{a+b}{2(b+3)},\frac{b}{2(b+1)}\right)>0.
\]
It has
\[
\varepsilon(b+3)\le a+b,\qquad \varepsilon(b+1)\le b.
\]
Define
\[
H(t)=A(t)+\varepsilon F(t).
\]
Using the energy dissipation inequality for \(A'\) and the upper bound for \(F'\), the proof shows
\[
H'(t)\le0\qquad(t>0).
\]
Since \(H\) is continuous on \([0,\infty)\), differentiable on the interior, and has nonpositive derivative there, the lemma `antitoneOn_of_deriv_nonpos` implies that \(H\) is antitone on \([0,\infty)\). Hence
\[
H(t)\le H(0)\qquad(t\ge0).
\]

From the bounded-below hypothesis on \(\Phi\), let \(m\le \Phi(x(t))\) for \(x(t)\in C\). Using this and Cauchy–Schwarz to bound the cross term in \(H\), the proof obtains a lower bound of the form
\[
H(t)\ge K m+\frac{\varepsilon((a+b)-\varepsilon)}{4}\|z_0-x(t)\|^2,
\]
where \(K=\beta(a+2b)+\varepsilon b\beta>0\). Combining this lower bound with the upper bound \(H(t)\le H(0)\), the proof concludes that
\[
\|z_0-x(t)\|^2\le Q
\]
for some \(Q\ge0\), hence \(\|z_0-x(t)\|\le R\) for all \(t\ge0\). Therefore \(x\) is bounded on \([0,\infty)\).

At this point the proof applies `constrained_din_global_properties_part_iii` to the boundedness of \(x\). That theorem gives:
\[
\nabla\Phi(x(t))\text{ is bounded on }[0,\infty),
\qquad
y(t)\text{ is bounded on }[0,\infty),
\qquad
\dot x(t)\text{ is bounded on }[0,\infty),
\]
and
\[
\dot x(t)\to0.
\]
Together with the earlier \(\dot y(t)\to0\), this yields several inner-product limits. For example, since \(\dot x(t)\to0\) and \(\nabla\Phi(x(t))\) is bounded, Cauchy–Schwarz gives
\[
\langle \dot x(t),\nabla\Phi(x(t))\rangle\to0.
\]
Similarly, since \(\dot y(t)\to0\) and \(\dot x(t)\) is bounded,
\[
\langle \dot x(t),\dot y(t)\rangle\to0,
\]
and since \(\dot y(t)-\dot x(t)\to0\) while \(z_0-x(t)\) is bounded,
\[
\langle z_0-x(t),\dot y(t)-\dot x(t)\rangle\to0.
\]
The tactic `squeeze_zero_norm'` is used to convert norm bounds and convergence to these inner-product limits.

The proof now shows that the limit \(l_\Phi\) of \(\Phi(x(t))\) is at most \(\Phi(z_0)\). It starts from the supporting inequality
\[
\Phi(x(t))+\langle \nabla\Phi(x(t)),z_0-x(t)\rangle\le \Phi(z_0)
\]
and rewrites the inner-product term using the key inequality. The resulting extra term tends to \(0\), so taking limits along \(t\to\infty\) gives
\[
l_\Phi\le \Phi(z_0).
\]

Next the proof verifies the distance hypothesis needed for Opial’s lemma. Let
\[
S=\operatorname{argminSet}\Phi\cap C.
\]
For an arbitrary \(z\in S\), the same argument as for \(z_0\) is repeated with \(z\) in place of \(z_0\). This produces a modified auxiliary function \(H_z(t)\) whose derivative is nonpositive, hence \(H_z\) is antitone; the same lower and upper bounds show that \(\|z-x(t)\|\) is bounded. Since \(q(t)\to0\), the cross term \(\langle z-x(t),q(t)\rangle\to0\). Because \(A(t)\to l_E\), \(H_z(t)\) has a limit, and \(\Phi(x(t))\to l_\Phi\), the proof solves for the limit of \(\|z-x(t)\|^2\). Thus
\[
\exists L_z,\qquad \|z-x(t)\|^2\to L_z.
\]
Since the square is nonnegative, \(L_z\ge0\), and by continuity of the square root,
\[
\|z-x(t)\|\to \sqrt{L_z}.
\]
Therefore, for every \(z\in S\), the distance \(\|z-x(t)\|\) has a real limit as \(t\to\infty\). This is exactly the hypothesis required by Opial’s continuous-time lemma.

The proof then verifies the weak-cluster-point hypothesis. Let \(s_n\to\infty\) and suppose that
\[
x(s_n)\rightharpoonup z
\]
weakly. Set \(s'_n=\max(s_n,0)\), so that \(s'_n\to\infty\) and all times are nonnegative. Since \(x(s'_n)\in C\) and \(C\) is closed and convex, the cited theorem `mem_of_tendsto_weakly_of_isClosed_convex` implies
\[
z\in C.
\]
This theorem states that a closed convex subset of a Hilbert space is weakly sequentially closed: if a sequence in \(C\) converges weakly to \(z\), then \(z\in C\).

To show that \(z\) is actually a global minimizer, the proof uses the continuity of the weak topology on inner products. The cited result `weakSpace_continuous_inner_right (gradient Φ z)` says that the map
\[
x\mapsto \langle x,\nabla\Phi(z)\rangle
\]
is continuous on the weak space. Hence weak convergence \(x(s'_n)\rightharpoonup z\) gives
\[
\langle x(s'_n),\nabla\Phi(z)\rangle\to \langle z,\nabla\Phi(z)\rangle,
\]
and therefore
\[
\langle \nabla\Phi(z),x(s'_n)-z\rangle\to0.
\]
Since \(z\in C\) and \(x(s'_n)\in C\), the supporting inequality gives
\[
\Phi(z)+\langle \nabla\Phi(z),x(s'_n)-z\rangle\le \Phi(x(s'_n)).
\]
Taking limits along \(n\to\infty\), using \(\Phi(x(s'_n))\to l_\Phi\), yields
\[
\Phi(z)\le l_\Phi.
\]
But earlier the proof obtained \(l_\Phi\le \Phi(z_0)\), and \(z_0\) is a global minimizer, so \(\Phi(z_0)\le \Phi(z)\). Thus
\[
\Phi(z)\le l_\Phi\le \Phi(z_0)\le \Phi(z),
\]
so equality holds and \(z\) is also a global minimizer. Therefore \(z\in\operatorname{argminSet}\Phi\cap C=S\). This proves that every weak sequential cluster point of \(x\) at infinity lies in \(S\).

Finally, \(S\) is nonempty because \(z_0\in S\). The proof applies `opial_continuous_time` to the trajectory \(x\), the set \(S\), the weak-cluster-point hypothesis just proved, and the distance-convergence hypothesis for every \(z\in S\). Opial’s lemma states that if \(S\) is nonempty, every weak cluster point of \(x(t)\) as \(t\to\infty\) lies in \(S\), and for every \(z\in S\) the distance \(\|x(t)-z\|\) has a limit, then there exists \(z\in S\) such that \(x(t)\rightharpoonup z\) weakly as \(t\to\infty\). Applying it gives \(z\in S\) with weak convergence of \(x(t)\) to \(z\). Unpacking \(z\in S\) yields \(z\in C\) and \(z\in\operatorname{argminSet}\Phi\), which is exactly the stated conclusion.

Throughout the proof, `intro` introduces the arbitrary variables or hypotheses in a universal statement, `rw` and `simp` unfold definitions and rewrite equalities such as the trajectory equations, `exact` supplies the named theorem or the already established fact, and `linarith` and `nlinarith` combine linear and nonlinear arithmetic inequalities. The tactics `field_simp`, `ring`, and `ring_nf` normalize algebraic expressions, `positivity` proves the positivity of constants such as \(\varepsilon\) and \(K\), and `filter_upwards` converts pointwise estimates into eventual statements as \(t\to\infty\).

