## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_5.lean`

## Lean statement
```lean
theorem theorem_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {r α s₀ : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (f : H → ℝ) (hf : Differentiable ℝ f)
    (z dz x y : ℝ → H) (hx : Differentiable ℝ x)
    (hy_diff : Differentiable ℝ y) (hx2 : Differentiable ℝ (deriv x))
    (hsol : IsDrygradTrajectory r hr f hf z dz (s₀ ^ 2 / (2 * (α - 1))))
    (hy : y = timeScaledTrajectory z (fun s => s ^ 2 / (2 * (α - 1))))
    (haverage : x s₀ = y s₀ ∧ ∀ s ∈ Set.Ici s₀,
      deriv x s + ((s / (α - 1))⁻¹) • (x s - y s) = 0) :
    IsDryStarFirstOrder r α s₀ hr f hf x y hx ∧
      ∃ p : ℝ → H, IsDryStarTrajectory r α s₀ f hf x (deriv x) (deriv (deriv x)) p
```

## Statement explanation
The theorem assumes a complete real inner product space \(H\) and real parameters \(r,\alpha,s_0\) with
\[
r>0,\qquad \alpha>1,\qquad s_0>0.
\]
There is a differentiable function \(f:H\to\mathbb R\), and curves
\[
z,dz,x,y:\mathbb R\to H.
\]
The curve \(x\) is differentiable, \(y\) is differentiable, and \(\operatorname{deriv} x\) is differentiable.

The hypotheses are:

- \(h_{\mathrm{sol}}\): the pair \((z,dz)\) satisfies an `IsDrygradTrajectory` property with friction parameter \(r\) and potential \(f\), starting from the scaled time
  \[
  \frac{s_0^2}{2(\alpha-1)}.
  \]
- \(h_y\): \(y\) is the time-scaled trajectory obtained from \(z\) using the time change
  \[
  s\mapsto \frac{s^2}{2(\alpha-1)}.
  \]
- \(h_{\mathrm{average}}\): 
  \[
  x(s_0)=y(s_0),
  \]
  and for every \(s\ge s_0\),
  \[
  \operatorname{deriv} x(s)
  +
  \left(\frac{s}{\alpha-1}\right)^{-1}\bullet (x(s)-y(s))
  =
  0.
  \]
  Here \(\bullet\) denotes scalar multiplication in the vector space \(H\).

The conclusion is a conjunction:

1. The first-order property
   \[
   \text{IsDryStarFirstOrder}\ r\ \alpha\ s_0\ hr\ f\ hf\ x\ y\ hx
   \]
   holds for \(x\) and \(y\).

2. There exists a curve \(p:\mathbb R\to H\) such that
   \[
   \text{IsDryStarTrajectory}\ r\ \alpha\ s_0\ f\ hf\ x\ (\operatorname{deriv} x)\ (\operatorname{deriv}(\operatorname{deriv} x))\ p
   \]
   holds. Thus the second-order trajectory uses \(x\) itself, its first derivative \(\operatorname{deriv} x\), its second derivative \(\operatorname{deriv}(\operatorname{deriv} x)\), and a witness \(p\).

## Lean proof
```lean
by
  have ha1 : 0 < α - 1 := sub_pos.mpr hα
  let dx : ℝ → H := deriv x
  let dy : ℝ → H := deriv y
  let ddx : ℝ → H := deriv (deriv x)
  have hdy : ∀ s, HasDerivAt y (deriv y s) s := fun s => (hy_diff s).hasDerivAt
  have hddx : ∀ s, HasDerivAt (deriv x) (deriv (deriv x) s) s :=
    fun s => (hx2 s).hasDerivAt
  have hτ_domain : ∀ s ∈ Set.Ici s₀,
      s ^ 2 / (2 * (α - 1)) ∈ Set.Ici (s₀ ^ 2 / (2 * (α - 1))) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hdenom : 0 < 2 * (α - 1) := mul_pos (by norm_num) ha1
    apply (div_le_div_iff_of_pos_right hdenom).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (add_nonneg (le_of_lt hs₀) (le_of_lt hspos))]
  have hτ_deriv : ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => t ^ 2 / (2 * (α - 1))) (s / (α - 1)) s := by
    intro s
    convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1
    all_goals
      field_simp [ne_of_gt ha1]
      ring
  have hfirst : IsDryStarFirstOrder r α s₀ hr f hf x y hx := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hdτpos : 0 < s / (α - 1) := div_pos hspos ha1
    have hsol_s := hsol (s ^ 2 / (2 * (α - 1))) (hτ_domain s hs)
    rcases hsol_s.2 with ⟨u, husub, huseq⟩
    have hy_point : y s = z (s ^ 2 / (2 * (α - 1))) := by
      simp [hy, timeScaledTrajectory]
    have hchain : HasDerivAt y ((s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1)))) s := by
      simpa only [hy, timeScaledTrajectory] using
        (hsol_s.1.scomp s (hτ_deriv s))
    have hdy_eq : dy s = (s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1))) :=
      (hdy s).unique hchain
    have hdy_deriv : HasDerivAt y (deriv y s) s := by
      convert hdy s using 1
    refine ⟨hdy_deriv, u, ?_, ?_, ?_⟩
    · -- Positive one-homogeneity transports the norm subgradient along the time scale.
      intro q
      have husub_real : ∀ q : H,
          r * ‖dz (s ^ 2 / (2 * (α - 1)))‖ +
              inner ℝ u (q - dz (s ^ 2 / (2 * (α - 1)))) ≤ r * ‖q‖ := by
        intro q
        exact_mod_cast husub q
      have hscaled_sub := dryFriction_subgradient_smul_pos hdτpos husub_real q
      rw [← hdy_eq] at hscaled_sub
      rw [(hdy s).deriv]
      exact_mod_cast hscaled_sub
    · have hscaled := congrArg (fun w : H => (s / (α - 1)) • w) huseq
      simp only [smul_add, smul_zero] at hscaled
      change dy s + (s / (α - 1)) • u + (s / (α - 1)) • gradient f (y s) = 0
      rw [hdy_eq, hy_point]
      exact hscaled
    · have havg := haverage.2 s hs
      have hcoef : (α - 1) / s = (s / (α - 1))⁻¹ := by
        field_simp [ne_of_gt ha1, ne_of_gt hspos]
      rw [hcoef]
      exact havg
  refine ⟨hfirst, ?_⟩
  have hyx : ∀ s ∈ Set.Ici s₀, y s = x s + (s / (α - 1)) • dx s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hcne : s / (α - 1) ≠ 0 := ne_of_gt (div_pos hspos ha1)
    have havg := congrArg (fun w : H => (s / (α - 1)) • w) (haverage.2 s hs)
    simp only [smul_add, smul_zero, smul_smul] at havg
    rw [mul_inv_cancel₀ hcne, one_smul] at havg
    calc y s = y s + ((s / (α - 1)) • dx s + (x s - y s)) := by rw [havg, add_zero]
         _ = x s + (s / (α - 1)) • dx s := by abel
  have hdy_avg : ∀ s ∈ Set.Ici s₀,
      dy s = (s / (α - 1)) • ddx s + (1 + 1 / (α - 1)) • dx s := by
    intro s hs
    let R : ℝ → H := fun t => x t + (t / (α - 1)) • dx t
    have hR : HasDerivAt R
        (dx s + (1 / (α - 1)) • dx s + (s / (α - 1)) • ddx s) s := by
      convert (hx s).hasDerivAt.add
        ((hasDerivAt_id s).div_const (α - 1) |>.smul (hddx s)) using 1
      all_goals
        simp
        module
    have hdiff : HasDerivAt (fun t => y t - R t)
        (dy s - (dx s + (1 / (α - 1)) • dx s + (s / (α - 1)) • ddx s)) s :=
      (hdy s).sub hR
    have hzero : dy s - (dx s + (1 / (α - 1)) • dx s +
        (s / (α - 1)) • ddx s) = 0 := by
      change s₀ ≤ s at hs
      rcases lt_or_eq_of_le hs with hslt | rfl
      · have heq : (fun t => y t - R t) =ᶠ[nhds s] fun _ => 0 := by
          filter_upwards [eventually_gt_nhds hslt] with t ht
          simp [R, hyx t (le_of_lt ht)]
        exact (hdiff.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s 0)
      · have heq : (fun t => y t - R t) =ᶠ[nhdsWithin s₀ (Set.Ioi s₀)] fun _ => 0 := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          change s₀ < t at ht
          simp [R, hyx t (le_of_lt ht)]
        calc
          dy s₀ - (dx s₀ + (1 / (α - 1)) • dx s₀ + (s₀ / (α - 1)) • ddx s₀) =
              derivWithin (fun t => y t - R t) (Set.Ioi s₀) s₀ :=
            (hdiff.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi s₀)).symm
          _ = 0 :=
            by
              have hend : y s₀ - R s₀ = 0 := by
                simp [R, hyx s₀ (Set.mem_Ici.mpr le_rfl)]
              have hzeroDeriv : HasDerivWithinAt (fun t => y t - R t) 0 (Set.Ioi s₀) s₀ :=
                (hasDerivAt_const s₀ (0 : H)).hasDerivWithinAt.congr_of_eventuallyEq
                  heq hend
              exact hzeroDeriv.derivWithin (uniqueDiffWithinAt_Ioi s₀)
    rw [sub_eq_zero] at hzero
    rw [hzero]
    module
  classical
  let uOf : ℝ → H := fun s => if hs : s ∈ Set.Ici s₀ then
    Classical.choose ((hsol (s ^ 2 / (2 * (α - 1))) (hτ_domain s hs)).2) else 0
  have huOf_spec : ∀ s (hs : s ∈ Set.Ici s₀),
      (∀ q : H,
        (dryFrictionPotential (H := H) r (dz (s ^ 2 / (2 * (α - 1)))) : EReal) +
          (inner ℝ (uOf s) (q - dz (s ^ 2 / (2 * (α - 1)))) : EReal) ≤
            dryFrictionPotential (H := H) r q) ∧
        dz (s ^ 2 / (2 * (α - 1))) + uOf s + gradient f (z (s ^ 2 / (2 * (α - 1)))) = 0 := by
    intro s hs
    dsimp [uOf]
    rw [dif_pos hs]
    exact Classical.choose_spec ((hsol _ (hτ_domain s hs)).2)
  let p : ℝ → H := fun s => -uOf s
  refine ⟨p, ?_⟩
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hcne : s / (α - 1) ≠ 0 := ne_of_gt (div_pos hspos ha1)
  have hy_point : y s = z (s ^ 2 / (2 * (α - 1))) := by simp [hy, timeScaledTrajectory]
  have hsol_s := hsol (s ^ 2 / (2 * (α - 1))) (hτ_domain s hs)
  have hchain : HasDerivAt y ((s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1)))) s := by
    simpa only [hy, timeScaledTrajectory] using hsol_s.1.scomp s (hτ_deriv s)
  have hdy_eq : dy s = (s / (α - 1)) • dz (s ^ 2 / (2 * (α - 1))) :=
    (hdy s).unique hchain
  rcases huOf_spec s hs with ⟨hsub, hforce⟩
  refine ⟨(hx s).hasDerivAt, hddx s, ?_, ?_⟩
  · have hproj := neg_drygrad_subgradient_mem_projector hr hsub hforce
    rw [← hy_point, hyx s hs] at hproj
    simpa [p] using hproj
  · have hscaled := congrArg (fun w : H => (s / (α - 1)) • w) hforce
    simp only [smul_add, smul_zero] at hscaled
    rw [← hdy_eq, ← hy_point] at hscaled
    have hdiv := congrArg (fun w : H => (s / (α - 1))⁻¹ • w) hscaled
    simp only [smul_add, smul_zero, smul_smul] at hdiv
    have hone : (s / (α - 1))⁻¹ * (s / (α - 1)) = 1 := inv_mul_cancel₀ hcne
    rw [hone, one_smul] at hdiv
    have hcoef : (s / (α - 1))⁻¹ * (1 + 1 / (α - 1)) = α / s := by
      field_simp [ne_of_gt hspos, ne_of_gt ha1]
      ring
    rw [hdy_avg s hs, smul_add, smul_smul, smul_smul, hcoef] at hdiv
    rw [hone, one_smul] at hdiv
    simp only [one_smul] at hdiv
    rw [← hyx s hs]
    simp only [p]
    calc
      ddx s + (α / s) • dx s + gradient f (y s) - -uOf s =
          ddx s + (α / s) • dx s + uOf s + gradient f (y s) := by abel
      _ = 0 := hdiv
```

## Proof explanation
The proof can be divided into several main parts.

First, the proof fixes notation and records basic derivative facts. It defines
\[
dx=\operatorname{deriv} x,\qquad dy=\operatorname{deriv} y,\qquad ddx=\operatorname{deriv}(\operatorname{deriv} x).
\]
From the differentiability assumptions it obtains pointwise derivative facts:
\[
\forall s,\quad \operatorname{HasDerivAt} y\ (dy(s))\ s,
\]
and
\[
\forall s,\quad \operatorname{HasDerivAt} (\operatorname{deriv} x)\ (ddx(s))\ s.
\]
It also notes that \(\alpha-1>0\).

The proof then studies the time scaling
\[
\tau(s)=\frac{s^2}{2(\alpha-1)}.
\]
Using monotonicity of the square on positive numbers, it proves that if \(s\ge s_0\), then
\[
\tau(s)\ge \tau(s_0)=\frac{s_0^2}{2(\alpha-1)}.
\]
It also proves
\[
\tau'(s)=\frac{s}{\alpha-1}.
\]
The positivity of \(s/(\alpha-1)\) for \(s\ge s_0>0\) is important later.

To prove the first conclusion `IsDryStarFirstOrder`, the proof fixes an arbitrary \(s\ge s_0\). From the hypothesis \(h_{\mathrm{sol}}\) at time \(\tau(s)\), it obtains a subgradient \(u\) and the force balance equation
\[
dz(\tau(s))+u+\nabla f(z(\tau(s)))=0.
\]
By the definition of the time-scaled trajectory,
\[
y(s)=z(\tau(s)).
\]
Using the chain rule for \(\tau\), it proves
\[
\operatorname{HasDerivAt} y
\left(\frac{s}{\alpha-1}\bullet dz(\tau(s))\right)
s.
\]
Uniqueness of derivatives gives
\[
dy(s)=\frac{s}{\alpha-1}\bullet dz(\tau(s)).
\]
Now the subgradient inequality for \(u\) is scaled by the positive factor \(\frac{s}{\alpha-1}\), using the lemma `dryFriction_subgradient_smul_pos`. The force balance equation is also scaled by the same factor. Finally, the average equation is rewritten using the identity
\[
\frac{\alpha-1}{s}=\left(\frac{s}{\alpha-1}\right)^{-1},
\]
which matches the required first-order dry-star condition.

The second part of the proof derives an algebraic relation between \(x\) and \(y\). For \(s\ge s_0\), the average equation
\[
dx(s)+\left(\frac{s}{\alpha-1}\right)^{-1}\bullet(x(s)-y(s))=0
\]
is multiplied by the nonzero scalar \(\frac{s}{\alpha-1}\). After simplification this yields
\[
\frac{s}{\alpha-1}\bullet dx(s)+(x(s)-y(s))=0,
\]
or equivalently
\[
y(s)=x(s)+\frac{s}{\alpha-1}\bullet dx(s).
\]
This relation is recorded as `hyx`.

Next, the proof differentiates this relation. It defines
\[
R(t)=x(t)+\frac{t}{\alpha-1}\bullet dx(t).
\]
The derivative of \(R\) is computed as
\[
R'(s)
=
dx(s)+\frac{1}{\alpha-1}\bullet dx(s)
+\frac{s}{\alpha-1}\bullet ddx(s).
\]
Since \(y(t)-R(t)=0\) for \(t\ge s_0\), the derivative of \(y-R\) is zero. For \(s>s_0\), this is immediate from a neighborhood equality. For \(s=s_0\), the proof uses a right-neighborhood within `Set.Ioi s_0` and `derivWithin` to handle the boundary. Therefore
\[
dy(s)
=
\frac{s}{\alpha-1}\bullet ddx(s)
+
\left(1+\frac{1}{\alpha-1}\right)\bullet dx(s).
\]

The proof now constructs the witness \(p\) for the second-order trajectory. For each \(s\ge s_0\), it chooses \(u(s)\) from the `hsol` data at time \(\tau(s)\), and sets
\[
p(s)=-u(s).
\]
Outside \(s\ge s_0\), the value is taken to be \(0\). The chosen \(u(s)\) satisfies the dry-friction subgradient inequality and the force balance
\[
dz(\tau(s))+u(s)+\nabla f(z(\tau(s)))=0.
\]

Finally, for \(s\ge s_0\), the proof verifies the second-order `IsDryStarTrajectory` condition with \(p(s)=-u(s)\). The derivative facts for \(x\) and \(dx\) are immediate. The projector condition for \(p\) is obtained from the lemma `neg_drygrad_subgradient_mem_projector` applied to the chosen \(u(s)\). The force balance equation is transported as follows. Scaling
\[
dz(\tau(s))+u(s)+\nabla f(z(\tau(s)))=0
\]
by \(\frac{s}{\alpha-1}\) gives
\[
dy(s)+\frac{s}{\alpha-1}\bullet u(s)
+\frac{s}{\alpha-1}\bullet \nabla f(y(s))
=
0.
\]
Multiplying by the inverse scalar \(\left(\frac{s}{\alpha-1}\right)^{-1}\) gives
\[
\left(\frac{s}{\alpha-1}\right)^{-1}\bullet dy(s)
+u(s)
+\nabla f(y(s))
=
0.
\]
Using the formula for \(dy(s)\) derived above,
\[
dy(s)
=
\frac{s}{\alpha-1}\bullet ddx(s)
+
\left(1+\frac{1}{\alpha-1}\right)\bullet dx(s),
\]
and the identity
\[
\left(\frac{s}{\alpha-1}\right)^{-1}
\left(1+\frac{1}{\alpha-1}\right)
=
\frac{\alpha}{s},
\]
the equation becomes
\[
ddx(s)
+
\frac{\alpha}{s}\bullet dx(s)
+
u(s)
+
\nabla f(y(s))
=
0.
\]
Since \(p(s)=-u(s)\), this matches the required second-order dry-star equation. Rewriting \(y(s)\) using the relation
\[
y(s)=x(s)+\frac{s}{\alpha-1}\bullet dx(s)
\]
gives the final form required by `IsDryStarTrajectory`.

Important Lean tactics used in the proof include `have` and `let` for intermediate facts and abbreviations; `intro` to fix arbitrary \(s\ge s_0\); `rcases` to extract the chosen subgradient from an existence hypothesis; `rw` and `simp` for rewriting with equations and simplifying scalar-multiplication expressions; `nlinarith` for nonlinear arithmetic inequalities; `field_simp` and `ring` for field and scalar algebra; `module` and `abel` for vector-space arithmetic; `HasDerivAt.unique` for uniqueness of derivatives; `congr_of_eventuallyEq` and `derivWithin` for derivative equality at the boundary; and `Classical.choose` with `dif_pos` to define a chosen subgradient curve.

