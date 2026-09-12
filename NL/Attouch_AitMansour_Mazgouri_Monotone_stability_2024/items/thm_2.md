## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_2.lean`

## Lean statement
```lean
theorem thm_2 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (r T : ℝ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hr : 0 < r) (hT : 0 < T)
    (hball : ∀ μ, μ ∈ V → ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ r) :
    ∀ μ, μ ∈ V → ∀ μ', μ' ∈ V →
      let m_μ
```

## Statement explanation
The declaration `thm_2` is a quantitative stability estimate for a parameter-dependent family of second-order evolution equations in a real inner product space. The type \(H\) is the state space, equipped with a norm and real inner product, and \(M\) is a normed parameter space. A subset \(V\subseteq M\) indexes the parameters for which the assumptions are imposed. For each parameter \(\mu\), the operator \(A_\mu:H\to H\) is given by \(A_\mu u=A(\mu,u)\). The real number \(\gamma\) is the damping coefficient in the evolution equation, while \(x_\mu,dx_\mu,ddx_\mu:\mathbb R\to H\) are the position, velocity, and acceleration components of a solution. The maps \(u_{0,\mu},v_{0,\mu}\in H\) are initial position and velocity, and \(\alpha_\mu\in\mathbb R\) is the cocoercivity modulus of \(A_\mu\).

The hypotheses are as follows. First, \(r>0\) and \(T>0\). Second, for every \(\mu\in V\), the modulus is positive, \(\alpha_\mu>0\), and \(A_\mu\) is \(\alpha_\mu\)-cocoercive: for all \(u,v\in H\),
\[
\alpha_\mu\|A_\mu u-A_\mu v\|^2\le \langle A_\mu u-A_\mu v,u-v\rangle .
\]
Third, for every \(\mu\in V\), the predicate `ext_def_2` holds for the tuple \((A_\mu,\gamma,u_{0,\mu},v_{0,\mu},x_\mu,dx_\mu,ddx_\mu)\). The proof does not expand this predicate directly; it uses the cited lemma `solution_data`, which extracts from it that \(\gamma>0\), that \(x_\mu\) and \(dx_\mu\) are absolutely continuous on the interval \(0\le t\le T\), that \(x_\mu(0)=u_{0,\mu}\) and \(dx_\mu(0)=v_{0,\mu}\), and that almost everywhere for \(t\ge0\) one has
\[
ddx_\mu(t)+\gamma\,dx_\mu(t)+A_\mu(x_\mu(t))=0,
\]
together with the derivative relations
\[
x_\mu'(t)=dx_\mu(t),\qquad dx_\mu'(t)=ddx_\mu(t).
\]
Fourth, for every \(\mu\in V\), almost every \(t\in[0,T]\) satisfies \(\|x_\mu(t)\|\le r\), so the trajectory remains in the closed ball of radius \(r\) almost everywhere on the time interval.

The conclusion is that for all \(\mu,\mu'\in V\), after defining
\[
m_\mu=\sqrt{1+2\gamma^2+\frac{2}{(\alpha_\mu)^2}},\qquad
m_{\mu'}=\sqrt{1+2\gamma^2+\frac{2}{(\alpha_{\mu'})^2}},\qquad
m=\max(m_\mu,m_{\mu'}),
\]
the following estimate holds for almost every \(t\in[0,T]\):
\[
\|x_\mu(t)-x_{\mu'}(t)\|
\le e^{mT}\sqrt{\|u_{0,\mu}-u_{0,\mu'}\|^2+\|v_{0,\mu}-v_{0,\mu'}\|^2}
+m^{-1}(e^{mT}-1)\operatorname{def}_6(r,hr,A_\mu,A_{\mu'}).
\]
Here \(\operatorname{def}_6(r,hr,A_\mu,A_{\mu'})\) is the quantity introduced by the abbreviation `def_6`, namely `supDiscrepancyOnBall r hr (A μ) (A μ')`. The cited lemmas `def_6_bddAbove_of_cocoercive` and `def_6_le_of_norm_le` show that, under the cocoercivity assumptions, the set of values \(\|A_\mu u-A_{\mu'}u\|\) for \(\|u\|\le r\) is bounded above and that \(\operatorname{def}_6(r,hr,A_\mu,A_{\mu'})\) is an upper bound for those values. Thus the theorem says that the distance between two trajectories is controlled by the initial data difference plus the discrepancy between the two operators on the ball of radius \(r\), with an exponential factor in time depending on \(\gamma\) and the cocoercivity moduli.

## Lean proof
```lean
Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))
      let m := max m_μ m_μ'
      ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤ Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          m⁻¹ * (Real.exp (m * T) - 1) * def_6 r hr (A μ) (A μ') := by
  intro μ hμ μ' hμ'
  dsimp
  obtain ⟨hαμ, hcoμ⟩ := hC₁ μ hμ
  obtain ⟨hαμ', hcoμ'⟩ := hC₁ μ' hμ'
  obtain ⟨hγμ, hxACμ, hdxACμ, hx0μ, hdx0μ, hodeμ, hxderivμ, hdxderivμ⟩ :=
    solution_data hT (hsol μ hμ)
  obtain ⟨hγμ', hxACμ', hdxACμ', hx0μ', hdx0μ', hodeμ', hxderivμ', hdxderivμ'⟩ :=
    solution_data hT (hsol μ' hμ')
  have hD_bdd : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ r ∧ q = ‖A μ u - A μ' u‖} :=
    def_6_bddAbove_of_cocoercive hr.le hαμ hαμ' (A μ) (A μ') hcoμ hcoμ'
  have hD_bound : ∀ ⦃u : H⦄, ‖u‖ ≤ r →
      ‖A μ u - A μ' u‖ ≤ def_6 r hr (A μ) (A μ') := by
    intro u hu
    exact def_6_le_of_norm_le hr (A μ) (A μ') hD_bdd hu
  have hD_nonneg : 0 ≤ def_6 r hr (A μ) (A μ') := by
    have hzero : ‖A μ (0 : H) - A μ' 0‖ ≤ def_6 r hr (A μ) (A μ') :=
      hD_bound (by simpa using hr.le)
    exact (norm_nonneg _).trans hzero
  let y : ℝ → H := fun t => x μ t - x μ' t
  let z : ℝ → H := fun t => dx μ t - dx μ' t
  let w : ℝ → ℝ := fun t => ‖y t‖ ^ 2 + ‖z t‖ ^ 2
  have hyAC : AbsolutelyContinuousOnInterval y 0 T := by
    simpa [y] using hxACμ.fun_sub hxACμ'
  have hzAC : AbsolutelyContinuousOnInterval z 0 T := by
    simpa [z] using hdxACμ.fun_sub hdxACμ'
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := by
    simpa [w] using (ac_norm_sq hyAC).fun_add (ac_norm_sq hzAC)
  have hw_nonneg : ∀ t, 0 ≤ w t := by
    intro t
    dsimp [w]
    positivity
  have hw0 : w 0 = ‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2 := by
    simp only [w, y, z, hx0μ, hx0μ', hdx0μ, hdx0μ']
  have hwDeriv : ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      HasDerivAt w
        (2 * inner ℝ (y t) (z t) +
          2 * inner ℝ (z t) (ddx μ t - ddx μ' t)) t := by
    filter_upwards [hxderivμ, hxderivμ', hdxderivμ, hdxderivμ'] with t hxμ hxμ' hdxμ hdxμ'
    intro ht
    have hyD : HasDerivAt y (z t) t := by
      simpa [y, z] using (hxμ ht).sub (hxμ' ht)
    have hzD : HasDerivAt z (ddx μ t - ddx μ' t) t := by
      simpa [z] using (hdxμ ht).sub (hdxμ' ht)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  let D := def_6 r hr (A μ) (A μ')
  let m := max (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ) ^ 2))
    (Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2))
  have hD0 : 0 ≤ D := by simpa [D] using hD_nonneg
  have hmone : 1 ≤ m := by
    apply le_trans ?_ (le_max_right _ _)
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hsq : 0 ≤ γ ^ 2 := sq_nonneg _
    have hinv : 0 ≤ 2 / (α μ') ^ 2 := by positivity
    linarith
  have hm0 : 0 ≤ m := by linarith
  have hm : 0 < m := by linarith
  have hfixed_pair (t : ℝ) :
      inner ℝ (y t) (z t) + inner ℝ (z t)
          (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))) ≤ m * w t := by
    have hbase := first_order_sq_bound (gamma := γ) hαμ' hcoμ'
      (x μ t) (x μ' t) (dx μ t) (dx μ' t)
    have hbase' : ‖z t‖ ^ 2 + ‖-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
        (1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2) * w t := by
      rw [show -γ • dx μ t - A μ' (x μ t) -
          (-γ • dx μ' t - A μ' (x μ' t)) =
          -γ • (dx μ t - dx μ' t) - (A μ' (x μ t) - A μ' (x μ' t)) by module] at hbase
      simpa [z, w] using hbase
    have hcoef : 1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2 ≤ m ^ 2 := by
      have hnon : 0 ≤ 1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2 := by positivity
      have hsqrtle : Real.sqrt (1 + 2 * γ ^ 2 + 2 / (α μ') ^ 2) ≤ m :=
        le_max_right _ _
      rw [← Real.sq_sqrt hnon]
      exact (sq_le_sq₀ (Real.sqrt_nonneg _) hm0).mpr hsqrtle
    have hsq : ‖z t‖ ^ 2 + ‖-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2 ≤
        m ^ 2 * w t := by
      exact hbase'.trans (mul_le_mul_of_nonneg_right hcoef (hw_nonneg t))
    have hpair := two_pairing_le (y t) (z t) (z t)
      (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t)))
    have hwrt : Real.sqrt (w t) ^ 2 = w t := Real.sq_sqrt (hw_nonneg t)
    have hsqrt : Real.sqrt (‖z t‖ ^ 2 + ‖-γ • z t -
        (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2) ≤ m * Real.sqrt (w t) := by
      have := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs, abs_of_nonneg hm0] at this
      exact this
    calc
      inner ℝ (y t) (z t) + inner ℝ (z t) (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))) ≤
          Real.sqrt (‖y t‖ ^ 2 + ‖z t‖ ^ 2) *
            Real.sqrt (‖z t‖ ^ 2 + ‖-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))‖ ^ 2) := hpair
      _ ≤ Real.sqrt (w t) * (m * Real.sqrt (w t)) := by
        simpa [w] using mul_le_mul_of_nonneg_left hsqrt
          (Real.sqrt_nonneg (‖y t‖ ^ 2 + ‖z t‖ ^ 2))
      _ = m * w t := by nlinarith [hwrt]
  have hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w t <= m * w t + D * w t ^ (1 / 2 : ℝ) := by
    filter_upwards [hodeμ, hodeμ', hwDeriv, hball μ hμ] with t htodeμ htodeμ' htderiv htball
    intro htIcc
    have hddxμ : ddx μ t = -γ • dx μ t - A μ (x μ t) := by
      calc
        ddx μ t = -(γ • dx μ t + A μ (x μ t)) :=
          eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using htodeμ htIcc.1)
        _ = -γ • dx μ t - A μ (x μ t) := by module
    have hddxμ' : ddx μ' t = -γ • dx μ' t - A μ' (x μ' t) := by
      calc
        ddx μ' t = -(γ • dx μ' t + A μ' (x μ' t)) :=
          eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using htodeμ' htIcc.1)
        _ = -γ • dx μ' t - A μ' (x μ' t) := by module
    have hddx : ddx μ t - ddx μ' t =
        (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t))) -
          (A μ (x μ t) - A μ' (x μ t)) := by
      rw [hddxμ, hddxμ']
      dsimp [z]
      module
    have hforce : ‖A μ (x μ t) - A μ' (x μ t)‖ <= D := by
      simpa [D] using hD_bound (htball htIcc)
    have hz_le : ‖z t‖ <= Real.sqrt (w t) := by
      apply Real.le_sqrt_of_sq_le
      dsimp [w]
      nlinarith [sq_nonneg ‖y t‖]
    have hforce_pair :
        -inner ℝ (z t) (A μ (x μ t) - A μ' (x μ t)) <= D * Real.sqrt (w t) := by
      calc
        -inner ℝ (z t) (A μ (x μ t) - A μ' (x μ t)) <=
            ‖z t‖ * ‖A μ (x μ t) - A μ' (x μ t)‖ := by
              exact le_trans (le_abs_self _) (by
                simpa using norm_inner_le_norm (𝕜 := ℝ) (z t)
                  (A μ (x μ t) - A μ' (x μ t)))
        _ <= D * Real.sqrt (w t) := by
              calc
                ‖z t‖ * ‖A μ (x μ t) - A μ' (x μ t)‖ <= ‖z t‖ * D :=
                  mul_le_mul_of_nonneg_left hforce (norm_nonneg _)
                _ <= Real.sqrt (w t) * D :=
                  mul_le_mul_of_nonneg_right hz_le hD0
                _ = D * Real.sqrt (w t) := by ring
    have henergy :
        inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t) =
        (inner ℝ (y t) (z t) + inner ℝ (z t)
          (-γ • z t - (A μ' (x μ t) - A μ' (x μ' t)))) -
          inner ℝ (z t) (A μ (x μ t) - A μ' (x μ t)) := by
      rw [hddx]
      simp only [inner_sub_right]
      ring
    have hderiv_eq : deriv w t =
        2 * (inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t)) := by
      rw [(htderiv htIcc.1).deriv]
      ring
    rw [hderiv_eq, henergy]
    rw [← Real.sqrt_eq_rpow]
    nlinarith [hfixed_pair t, hforce_pair]
  have hgronwall := ext_lem_1 (w := w) (a := fun _ : ℝ => m)
    (b := fun _ : ℝ => D) (t₀ := 0) (T := T) (α := (1 / 2 : ℝ))
    hT (by norm_num) (by norm_num) (by simpa using hwAC)
    (by intro t ht; exact hw_nonneg t)
    (by simp)
    (by simp)
    (Filter.Eventually.of_forall (fun t _ => hD0)) (by simpa using hineq)
  have hconst_int (a b : ℝ) : (∫ s in a..b, m) = (b - a) * m := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  filter_upwards with t htIcc
  have ht0 : 0 <= t := htIcc.1
  have htT : t <= T := htIcc.2
  have hgr := hgronwall t ht0 (by simpa using htT)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hkernel0 : (∫ s in 0..t, Real.exp ((t - s) * m)) =
      m⁻¹ * (Real.exp (m * t) - 1) := by
    calc
      (∫ s in 0..t, Real.exp ((t - s) * m)) =
          ∫ s in 0..t, Real.exp (m * (t - s)) * 1 := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with s hs
            ring
      _ = m⁻¹ * (Real.exp (m * t) - 1) * 1 := exp_kernel_integral m 1 t hm
      _ = m⁻¹ * (Real.exp (m * t) - 1) := by ring
  have hgr' : Real.sqrt (w t) <=
      Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) +
        m⁻¹ * (Real.exp (m * t) - 1) * D := by
    rw [hkernel0] at hgr
    convert hgr using 1
    all_goals ring
  have hmt : m * t <= m * T := mul_le_mul_of_nonneg_left htT hm0
  have hexp : Real.exp (m * t) <= Real.exp (m * T) := Real.exp_le_exp.mpr hmt
  have hkernel : m⁻¹ * (Real.exp (m * t) - 1) * D <=
      m⁻¹ * (Real.exp (m * T) - 1) * D := by
    have hsub := sub_le_sub_right hexp 1
    have hscale : 0 <= m⁻¹ * D := mul_nonneg (inv_nonneg.mpr hm0) hD0
    nlinarith [mul_le_mul_of_nonneg_left hsub hscale]
  have hy_le : ‖x μ t - x μ' t‖ <= Real.sqrt (w t) := by
    change ‖y t‖ <= Real.sqrt (w t)
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  have hinit0 : 0 <= Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) :=
    Real.sqrt_nonneg _
  calc
    ‖x μ t - x μ' t‖ <= Real.sqrt (w t) := hy_le
    _ <= Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) +
        m⁻¹ * (Real.exp (m * t) - 1) * D := hgr'
    _ <= Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * T) +
        m⁻¹ * (Real.exp (m * T) - 1) * D := by
      exact add_le_add (mul_le_mul_of_nonneg_left hexp hinit0) hkernel
    _ = Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        m⁻¹ * (Real.exp (m * T) - 1) * def_6 r hr (A μ) (A μ') := by
      dsimp [D]
      ring
```

## Proof explanation
The proof begins with `intro μ hμ μ' hμ'`, introducing arbitrary parameters \(\mu,\mu'\in V\). The tactic `dsimp` unfolds the local `let` definitions in the goal, so the quantities \(m_\mu,m_{\mu'},m\) become explicit. Then `obtain` destructs the assumptions `hC₁ μ hμ` and `hC₁ μ' hμ'`, giving \(\alpha_\mu>0\), \(\alpha_{\mu'}>0\), and the two cocoercivity inequalities for \(A_\mu\) and \(A_{\mu'}\).

Next, the proof applies `solution_data hT (hsol μ hμ)` and `solution_data hT (hsol μ' hμ')`. The lemma `solution_data` states that from `ext_def_2 A γ u₀ v₀ x dx ddx` and \(T>0\) one obtains \(0<\gamma\), absolute continuity of \(x\) and \(dx\) on \(0\le t\le T\), the initial conditions \(x(0)=u_0\), \(dx(0)=v_0\), the almost-everywhere ODE \(ddx+\gamma dx+A(x)=0\) for \(t\ge0\), and the almost-everywhere derivative relations \(x'=dx\), \(dx'=ddx\). The proof extracts these facts separately for \(\mu\) and \(\mu'\). The positivity of \(\gamma\) is also extracted, though the later estimates mainly use the ODE and absolute-continuity consequences.

The proof then establishes a uniform bound for the operator discrepancy. It applies `def_6_bddAbove_of_cocoercive` with \(a=\alpha_\mu\), \(b=\alpha_{\mu'}\), \(A=A_\mu\), and \(B=A_{\mu'}\). The lemma states that if \(0\le r\), \(a>0\), \(b>0\), \(A\) is \(a\)-cocoercive, and \(B\) is \(b\)-cocoercive, then the set
\[
\{q:\mathbb R\mid \exists u\in H,\ \|u\|\le r,\ q=\|Au-Bu\|\}
\]
is bounded above. Hence the discrepancy values \(\|A_\mu u-A_{\mu'}u\|\) on the ball \(\|u\|\le r\) are bounded above. Then `def_6_le_of_norm_le` is applied. This lemma says that if \(r>0\), the above set is bounded above, and \(\|u\|\le r\), then
\[
\|Au-Bu\|\le \operatorname{def}_6(r,hr,A,B).
\]
Thus the proof obtains the pointwise bound
\[
\|u\|\le r\implies \|A_\mu u-A_{\mu'}u\|\le D,
\]
where \(D=\operatorname{def}_6(r,hr,A_\mu,A_{\mu'})\). Taking \(u=0\), which is allowed because \(r>0\), gives \(\|A_\mu0-A_{\mu'}0\|\le D\); since the left side is nonnegative, this yields \(D\ge0\).

The proof next introduces the energy variables
\[
y=x_\mu-x_{\mu'},\qquad z=dx_\mu-dx_{\mu'},\qquad
w=\|y\|^2+\|z\|^2.
\]
The absolute continuity of \(y\) follows from subtracting the two absolutely continuous functions \(x_\mu\) and \(x_{\mu'}\), using `fun_sub`. Similarly, \(z\) is absolutely continuous. The lemma `ac_norm_sq` states that if a function \(f\) is absolutely continuous, then \(t\mapsto\|f(t)\|^2\) is absolutely continuous. Applying it to \(y\) and \(z\), then adding the two results, shows that \(w\) is absolutely continuous on \(0\le t\le T\). The nonnegativity of \(w\) is immediate from the sum of two squares of norms. The initial value is computed using \(x_\mu(0)=u_{0,\mu}\), \(x_{\mu'}(0)=u_{0,\mu'}\), \(dx_\mu(0)=v_{0,\mu}\), and \(dx_{\mu'}(0)=v_{0,\mu'}\):
\[
w(0)=\|u_{0,\mu}-u_{0,\mu'}\|^2+\|v_{0,\mu}-v_{0,\mu'}\|^2.
\]

The proof then computes the derivative of \(w\). Using the almost-everywhere derivative relations from `solution_data`, it obtains \(y'(t)=z(t)\) and \(z'(t)=ddx_\mu(t)-ddx_{\mu'}(t)\). The derivative of a squared norm gives the inner-product formula, so
\[
w'(t)=2\langle y(t),z(t)\rangle
+2\langle z(t),ddx_\mu(t)-ddx_{\mu'}(t)\rangle
\]
almost everywhere for \(t\ge0\).

To bound the first inner product term, the proof defines
\[
D=\operatorname{def}_6(r,hr,A_\mu,A_{\mu'}),\qquad
m=\max\left(
\sqrt{1+2\gamma^2+\frac{2}{(\alpha_\mu)^2}},
\sqrt{1+2\gamma^2+\frac{2}{(\alpha_{\mu'})^2}}
\right).
\]
Because \(\alpha_{\mu'}>0\), the quantity \(1+2\gamma^2+2/(\alpha_{\mu'})^2\) is at least \(1\), so its square root is at least \(1\). Since \(m\) is at least that square root, one has \(m\ge1\), hence \(m>0\). This ensures that \(m^{-1}\) is meaningful and nonnegative later.

The key pointwise estimate is
\[
\langle y(t),z(t)\rangle
+\left\langle z(t),-\gamma z(t)-\bigl(A_{\mu'}(x_\mu(t))-A_{\mu'}(x_{\mu'}(t))\bigr)\right\rangle
\le m\,w(t).
\]
To prove it, the proof applies `first_order_sq_bound` with \(A=A_{\mu'}\), cocoercivity constant \(\alpha_{\mu'}\), and the four points
\[
u=x_\mu(t),\quad u'=x_{\mu'}(t),\quad v=dx_\mu(t),\quad v'=dx_{\mu'}(t).
\]
That lemma gives
\[
\|v-v'\|^2+\|-\gamma v-A_{\mu'}u-(-\gamma v'-A_{\mu'}u')\|^2
\le \left(1+2\gamma^2+\frac{2}{\alpha_{\mu'}^2}\right)
\bigl(\|u-u'\|^2+\|v-v'\|^2\bigr).
\]
In the present notation this becomes
\[
\|z(t)\|^2+
\left\|-\gamma z(t)-\bigl(A_{\mu'}(x_\mu(t))-A_{\mu'}(x_{\mu'}(t))\bigr)\right\|^2
\le \left(1+2\gamma^2+\frac{2}{\alpha_{\mu'}^2}\right)w(t).
\]
Since \(m\) dominates the square root of the coefficient, the right side is at most \(m^2w(t)\). The proof then applies `two_pairing_le`, which states that for all \(a,b,c,d\in H\),
\[
\langle a,c\rangle+\langle b,d\rangle
\le \sqrt{\|a\|^2+\|b\|^2}\sqrt{\|c\|^2+\|d\|^2}.
\]
Taking
\[
a=y(t),\quad b=z(t),\quad c=z(t),\quad
d=-\gamma z(t)-\bigl(A_{\mu'}(x_\mu(t))-A_{\mu'}(x_{\mu'}(t))\bigr),
\]
the left side is exactly the inner-product expression above, and the right side is bounded by
\[
\sqrt{w(t)}\sqrt{\|z(t)\|^2+\|d\|^2}
\le \sqrt{w(t)}\cdot m\sqrt{w(t)}
=m\,w(t).
\]
Thus the desired pointwise bound is obtained.

Next, the proof uses the ODEs to rewrite the acceleration difference. From
\[
ddx_\mu(t)=-\gamma dx_\mu(t)-A_\mu(x_\mu(t)),\qquad
ddx_{\mu'}(t)=-\gamma dx_{\mu'}(t)-A_{\mu'}(x_{\mu'}(t)),
\]
one gets
\[
ddx_\mu(t)-ddx_{\mu'}(t)
=
\left(-\gamma z(t)-\bigl(A_{\mu'}(x_\mu(t))-A_{\mu'}(x_{\mu'}(t))\bigr)\right)
-\bigl(A_\mu(x_\mu(t))-A_{\mu'}(x_\mu(t))\bigr).
\]
The ball hypothesis gives \(\|x_\mu(t)\|\le r\), so the discrepancy bound yields
\[
\|A_\mu(x_\mu(t))-A_{\mu'}(x_\mu(t))\|\le D.
\]
Writing \(F=A_\mu(x_\mu(t))-A_{\mu'}(x_\mu(t))\), Cauchy-Schwarz gives
\[
-\langle z(t),F\rangle
\le \|z(t)\|\,\|F\|
\le \sqrt{w(t)}\,D
=D\,w(t)^{1/2}.
\]
Combining this with the previously proved bound on the first inner product gives
\[
\langle y(t),z(t)\rangle+\langle z(t),ddx_\mu(t)-ddx_{\mu'}(t)\rangle
\le m\,w(t)+D\,w(t)^{1/2}.
\]
Since \(w'(t)=2\) times that inner-product expression, this is equivalent to
\[
\left(1-\frac12\right)w'(t)\le m\,w(t)+D\,w(t)^{1/2}
\]
almost everywhere on \(0\le t\le T\). This is the differential inequality needed for the nonlinear Gronwall lemma.

The proof then applies `ext_lem_1`, which is the nonlinear Gronwall inequality `nonlinear_gronwall_inequality`. In the present specialization, \(t_0=0\), the final time is \(T\), the exponent parameter is \(\alpha=1/2\), \(a(t)=m\), and \(b(t)=D\). The lemma requires \(T>0\), \(0\le1/2<1\), absolute continuity of \(w\), nonnegativity of \(w\), integrability of the constant functions \(m\) and \(D\), nonnegativity of \(D\), and the differential inequality just proved. Its conclusion is that for every \(t\) with \(0\le t\le T\),
\[
w(t)^{1-1/2}\le w(0)^{1-1/2}\exp\left(\int_0^t m\,ds\right)
+\int_0^t \exp\left(\int_s^t m\,d\tau\right)D\,ds.
\]
Since \(1-1/2=1/2\), this becomes
\[
\sqrt{w(t)}
\le \sqrt{w(0)}e^{mt}
+\int_0^t e^{m(t-s)}D\,ds.
\]
The remaining integral is evaluated using `exp_kernel_integral`. With \(D=1\), that lemma gives
\[
\int_0^t e^{m(t-s)}\,ds=m^{-1}(e^{mt}-1).
\]
Therefore
\[
\sqrt{w(t)}
\le \sqrt{w(0)}e^{mt}+m^{-1}(e^{mt}-1)D.
\]
Substituting \(w(0)=\|u_{0,\mu}-u_{0,\mu'}\|^2+\|v_{0,\mu}-v_{0,\mu'}\|^2\) gives the corresponding bound in terms of the initial data.

Finally, the proof uses monotonicity in time. Since \(m\ge0\) and \(t\le T\), one has \(mt\le mT\), hence \(e^{mt}\le e^{mT}\). Since \(D\ge0\), the kernel term also satisfies
\[
m^{-1}(e^{mt}-1)D\le m^{-1}(e^{mT}-1)D.
\]
Also, because
\[
w(t)=\|y(t)\|^2+\|z(t)\|^2,
\]
one has
\[
\|x_\mu(t)-x_{\mu'}(t)\|=\|y(t)\|\le\sqrt{w(t)}.
\]
Combining these inequalities yields
\[
\|x_\mu(t)-x_{\mu'}(t)\|
\le \sqrt{\|u_{0,\mu}-u_{0,\mu'}\|^2+\|v_{0,\mu}-v_{0,\mu'}\|^2}e^{mT}
+m^{-1}(e^{mT}-1)D.
\]
Rewriting \(D=\operatorname{def}_6(r,hr,A_\mu,A_{\mu'})\) and rearranging the first product into the displayed order gives exactly the estimate stated in `thm_2`. The use of `filter_upwards` combines the almost-everywhere ODE, derivative, and ball hypotheses into a single almost-everywhere event, and the final `calc` block chains the norm bound, the Gronwall bound, the time-monotonicity step, and the final algebraic rewriting.

