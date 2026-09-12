## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/thm_3.lean`

## Lean statement
```lean
theorem thm_3 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → SetValuedOperator H H)
    (hA : ∀ μ, μ ∈ V → (A μ).IsMaximalMonotone)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (γ lam ρ T : ℝ)
    (hlam : 0 < lam) (hρ : 0 < ρ) (hT : 0 < T)
    (hsol : ∀ μ (hμ : μ ∈ V), ext_def_2 (fun u : H => lam⁻¹ •
      (u - SetValuedOperator.resolventMap (A μ) (hA μ hμ) lam hlam u)) γ
      (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hball : ∀ μ, μ ∈ V → ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T → ‖x μ t‖ ≤ ρ) :
    ∀ μ (hμ : μ ∈ V), ∀ μ' (hμ' : μ' ∈ V),
      let m
```

## Statement explanation
The theorem proves a quantitative stability estimate for two solutions of a second-order differential inclusion after it has been regularized by Yosida approximations of maximal monotone operators.

Let $H$ be a real Hilbert space and let $M$ be a parameter type. A parameter is chosen from a set $V\subseteq M$. For each parameter $\mu\in V$, the map $A_\mu:H\to 2^H$ is a set-valued operator which is assumed to be maximal monotone. For $\lambda\gt 0$, let

$$
J_\lambda^{A_\mu}=(I+\lambda A_\mu)^{-1}
$$

be the resolvent of $A_\mu$, and let

$$
Y_\mu(u)=\lambda^{-1}\bigl(u-J_\lambda^{A_\mu}u\bigr)
$$

be the corresponding Yosida approximation. For each $\mu\in V$, the theorem is given functions $x_\mu,dx_\mu,ddx_\mu:\mathbb R\to H$, and initial data $u_0(\mu),v_0(\mu)\in H$. The hypothesis `hsol` says that the triple $(x_\mu,dx_\mu,ddx_\mu)$ solves, in the sense of `ext_def_2`, the second-order Cauchy problem associated with the regularized operator $Y_\mu$, namely $dx_\mu$ is the derivative of $x_\mu$, $ddx_\mu$ is the derivative of $dx_\mu$, the initial conditions are

$$
x_\mu(0)=u_0(\mu),\qquad dx_\mu(0)=v_0(\mu),
$$

and almost everywhere the differential inclusion becomes the equation

```math
ddx_\mu(t)+\gamma\,dx_\mu(t)+Y_\mu(x_\mu(t))=0.
```

The constants satisfy $\lambda\gt 0$, $\rho\gt 0$, and $T\gt 0$. The hypothesis `hball` says that, for almost every $t\in[0,T]$,

```math
\|x_\mu(t)\|\le \rho.
```

Thus both trajectories under comparison are assumed to remain in the closed ball of radius $\rho$ on the time interval $[0,T]$.

The conclusion concerns any two parameters $\mu,\mu'\in V$. Define

$$
m=\sqrt{1+2\gamma^2+\frac{2}{\lambda^2}}.
$$

Let

```math
d_{\lambda,\rho}(A_\mu,A_{\mu'})
=\sup_{\|u\|\le \rho}
\left\|J_\lambda^{A_\mu}u-J_\lambda^{A_{\mu'}}u\right\|
```

be the resolvent distance `def_7` between the two maximal monotone operators. Then the theorem states that for almost every $t\in[0,T]$,

```math
\|x_\mu(t)-x_{\mu'}(t)\|
\le
e^{mT}
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+(\lambda m)^{-1}(e^{mT}-1)\,d_{\lambda,\rho}(A_\mu,A_{\mu'}).
```

So the distance between the two trajectories is controlled by the distance between their initial positions and velocities, plus the resolvent distance between the two operators, with an exponential factor in time.

## Lean proof
```lean
Real.sqrt (1 + 2 * γ ^ 2 + 2 / (lam ^ 2))
      let d_lambda_rho := def_7 (A μ) (A μ') (hA μ hμ) (hA μ' hμ')
        lam ρ hlam hρ
      ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
        ‖x μ t - x μ' t‖ ≤ Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (lam * m)⁻¹ * (Real.exp (m * T) - 1) * d_lambda_rho := by
  intro μ hμ μ' hμ'
  dsimp
  let Y : H → H := fun u => lam⁻¹ • (u - SetValuedOperator.resolventMap (A μ) (hA μ hμ) lam hlam u)
  let Y' : H → H := fun u => lam⁻¹ • (u - SetValuedOperator.resolventMap (A μ') (hA μ' hμ') lam hlam u)
  have hco : ∀ u v : H, lam * ‖Y u - Y v‖ ^ 2 ≤ inner ℝ (Y u - Y v) (u - v) := by
    intro u v
    simpa [Y, real_inner_comm] using (SetValuedOperator.yosida_is_cocoercive (A μ) (hA μ hμ) lam hlam).1.ineq
      ⟨u, Set.mem_univ _⟩ ⟨v, Set.mem_univ _⟩
  have hco' : ∀ u v : H, lam * ‖Y' u - Y' v‖ ^ 2 ≤ inner ℝ (Y' u - Y' v) (u - v) := by
    intro u v
    simpa [Y', real_inner_comm] using (SetValuedOperator.yosida_is_cocoercive (A μ') (hA μ' hμ') lam hlam).1.ineq
      ⟨u, Set.mem_univ _⟩ ⟨v, Set.mem_univ _⟩
  obtain ⟨_, hxACμ, hdxACμ, hx0μ, hdx0μ, hodeμ, hxderivμ, hdxderivμ⟩ :=
    thm_3_solution_data hT (hsol μ hμ)
  obtain ⟨_, hxACμ', hdxACμ', hx0μ', hdx0μ', hodeμ', hxderivμ', hdxderivμ'⟩ :=
    thm_3_solution_data hT (hsol μ' hμ')
  have hD_bdd : BddAbove {q : ℝ | ∃ u : H, ‖u‖ ≤ ρ ∧ q = ‖Y u - Y' u‖} := by
    let LY := thm_3_cocoercive_lipschitz hlam hco
    let LY' := thm_3_cocoercive_lipschitz hlam hco'
    refine ⟨lam⁻¹ * ρ + ‖Y 0 - Y' 0‖ + lam⁻¹ * ρ, ?_⟩
    rintro q ⟨u, hu, rfl⟩
    calc
      ‖Y u - Y' u‖ = ‖(Y u - Y 0) + (Y 0 - Y' 0) + (Y' 0 - Y' u)‖ := by congr 1; abel
      _ ≤ ‖Y u - Y 0‖ + ‖Y 0 - Y' 0‖ + ‖Y' 0 - Y' u‖ := norm_add_le _ _ |>.trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ lam⁻¹ * ρ + ‖Y 0 - Y' 0‖ + lam⁻¹ * ρ := by
        have hYu : ‖Y u - Y 0‖ ≤ lam⁻¹ * ρ := by
          simpa using (LY u 0).trans (mul_le_mul_of_nonneg_left (by simpa using hu) (inv_nonneg.mpr hlam.le))
        have hYu' : ‖Y' 0 - Y' u‖ ≤ lam⁻¹ * ρ := by
          simpa using (LY' 0 u).trans (mul_le_mul_of_nonneg_left (by simpa using hu) (inv_nonneg.mpr hlam.le))
        linarith
  let D : ℝ := lam⁻¹ * def_7 (A μ) (A μ') (hA μ hμ) (hA μ' hμ') lam ρ hlam hρ
  have hD_bound : ∀ ⦃u : H⦄, ‖u‖ ≤ ρ → ‖Y u - Y' u‖ ≤ D := by
    intro u hu
    have hs := le_csSup hD_bdd ⟨u, hu, rfl⟩
    have hne : lam ≠ 0 := ne_of_gt hlam
    change ‖Y u - Y' u‖ ≤ lam⁻¹ * (lam * sSup {q : ℝ | ∃ v : H, ‖v‖ ≤ ρ ∧ q = ‖Y v - Y' v‖})
    calc
      _ ≤ sSup {q : ℝ | ∃ v : H, ‖v‖ ≤ ρ ∧ q = ‖Y v - Y' v‖} := hs
      _ = _ := by field_simp [hne]
  have hD0 : 0 ≤ D := by
    have := hD_bound (u := (0 : H)) (by simpa using hρ.le)
    exact (norm_nonneg _).trans this
  let y : ℝ → H := fun t => x μ t - x μ' t
  let z : ℝ → H := fun t => dx μ t - dx μ' t
  let w : ℝ → ℝ := fun t => ‖y t‖ ^ 2 + ‖z t‖ ^ 2
  have hyAC : AbsolutelyContinuousOnInterval y 0 T := by simpa [y] using hxACμ.fun_sub hxACμ'
  have hzAC : AbsolutelyContinuousOnInterval z 0 T := by simpa [z] using hdxACμ.fun_sub hdxACμ'
  have hwAC : AbsolutelyContinuousOnInterval w 0 T := by simpa [w] using (thm_3_ac_norm_sq hyAC).fun_add (thm_3_ac_norm_sq hzAC)
  have hw_nonneg : ∀ t, 0 ≤ w t := by intro t; dsimp [w]; positivity
  have hw0 : w 0 = ‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2 := by simp [w, y, z, hx0μ, hx0μ', hdx0μ, hdx0μ']
  have hwDeriv : ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt w (2 * inner ℝ (y t) (z t) + 2 * inner ℝ (z t) (ddx μ t - ddx μ' t)) t := by
    filter_upwards [hxderivμ, hxderivμ', hdxderivμ, hdxderivμ'] with t hx hx' hdx hdx'
    intro ht
    have hyD : HasDerivAt y (z t) t := by simpa [y, z] using (hx ht).sub (hx' ht)
    have hzD : HasDerivAt z (ddx μ t - ddx μ' t) t := by simpa [z] using (hdx ht).sub (hdx' ht)
    simpa [w] using hyD.norm_sq.add hzD.norm_sq
  let m := Real.sqrt (1 + 2 * γ ^ 2 + 2 / lam ^ 2)
  have hmone : 1 ≤ m := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 2 / lam ^ 2 := by positivity
    nlinarith [sq_nonneg γ]
  have hm0 : 0 ≤ m := by linarith
  have hm : 0 < m := by linarith
  have hfixed (t : ℝ) : inner ℝ (y t) (z t) + inner ℝ (z t) (-γ • z t - (Y' (x μ t) - Y' (x μ' t))) ≤ m * w t := by
    have hb := thm_3_first_order_sq_bound (gamma := γ) hlam hco' (x μ t) (x μ' t) (dx μ t) (dx μ' t)
    have hb' : ‖z t‖ ^ 2 + ‖-γ • z t - (Y' (x μ t) - Y' (x μ' t))‖ ^ 2 ≤ m ^ 2 * w t := by
      rw [show -γ • dx μ t - Y' (x μ t) - (-γ • dx μ' t - Y' (x μ' t)) = -γ • (dx μ t - dx μ' t) - (Y' (x μ t) - Y' (x μ' t)) by module] at hb
      have hsq : m ^ 2 = 1 + 2 * γ ^ 2 + 2 / lam ^ 2 := Real.sq_sqrt (by positivity)
      simpa [z, w, hsq] using hb
    have hp := thm_3_two_pairing_le (y t) (z t) (z t) (-γ • z t - (Y' (x μ t) - Y' (x μ' t)))
    have hs := Real.sqrt_le_sqrt hb'
    rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq_eq_abs, abs_of_nonneg hm0] at hs
    have hwr : Real.sqrt (w t) ^ 2 = w t := Real.sq_sqrt (hw_nonneg t)
    calc
      _ ≤ Real.sqrt (‖y t‖ ^ 2 + ‖z t‖ ^ 2) * Real.sqrt (‖z t‖ ^ 2 + ‖-γ • z t - (Y' (x μ t) - Y' (x μ' t))‖ ^ 2) := hp
      _ ≤ Real.sqrt (w t) * (m * Real.sqrt (w t)) := by simpa [w] using mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
      _ = m * w t := by nlinarith [hwr]
  have hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc (0 : ℝ) T →
      (1 - (1 / 2 : ℝ)) * deriv w t ≤ m * w t + D * w t ^ (1 / 2 : ℝ) := by
    filter_upwards [hodeμ, hodeμ', hwDeriv, hball μ hμ] with t ho ho' hd hb
    intro ht
    have hddx : ddx μ t - ddx μ' t = (-γ • z t - (Y' (x μ t) - Y' (x μ' t))) - (Y (x μ t) - Y' (x μ t)) := by
      have h1 : ddx μ t = -γ • dx μ t - Y (x μ t) := by
        calc ddx μ t = -(γ • dx μ t + Y (x μ t)) := eq_neg_of_add_eq_zero_left (by simpa [add_assoc, Y] using ho ht.1)
             _ = _ := by module
      have h2 : ddx μ' t = -γ • dx μ' t - Y' (x μ' t) := by
        calc ddx μ' t = -(γ • dx μ' t + Y' (x μ' t)) := eq_neg_of_add_eq_zero_left (by simpa [add_assoc, Y'] using ho' ht.1)
             _ = _ := by module
      rw [h1, h2]
      dsimp [z]
      module
    have hf : ‖Y (x μ t) - Y' (x μ t)‖ ≤ D := hD_bound (hb ht)
    have hz : ‖z t‖ ≤ Real.sqrt (w t) := by
      apply Real.le_sqrt_of_sq_le
      dsimp [w]
      nlinarith [sq_nonneg ‖y t‖]
    have hforce : -inner ℝ (z t) (Y (x μ t) - Y' (x μ t)) ≤ D * Real.sqrt (w t) := by
      calc
        _ ≤ ‖z t‖ * ‖Y (x μ t) - Y' (x μ t)‖ := le_trans (le_abs_self _) (by simpa using norm_inner_le_norm (𝕜 := ℝ) (z t) (Y (x μ t) - Y' (x μ t)))
        _ ≤ D * Real.sqrt (w t) := by
          calc
            _ ≤ ‖z t‖ * D := mul_le_mul_of_nonneg_left hf (norm_nonneg _)
            _ ≤ Real.sqrt (w t) * D := mul_le_mul_of_nonneg_right hz hD0
            _ = _ := by ring
    have he : inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t) =
        (inner ℝ (y t) (z t) + inner ℝ (z t) (-γ • z t - (Y' (x μ t) - Y' (x μ' t)))) - inner ℝ (z t) (Y (x μ t) - Y' (x μ t)) := by
      rw [hddx]
      simp only [inner_sub_right]
      ring
    have hd' : deriv w t = 2 * (inner ℝ (y t) (z t) + inner ℝ (z t) (ddx μ t - ddx μ' t)) := by rw [(hd ht.1).deriv]; ring
    rw [hd', he, ← Real.sqrt_eq_rpow]
    nlinarith [hfixed t, hforce]
  have hg := ext_lem_1 (w := w) (a := fun _ : ℝ => m) (b := fun _ : ℝ => D)
    (t₀ := 0) (T := T) (α := (1 / 2 : ℝ)) hT (by norm_num) (by norm_num)
    (by simpa using hwAC) (by intro t _; exact hw_nonneg t) (by simp) (by simp)
    (Filter.Eventually.of_forall (fun _ _ => hD0)) (by simpa using hineq)
  filter_upwards with t ht
  have ht0 := ht.1
  have htT := ht.2
  have hgr := hg t ht0 (by simpa using htT)
  norm_num at hgr
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hw0] at hgr
  have hk : (∫ s in 0..t, Real.exp ((t - s) * m)) = m⁻¹ * (Real.exp (m * t) - 1) := by
    calc
      _ = ∫ s in 0..t, Real.exp (m * (t - s)) * 1 := by apply intervalIntegral.integral_congr_ae; filter_upwards with s hs; ring
      _ = _ := by simpa using thm_3_exp_kernel_integral m 1 t hm
  rw [hk] at hgr
  have hgr' : Real.sqrt (w t) ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) + m⁻¹ * (Real.exp (m * t) - 1) * D := by
    convert hgr using 1
    all_goals ring
  have hexp : Real.exp (m * t) ≤ Real.exp (m * T) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hm0)
  have hker : m⁻¹ * (Real.exp (m * t) - 1) * D ≤ m⁻¹ * (Real.exp (m * T) - 1) * D := by
    have hs := sub_le_sub_right hexp 1
    have hp : 0 ≤ m⁻¹ * D := mul_nonneg (inv_nonneg.mpr hm0) hD0
    nlinarith [mul_le_mul_of_nonneg_left hs hp]
  have hy : ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := by
    change ‖y t‖ ≤ _
    apply Real.le_sqrt_of_sq_le
    dsimp [w]
    nlinarith [sq_nonneg ‖z t‖]
  calc
    ‖x μ t - x μ' t‖ ≤ Real.sqrt (w t) := hy
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * t) + m⁻¹ * (Real.exp (m * t) - 1) * D := hgr'
    _ ≤ Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) * Real.exp (m * T) + m⁻¹ * (Real.exp (m * T) - 1) * D :=
      add_le_add (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)) hker
    _ = Real.exp (m * T) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) + (lam * m)⁻¹ * (Real.exp (m * T) - 1) * def_7 (A μ) (A μ') (hA μ hμ) (hA μ' hμ') lam ρ hlam hρ := by
      dsimp [D]
      field_simp [ne_of_gt hlam, ne_of_gt hm]
```

## Proof explanation
The proof begins with `intro μ hμ μ' hμ'`, which fixes arbitrary parameters $\mu,\mu'\in V$. The `dsimp` step unfolds the `let` abbreviations in the goal so that the estimate can be proved directly.

Next the proof defines the two Yosida approximations

$$
Y(u)=\lambda^{-1}\bigl(u-J_\lambda^{A_\mu}u\bigr),
\qquad
Y'(u)=\lambda^{-1}\bigl(u-J_\lambda^{A_{\mu'}}u\bigr).
$$

The cited theorem `SetValuedOperator.yosida_is_cocoercive` says that if $T$ is maximal monotone and $\lambda\gt 0$, then its Yosida approximation $u\mapsto \lambda^{-1}(u-J_\lambda^T u)$ is cocoercive with constant $\lambda$:

```math
\lambda\|Y_\lambda^T u-Y_\lambda^T v\|^2
\le
\langle Y_\lambda^T u-Y_\lambda^T v,u-v\rangle.
```

The proof applies this to $A_\mu$ and $A_{\mu'}$, obtaining the two inequalities

```math
\lambda\|Y u-Y v\|^2
\le
\langle Y u-Y v,u-v\rangle,
\qquad
\lambda\|Y' u-Y' v\|^2
\le
\langle Y' u-Y' v,u-v\rangle.
```

These are the assumptions `hco` and `hco'`.

The proof then applies `thm_3_solution_data` to the solution hypotheses for $\mu$ and for $\mu'$. That cited result extracts from `ext_def_2` the following consequences: $x_\mu$ and $dx_\mu$ are absolutely continuous on $[0,T]$, the initial conditions $x_\mu(0)=u_0(\mu)$ and $dx_\mu(0)=v_0(\mu)$ hold, almost everywhere the equation

```math
ddx_\mu+\gamma\,dx_\mu+Y(x_\mu)=0
```

holds on $t\ge 0$, and almost everywhere $x_\mu$ has derivative $dx_\mu$ while $dx_\mu$ has derivative $ddx_\mu$. The same consequences are obtained for $x_{\mu'},dx_{\mu'},ddx_{\mu'}$, with $Y'$ in place of $Y$.

The next step controls the Yosida approximation distance over the ball of radius $\rho$. The proof defines

$$
D=\lambda^{-1}d_{\lambda,\rho}(A_\mu,A_{\mu'}).
$$

Since

$$
Y u-Y' u
=\lambda^{-1}\bigl(J_\lambda^{A_{\mu'}}u-J_\lambda^{A_\mu}u\bigr),
$$

the quantity $D$ is the supremum of $`\|Y u-Y' u\|`$over$`\|u\|\le \rho`$. The proof first shows that this supremum is finite. It applies `thm_3_cocoercive_lipschitz` to `hco` and to `hco'`. That lemma says that if $a\gt 0$ and

```math
a\|B u-B v\|^2\le \langle B u-B v,u-v\rangle,
```

then

```math
\|B u-B v\|\le a^{-1}\|u-v\|.
```

Taking $a=\lambda$, it follows that both $Y$ and $Y'$ are Lipschitz with constant $\lambda^{-1}$. For any $u$ with $`\|u\|\le \rho`$, the triangle inequality gives

```math
\|Y u-Y' u\|
=\|(Y u-Y0)+(Y0-Y'0)+(Y'0-Y'u)\|
\le
\|Y u-Y0\|+\|Y0-Y'0\|+\|Y'0-Y'u\|.
```

Using the Lipschitz bounds and $`\|u\|\le \rho`$, this is at most

```math
\lambda^{-1}\rho+\|Y0-Y'0\|+\lambda^{-1}\rho.
```

Therefore the set of values $`\|Y u-Y' u\|`$ over the ball is bounded above. The `le_csSup` step then gives, for every $u$ with $`\|u\|\le \rho`$,

```math
\|Y u-Y' u\|\le D.
```

In particular, taking $u=0$ shows $D\ge 0$.

Now the proof defines the difference functions

```math
y(t)=x_\mu(t)-x_{\mu'}(t),
\qquad
z(t)=dx_\mu(t)-dx_{\mu'}(t),
\qquad
w(t)=\|y(t)\|^2+\|z(t)\|^2.
```

Because $x_\mu$ and $x_{\mu'}$ are absolutely continuous, their difference $y$ is absolutely continuous. Similarly $z$ is absolutely continuous. The cited lemma `thm_3_ac_norm_sq` says that if a function is absolutely continuous on $[0,T]$, then the square of its norm is also absolutely continuous. Applying this to $y$ and to $z$, and then using that sums of absolutely continuous functions are absolutely continuous, gives that $w$ is absolutely continuous on $[0,T]$. Since $w$ is a sum of squares, $w(t)\ge 0$ for every $t$. The initial value is

```math
w(0)=\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2.
```

The proof also computes the derivative of $w$. Almost everywhere, $x_\mu$ and $x_{\mu'}$ have derivatives $dx_\mu$ and $dx_{\mu'}$, while $dx_\mu$ and $dx_{\mu'}$ have derivatives $ddx_\mu$ and $ddx_{\mu'}$. Hence

$$
y'=z,
\qquad
z'=ddx_\mu-ddx_{\mu'}.
$$

Using the derivative of the squared norm, the proof obtains almost everywhere

$$
w'(t)
=2\langle y(t),z(t)\rangle
+2\langle z(t),ddx_\mu(t)-ddx_{\mu'}(t)\rangle.
$$

Next the proof defines

$$
m=\sqrt{1+2\gamma^2+\frac{2}{\lambda^2}}.
$$

Since the expression under the square root is at least $1$, one has $m\ge 1$, hence $m\gt 0$.

A key pointwise inequality is then established:

$$
\langle y,z\rangle
+\left\langle z,-\gamma z-\bigl(Y'(x_\mu)-Y'(x_{\mu'})\bigr)\right\rangle
\le
m w.
$$

This uses `thm_3_first_order_sq_bound`. That lemma says that if $A$ is $\alpha$-cocoercive with $\alpha\gt 0$, then for all $u,u',v,v'$,

```math
\|v-v'\|^2
+\left\|-\gamma v-A u-(-\gamma v'-A u')\right\|^2
\le
\left(1+2\gamma^2+\frac{2}{\alpha^2}\right)
\bigl(\|u-u'\|^2+\|v-v'\|^2\bigr).
```

The proof applies it with $A=Y'$, $\alpha=\lambda$, $u=x_\mu$, $u'=x_{\mu'}$, $v=dx_\mu$, and $v'=dx_{\mu'}$. Since $z=dx_\mu-dx_{\mu'}$, this gives

```math
\|z\|^2+
\left\|-\gamma z-\bigl(Y'(x_\mu)-Y'(x_{\mu'})\bigr)\right\|^2
\le
m^2 w.
```

The proof then invokes `thm_3_two_pairing_le`, which is the Cauchy–Schwarz-type inequality

```math
\langle a,c\rangle+\langle b,d\rangle
\le
\sqrt{\|a\|^2+\|b\|^2}
\sqrt{\|c\|^2+\|d\|^2}.
```

Taking

$$
a=y,\qquad b=z,\qquad c=z,\qquad
d=-\gamma z-\bigl(Y'(x_\mu)-Y'(x_{\mu'})\bigr),
$$

the first square root is $\sqrt w$, and the second is at most $m\sqrt w$ by the previous bound. Multiplying gives the desired inequality by $mw$.

The proof then derives the differential inequality for $w$. From the two regularized equations,

$$
ddx_\mu=-\gamma dx_\mu-Y(x_\mu),
\qquad
ddx_{\mu'}=-\gamma dx_{\mu'}-Y'(x_{\mu'}),
$$

one obtains

$$
ddx_\mu-ddx_{\mu'}
=-\gamma z-\bigl(Y'(x_\mu)-Y'(x_{\mu'})\bigr)
-\bigl(Y(x_\mu)-Y'(x_\mu)\bigr).
$$

Substituting this into the formula for $w'$, the proof gets

$$
w'
=2\left[
\langle y,z\rangle
+\left\langle z,-\gamma z-\bigl(Y'(x_\mu)-Y'(x_{\mu'})\bigr)\right\rangle
\right]
-2\langle z,Y(x_\mu)-Y'(x_\mu)\rangle.
$$

Since $`\|x_\mu(t)\|\le \rho`$almost everywhere on$[0,T]$, the bound on$Y-Y'$over the$\rho$-ball gives

```math
\|Y(x_\mu(t))-Y'(x_\mu(t))\|\le D.
```

Using Cauchy–Schwarz,

```math
-\langle z,Y(x_\mu)-Y'(x_\mu)\rangle
\le
\|z\|\,\|Y(x_\mu)-Y'(x_\mu)\|
\le
D\sqrt{w}.
```

Combined with the earlier pointwise inequality, this yields

$$
\frac12 w'
\le
m w+D w^{1/2}.
$$

Equivalently,

$$
\left(1-\frac12\right)w'
\le
m w+D w^{1/2}.
$$

Now the proof applies `ext_lem_1`, the nonlinear Gronwall inequality. Its visible content is: if $w$ is absolutely continuous, $w\ge 0$, $a,b$ are integrable, $b\ge 0$ almost everywhere, and for almost every $t\in[0,T]$,

$$
(1-\alpha)w'(t)\le a(t)w(t)+b(t)w(t)^\alpha,
$$

with $0\le \alpha\lt 1$, then for every $t\in[0,T]$,

```math
w(t)^{1-\alpha}
\le
w(0)^{1-\alpha}\exp\left(\int_0^t a\right)
+\int_0^t
\exp\left(\int_s^t a\right)b(s)\,ds.
```

The proof takes $\alpha=\frac12$, $a(t)=m$, and $b(t)=D$. It obtains

```math
\sqrt{w(t)}
\le
\sqrt{w(0)}\,e^{mt}
+\int_0^t e^{m(t-s)}D\,ds.
```

The cited lemma `thm_3_exp_kernel_integral` evaluates the exponential convolution:

```math
\int_0^t e^{m(t-s)}D\,ds
=m^{-1}(e^{mt}-1)D.
```

Thus

```math
\sqrt{w(t)}
\le
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}\,e^{mt}
+m^{-1}(e^{mt}-1)D.
```

Finally, since $t\le T$ and $m\ge 0$,

$$
e^{mt}\le e^{mT}.
$$

Also $m^{-1}(e^{mt}-1)D\le m^{-1}(e^{mT}-1)D$ because $m^{-1}D\ge 0$. Therefore

```math
\sqrt{w(t)}
\le
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}\,e^{mT}
+m^{-1}(e^{mT}-1)D.
```

Since

```math
\|x_\mu(t)-x_{\mu'}(t)\|=\|y(t)\|\le \sqrt{w(t)},
```

and since $D=\lambda^{-1}d_{\lambda,\rho}(A_\mu,A_{\mu'})$, the last term becomes

$$
m^{-1}(e^{mT}-1)D
=(\lambda m)^{-1}(e^{mT}-1)d_{\lambda,\rho}(A_\mu,A_{\mu'}).
$$

Reordering the first term gives exactly the claimed estimate. The final `field_simp` uses $\lambda\ne 0$ and $m\ne 0$ to simplify the rational coefficient.

