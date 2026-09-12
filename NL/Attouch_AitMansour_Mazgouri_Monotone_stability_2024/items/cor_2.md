## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/cor_2.lean`

## Lean statement
```lean
theorem cor_2 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M)
    (Tmap : M → H → H) (γ : ℝ) (x dx ddx : M → ℝ → H)
    (u₀ v₀ : M → H) (θ₁ θ₂ : ℝ)
    (hcontr : ∀ μ ∈ V, ext_def_5 (Tmap μ))
    (hsol : ∀ μ ∈ V, ext_def_2 (fun u => u - Tmap μ u) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hθ₁ : 0 < θ₁) (hθ₂_pos : 0 < θ₂) (hθ₂_le : θ₂ ≤ 1)
    (h12 : ∀ u : H, ∀ μ ∈ V, ∀ μ' ∈ V, ‖Tmap μ u - Tmap μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂) :
    let m
```

## Statement explanation
The theorem `cor_2` is a stability corollary for a parameter-dependent family of contraction-type maps \(T_\mu\) on a real Hilbert space \(H\). The parameter space is a normed additive commutative group \(M\), and \(V \subseteq M\) is the set of admissible parameters. For each parameter \(\mu\), the map is
\[
T_\mu := \operatorname{Tmap}(\mu) : H \to H .
\]
The theorem studies the residual maps
\[
A_\mu(u) := u - T_\mu(u).
\]
The data \(x,dx,ddx : M \to \mathbb R \to H\) give, for each \(\mu\), three curves
\[
x_\mu := x(\mu),\qquad dx_\mu := dx(\mu),\qquad ddx_\mu := ddx(\mu).
\]
The initial data are \(u_0(\mu)\) and \(v_0(\mu)\), and \(\gamma,\theta_1,\theta_2\) are real constants.

The hypothesis `hcontr` says that for every \(\mu \in V\), the map \(T_\mu\) satisfies `ext_def_5`. The definition of `ext_def_5` is not included in the supplied context, but in the proof it is expanded into a constant \(c\), some conditions on \(c\), and a Lipschitz estimate
\[
\|T_\mu(z)-T_\mu(w)\| \le c\|z-w\|.
\]
The condition on \(c\) is then used to compare \(c\) with \(1\), so that \(T_\mu\) can be regarded as \(1\)-Lipschitz.

The hypothesis `hsol` says that for every \(\mu\in V\),
\[
\operatorname{ext\_def\_2}(A_\mu,\gamma,u_0(\mu),v_0(\mu),x_\mu,dx_\mu,ddx_\mu)
\]
holds, where \(A_\mu(u)=u-T_\mu(u)\). In the given context,
\[
\operatorname{ext\_def\_2}(A,\gamma,u_0,v_0,x,dx,ddx)
\]
means
\[
0<\gamma \;\land\; \operatorname{def\_3}(A,\gamma,u_0,v_0,x,dx,ddx).
\]
The inner predicate `def_3` is not unfolded in the proof; it is the actual solution property for the second-order problem associated with \(A\). Thus `hsol` says the given curves solve that problem for the residual operator \(I-T_\mu\), with initial data \(u_0(\mu),v_0(\mu)\).

The remaining hypotheses are
\[
0<\theta_1,\qquad 0<\theta_2,\qquad \theta_2\le 1,
\]
and the parameter-Hölder estimate
\[
\|T_\mu(u)-T_{\mu'}(u)\|
\le \theta_1\|\mu-\mu'\|^{\theta_2}
\]
for all \(u\in H\) and all \(\mu,\mu'\in V\).

The conclusion begins by setting
\[
m := \sqrt{1+2\gamma^2+8}.
\]
It then asserts two things.

First, for every \(\mu\in V\), there exists a solution triple
\[
(x_\mu,dx_\mu,ddx_\mu)
\]
for the residual problem \(A_\mu=I-T_\mu\), and any other solution \((y,dy,ddy)\) of the same problem agrees with \(x_\mu\) on the nonnegative half-line \(t\ge 0\). That is, the solution is unique on \([0,\infty)\).

Second, for every \(\mu,\mu'\in V\), for almost every \(t\in\mathbb R\) with respect to Lebesgue measure, if \(0\le t\), then
\[
\|x_\mu(t)-x_{\mu'}(t)\|
\le
e^{mt}
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+
\frac{\theta_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\theta_2}.
\]
This is a stability estimate: it bounds the distance between the two solution curves in terms of the differences in initial data and in the parameters.

## Lean proof
```lean
Real.sqrt (1 + 2 * γ ^ 2 + 8)
    (∀ μ ∈ V, ∃ x_μ dx_μ ddx_μ : ℝ → H,
      ext_def_2 (fun u => u - Tmap μ u) γ (u₀ μ) (v₀ μ) x_μ dx_μ ddx_μ ∧
        ∀ y dy ddy : ℝ → H,
          ext_def_2 (fun u => u - Tmap μ u) γ (u₀ μ) (v₀ μ) y dy ddy →
            Set.EqOn x_μ y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V, ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
      ‖x μ t - x μ' t‖ ≤ Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
        (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂) := by
  dsimp
  by_cases hV : V.Nonempty
  · rcases hV with ⟨μ₀, hμ₀⟩
    have hC₁ : ∀ μ ∈ V, 0 < (1 / 2 : ℝ) ∧ ∀ u v : H,
        (1 / 2 : ℝ) * ‖(u - Tmap μ u) - (v - Tmap μ v)‖ ^ 2 ≤
          inner ℝ ((u - Tmap μ u) - (v - Tmap μ v)) (u - v) := by
      intro μ hμ
      rcases hcontr μ hμ with ⟨c, hc0, hc1, hc⟩
      have hLip : LipschitzWith 1 (fun z : (Set.univ : Set H) => Tmap μ (z : H)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simp only [dist_eq_norm, Subtype.dist_eq]
        calc
          ‖Tmap μ (z : H) - Tmap μ (w : H)‖ ≤ c * ‖(z : H) - w‖ := by
            simpa only [dist_eq_norm, Subtype.dist_eq] using hc (z : H) (w : H)
          _ ≤ 1 * ‖(z : H) - w‖ := by
            gcongr
      have hresidual :=
        (lipschitzWith_one_iff_residualMap_cocoerciveOn_half
          (fun z : (Set.univ : Set H) => Tmap μ (z : H))).mp hLip
      have hpoint :=
        (CocoerciveOn.pointwise_iff (fun z : H => z - Tmap μ z)
          (1 / 2 : ℝ) (by norm_num)).mp (by simpa [residualMap] using hresidual)
      refine ⟨by norm_num, ?_⟩
      intro u v
      simpa using hpoint v u
    have hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
        ∀ u μ μ', μ ∈ V → μ' ∈ V →
          ‖(u - Tmap μ u) - (u - Tmap μ' u)‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂ := by
      refine ⟨hθ₁, hθ₂_pos, hθ₂_le, ?_⟩
      intro u μ μ' hμ hμ'
      have hres : (u - Tmap μ u) - (u - Tmap μ' u) =
          -(Tmap μ u - Tmap μ' u) := by abel
      rw [hres, norm_neg]
      exact h12 u μ hμ μ' hμ'
    have hmain := thm_1 V (fun μ u => u - Tmap μ u) γ u₀ v₀
      (fun _ => (1 / 2 : ℝ)) θ₁ θ₂ (hsol μ₀ hμ₀).1 hC₁ hC₂
    refine ⟨hmain.1, ?_⟩
    intro μ hμ μ' hμ'
    rcases hmain.2 μ hμ μ' hμ' with ⟨x₁, x₂, hx₁, hx₂, hbound⟩
    rcases hx₁ with ⟨dx₁, ddx₁, hx₁sol⟩
    rcases hx₂ with ⟨dx₂, ddx₂, hx₂sol⟩
    obtain ⟨z₁, dz₁, ddz₁, hz₁, hz₁uniq⟩ := hmain.1 μ hμ
    have hx₁eq : Set.EqOn (x μ) x₁ (Set.Ici 0) := fun t ht =>
      (hz₁uniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
        (hz₁uniq x₁ dx₁ ddx₁ hx₁sol ht)
    obtain ⟨z₂, dz₂, ddz₂, hz₂, hz₂uniq⟩ := hmain.1 μ' hμ'
    have hx₂eq : Set.EqOn (x μ') x₂ (Set.Ici 0) := fun t ht =>
      (hz₂uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
        (hz₂uniq x₂ dx₂ ddx₂ hx₂sol ht)
    have hrate : Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((1 / 2 : ℝ) ^ 2)) =
        Real.sqrt (1 + 2 * γ ^ 2 + 8) := by
      congr 1
      norm_num
    filter_upwards [hbound] with t ht
    intro ht_nonneg
    have ht_bound := ht ht_nonneg
    rw [← hx₁eq ht_nonneg, ← hx₂eq ht_nonneg] at ht_bound
    simpa only [max_self, hrate] using ht_bound
  · simp [Set.not_nonempty_iff_eq_empty.mp hV]
```

## Proof explanation
The proof begins with `dsimp`, which unfolds the let-bound constant \(m\) in the goal, replacing it by
\[
\sqrt{1+2\gamma^2+8}.
\]
Thus the target is now the two-conjunct statement with this explicit value of \(m\).

The proof then splits on whether \(V\) is nonempty using `by_cases hV : V.Nonempty`.

If \(V\) is empty, then `Set.not_nonempty_iff_eq_empty.mp hV` gives \(V=\emptyset\), and `simp` proves the whole conclusion vacuously: every statement quantified over \(\mu\in V\) or \(\mu,\mu'\in V\) is true because there are no such parameters.

So assume \(V\) is nonempty. The proof chooses a parameter \(\mu_0\in V\). This will be used only to extract \(0<\gamma\) from `hsol`, because `ext_def_2` contains \(0<\gamma\) as its first component.

Next the proof constructs the hypotheses needed for `thm_1`. The first is \(hC_1\), namely that for every \(\mu\in V\), the constant \(1/2\) is positive and the residual map \(A_\mu(u)=u-T_\mu(u)\) is \((1/2)\)-cocoercive:
\[
\frac12\|A_\mu(u)-A_\mu(v)\|^2
\le
\langle A_\mu(u)-A_\mu(v),u-v\rangle.
\]

To prove this, the proof fixes \(\mu\in V\). It expands `hcontr μ hμ` into a constant \(c\), its accompanying conditions, and the estimate
\[
\|T_\mu(z)-T_\mu(w)\| \le c\|z-w\|.
\]
Using `LipschitzWith.of_dist_le_mul`, it suffices to show that \(T_\mu\), viewed as a map from `Set.univ` to \(H\), is \(1\)-Lipschitz. The distance on the subtype is converted to the norm by `simp only [dist_eq_norm, Subtype.dist_eq]`. Then the proof uses a `calc` block:
\[
\|T_\mu(z)-T_\mu(w)\|
\le c\|z-w\|
\le 1\|z-w\|.
\]
The first inequality is the contraction estimate from `hcontr`. The second is handled by `gcongr`, using the available condition on \(c\) to compare \(c\) with \(1\). Hence \(T_\mu\) is \(1\)-Lipschitz.

The proof then applies the theorem
\[
\text{lipschitzWith\_one\_iff\_residualMap\_cocoerciveOn\_half}.
\]
That theorem states that a map \(T:D\to H\) is \(1\)-Lipschitz if and only if its residual map
\[
\operatorname{residualMap}(D,T)(x)=x-T(x)
\]
is \((1/2)\)-cocoercive on \(D\). Here \(D=\text{Set.univ}\) and \(T=T_\mu\). Since \(T_\mu\) has just been shown to be \(1\)-Lipschitz, the forward direction `.mp` gives that the residual map
\[
z\mapsto z-T_\mu(z)
\]
is \((1/2)\)-cocoercive on `Set.univ`.

The proof then uses `CocoerciveOn.pointwise_iff` to convert this set-level cocoercivity statement into a pointwise inequality over all \(x,y\in H\). The numerical side condition on \(1/2\) is discharged by `norm_num`. After unfolding `residualMap` via `simpa [residualMap]`, the obtained pointwise statement gives, for all \(x,y\in H\),
\[
\frac12\|(x-T_\mu x)-(y-T_\mu y)\|^2
\le
\langle (x-T_\mu x)-(y-T_\mu y),x-y\rangle.
\]
The proof then specializes this to \(x=v\) and \(y=u\), and `simpa` rewrites it into the required form for \(u,v\). This is exactly the cocoercivity inequality for \(A_\mu=I-T_\mu\) with constant \(1/2\). Thus \(hC_1\) is proved.

Next the proof establishes \(hC_2\), the parameter-Hölder condition for the residual maps. It packages the three inequalities
\[
0<\theta_1,\qquad 0<\theta_2,\qquad \theta_2\le 1
\]
directly from the hypotheses. Then for arbitrary \(u\in H\) and \(\mu,\mu'\in V\), it computes
\[
(u-T_\mu u)-(u-T_{\mu'}u)
=
-(T_\mu u-T_{\mu'}u).
\]
This algebraic identity is proved by `abel`. Rewriting with this identity and using `norm_neg`, the norm becomes
\[
\|T_\mu u-T_{\mu'}u\|.
\]
By `h12`, this is at most
\[
\theta_1\|\mu-\mu'\|^{\theta_2}.
\]
Thus \(hC_2\) holds.

Now the proof applies `thm_1`. The theorem `thm_1` says that if a family of maps \(A_\mu\) is uniformly cocoercive with positive constants \(\alpha(\mu)\), and is Hölder-continuous in the parameter \(\mu\), then solutions exist uniquely and satisfy a stability estimate. In the present application,
\[
A_\mu(u)=u-T_\mu(u),\qquad \alpha(\mu)=\frac12.
\]
The positivity of \(\gamma\) required by `thm_1` is extracted from `(hsol μ₀ hμ₀).1`, since `ext_def_2` contains \(0<\gamma\). The hypotheses \(hC_1\) and \(hC_2\) supply the cocoercivity and Hölder conditions. Therefore `thm_1` gives `hmain`.

The first conjunct of `hmain.1` is exactly the first conclusion of the theorem: for every \(\mu\in V\), there exists a solution triple for \(A_\mu=I-T_\mu\), and any other solution agrees with it on \([0,\infty)\). The proof uses `refine ⟨hmain.1, ?_⟩` to take this first conjunct directly and then focuses on the stability estimate.

For the stability estimate, fix \(\mu,\mu'\in V\). The second conjunct `hmain.2` gives two solution triples \(x_1,x_2\) for the parameters \(\mu,\mu'\), together with an almost-everywhere bound
\[
\|x_1(t)-x_2(t)\|
\le
e^{m_{\mathrm{thm}}t}
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+
\frac{\theta_1}{m_{\mathrm{thm}}}
(e^{m_{\mathrm{thm}}t}-1)\|\mu-\mu'\|^{\theta_2},
\]
where, from `thm_1`,
\[
m_{\mathrm{thm}}
=
\max\left(
\sqrt{1+2\gamma^2+\frac{2}{(1/2)^2}},
\sqrt{1+2\gamma^2+\frac{2}{(1/2)^2}}
\right).
\]

The proof must replace \(x_1,x_2\) by the originally given curves \(x_\mu,x_{\mu'}\). It does this using uniqueness. From `hmain.1 μ hμ`, it obtains a solution \(z_1\) and the uniqueness property that any solution agrees with \(z_1\) on \([0,\infty)\). Since \(x_\mu\) is a solution by `hsol μ hμ`, and \(x_1\) is a solution by `hx₁sol`, uniqueness gives
\[
x_\mu(t)=x_1(t)\qquad\text{for all }t\ge 0.
\]
The code obtains this by composing the equalities \(z_1=x_\mu\) and \(z_1=x_1\). Similarly, using `hmain.1 μ' hμ'`, it obtains
\[
x_{\mu'}(t)=x_2(t)\qquad\text{for all }t\ge 0.
\]

Next the proof simplifies the constants. Since
\[
\frac{2}{(1/2)^2}=8,
\]
we have
\[
\sqrt{1+2\gamma^2+\frac{2}{(1/2)^2}}
=
\sqrt{1+2\gamma^2+8}.
\]
The proof records this as `hrate`. The tactic `congr 1` reduces the equality of the two square roots to equality of their radicands, and `norm_num` proves the numerical identity.

Finally the proof proves the almost-everywhere inequality for \(x_\mu,x_{\mu'}\). It uses `filter_upwards [hbound]`, which means: it is enough to prove the desired inequality at every \(t\) where the previously obtained almost-everywhere bound `hbound` holds. For such a \(t\), it introduces the assumption \(0\le t\). Applying `hbound` gives the bound for \(x_1(t),x_2(t)\). Then `rw [← hx₁eq ht_nonneg, ← hx₂eq ht_nonneg] at ht_bound` rewrites \(x_1(t)\) to \(x_\mu(t)\) and \(x_2(t)\) to \(x_{\mu'}(t)\), using the equalities on \(t\ge0\). The result is the desired bound for \(x_\mu(t)\) and \(x_{\mu'}(t)\). The final `simpa only [max_self, hrate]` simplifies the maximum of the two equal constants to that common constant and replaces it by
\[
\sqrt{1+2\gamma^2+8},
\]
which is exactly the \(m\) from the statement. This completes the proof of the stability estimate.

