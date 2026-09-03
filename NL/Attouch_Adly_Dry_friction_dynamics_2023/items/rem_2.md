## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/rem_2.lean`

## Lean statement
```lean
theorem remark_4_1 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {sbar α : ℝ}
    (x y dx : ℝ → H) (xLimit : H)
    (hα : 1 < α) (hpositiveTime : 0 < sbar)
    (haverage : ∀ s ∈ Set.Ici sbar, HasDerivAt x (dx s) s ∧
      dx s + ((α - 1) / s) • (x s - y s) = 0)
    (hstab : ∀ s ∈ Set.Ici sbar, y s = xLimit) :
    ∃ C : H, ∀ s ∈ Set.Ici sbar, x s = xLimit + (Real.rpow s (α - 1))⁻¹ • C
```

## Statement explanation
Let \(H\) be a type with the structure of an additive normed commutative group and a normed real vector space over \(\mathbb R\). Let \(sbar,\alpha\) be real numbers, and let \(x,y,dx\) be functions from \(\mathbb R\) to \(H\). Let \(xLimit\) be an element of \(H\).

The assumptions are:

- \(hα : 1 < α\).
- \(hpositiveTime : 0 < sbar\).
- \(haverage :\) for every \(s \in \operatorname{Set.Ici} sbar\), meaning every \(s \ge sbar\), both
  1. \(x\) has derivative \(dx(s)\) at \(s\), written \(\operatorname{HasDerivAt} x (dx s) s\);
  2. the vector equation
     \[
     dx(s) + \frac{\alpha-1}{s}\bigl(x(s)-y(s)\bigr) = 0
     \]
     holds.
- \(hstab :\) for every \(s \ge sbar\), \(y(s) = xLimit\).

The conclusion is:
\[
\exists C : H,\ \forall s \in \mathbb R,\ s \ge sbar \Rightarrow
x(s) = xLimit + \bigl(s^{\alpha-1}\bigr)^{-1}\bullet C.
\]
Here \(\operatorname{Real.rpow} s (\alpha-1)\) denotes the real power \(s^{\alpha-1}\), the symbol \(\bullet\) denotes scalar multiplication by a real number on \(H\), and \((s^{\alpha-1})^{-1}\) is its multiplicative inverse as a real number.

## Lean proof
```lean
by
  have _hp : 0 < α - 1 := sub_pos.mpr hα
  let F : ℝ → H := fun t => Real.rpow t (α - 1) • (x t - xLimit)
  have hFzero : ∀ s ∈ Set.Ici sbar, HasDerivAt F 0 s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hpositiveTime hs
    have havg := haverage s hs
    rw [hstab s hs] at havg
    exact integrating_factor_deriv_zero hspos havg.1 havg.2
  refine ⟨F sbar, ?_⟩
  intro s hs
  have hdiff : ∀ t ∈ Set.Ici sbar, DifferentiableWithinAt ℝ F (Set.Ici sbar) t := by
    intro t ht
    exact (hFzero t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ Set.Ici sbar, fderivWithin ℝ F (Set.Ici sbar) t = 0 := by
    intro t ht
    simpa using HasFDerivWithinAt.fderivWithin
      (hFzero t ht).hasDerivWithinAt.hasFDerivWithinAt (uniqueDiffOn_Ici sbar t ht)
  have hF : F s = F sbar :=
    (convex_Ici sbar).is_const_of_fderivWithin_eq_zero hdiff hderiv
      hs (Set.mem_Ici.mpr le_rfl)
  have hspos : 0 < s := lt_of_lt_of_le hpositiveTime hs
  have hpow_ne : Real.rpow s (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hspos (α - 1)).ne'
  have hdiv := congrArg (fun v : H => (Real.rpow s (α - 1))⁻¹ • v) hF
  change x s = xLimit + (Real.rpow s (α - 1))⁻¹ • F sbar
  rw [show F s = Real.rpow s (α - 1) • (x s - xLimit) from rfl] at hdiv
  change (Real.rpow s (α - 1))⁻¹ • (Real.rpow s (α - 1) • (x s - xLimit)) =
    (Real.rpow s (α - 1))⁻¹ • F sbar at hdiv
  rw [smul_smul, inv_mul_cancel₀ hpow_ne, one_smul] at hdiv
  exact sub_eq_iff_eq_add'.mp hdiv
```

## Proof explanation
The proof starts by obtaining a positive exponent:
\[
have\ {\_hp}: 0 < \alpha - 1 := sub\_pos.mpr hα,
\]
which rewrites the hypothesis \(1<\alpha\) into \(0<\alpha-1\).

Next it defines
\[
F(t) = \operatorname{Real.rpow} t (\alpha-1)\bullet (x(t)-xLimit).
\]
This is the intended “integrating factor” adjustment of \(x(t)-xLimit\).

The first key claim is \(hFzero\): for every \(s \ge sbar\), \(F\) has derivative \(0\) at \(s\). The proof fixes \(s\) with \(s\ge sbar\). From \(0<sbar\le s\) it derives \(0<s\). It applies \(haverage\) at this \(s\), yielding both \(\operatorname{HasDerivAt} x (dx s) s\) and
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-y(s)\bigr)=0.
\]
Using \(hstab\), it rewrites \(y(s)\) to \(xLimit\), so the equation becomes
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-xLimit\bigr)=0.
\]
The declaration then applies the helper lemma `integrating_factor_deriv_zero` to conclude exactly that \(F\) has derivative zero at \(s\). This helper is the mathematical fact that this particular differential equation for \(x\) is equivalent to the vanishing derivative of the factored expression \(F\).

The next part proves that \(F\) is constant on the whole interval \([sbar,\infty)\). The proof first notes \(hdiff\): at each \(t\ge sbar\), \(F\) is differentiable within the set \(\{s \mid sbar \le s\}\), because it actually has a full derivative at \(t\). Then it defines \(hderiv\): the derivative within that interval is zero at each such \(t\). This follows from having derivative zero at \(t\), using `HasFDerivWithinAt.fderivWithin` together with the fact that the interval has a unique derivative direction at every point. Then the proof invokes the theorem
\[
(convex\_Ici sbar).is\_const\_of\_fderivWithin\_eq\_zero
\]
with the differentiability data, the zero derivative data, and the two points \(s\) and \(sbar\). Since the interval is convex and \(F\) is differentiable on it with zero derivative, \(F\) is constant, giving
\[
F(s)=F(sbar).
\]

With this equality in hand, the rest is algebraic manipulation. Since \(s\ge sbar>0\), the base \(s\) is positive, hence
\[
Real.rpow s (\alpha-1) \neq 0.
\]
The proof defines \(hdiv\) by applying to the equality \(F(s)=F(sbar)\) the scalar multiplication map
\[
v \mapsto \bigl(\operatorname{Real.rpow} s (\alpha-1)\bigr)^{-1}\bullet v.
\]
Thus \(hdiv\) states
\[
\bigl(s^{\alpha-1}\bigr)^{-1}\bullet F(s)
=
\bigl(s^{\alpha-1}\bigr)^{-1}\bullet F(sbar).
\]
Using the definition of \(F(s)\), this becomes
\[
\bigl(s^{\alpha-1}\bigr)^{-1}\bullet
\Bigl(\bigl(s^{\alpha-1}\bigr)\bullet (x(s)-xLimit)\Bigr)
=
\bigl(s^{\alpha-1}\bigr)^{-1}\bullet F(sbar).
\]
The `rw` command applies associativity of scalar multiplication, cancellation of \(s^{\alpha-1}\) with its inverse, and the identity \(1\bullet v=v\). The equation simplifies to
\[
x(s)-xLimit = \bigl(s^{\alpha-1}\bigr)^{-1}\bullet F(sbar).
\]
Finally, `sub_eq_iff_eq_add'.mp` converts the equality \(x(s)-xLimit = C'\) into \(x(s)=xLimit+C'\). Therefore, choosing \(C=F(sbar)\) establishes exactly the desired existential statement. No use of `linarith` is needed; the positivity and cancellation arguments come from already proved facts about real powers, inequalities, and scalar multiplication.

