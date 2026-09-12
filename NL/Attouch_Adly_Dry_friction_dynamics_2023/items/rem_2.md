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
Let \(H\) be a real normed vector space, let \(\bar s,\alpha\in\mathbb R\), let \(x,y,dx:\mathbb R\to H\) be functions, and let \(x_{\mathrm{Limit}}\in H\). The theorem assumes:

- \(1<\alpha\);
- \(0<\bar s\);
- for every \(s\in[\bar s,\infty)\),
  \[
  x'(s)=dx(s)
  \]
  in the sense of `HasDerivAt`, and
  \[
  dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-y(s)\bigr)=0;
  \]
- for every \(s\in[\bar s,\infty)\),
  \[
  y(s)=x_{\mathrm{Limit}}.
  \]

The conclusion is that there exists a vector \(C\in H\) such that, for every \(s\in[\bar s,\infty)\),
\[
x(s)=x_{\mathrm{Limit}}+\bigl(s^{\alpha-1}\bigr)^{-1}\cdot C,
\]
where the scalar multiplication is the real vector-space action on \(H\).

Mathematically, on the tail \([\bar s,\infty)\) the function \(x\) satisfies the first-order linear ODE
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-y(s)\bigr)=0.
\]
Since \(y(s)=x_{\mathrm{Limit}}\) there, this becomes
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-x_{\mathrm{Limit}}\bigr)=0.
\]
The usual integrating factor for this equation is \(s^{\alpha-1}\). The theorem says that \(s^{\alpha-1}\bigl(x(s)-x_{\mathrm{Limit}}\bigr)\) is constant on the tail, so that
\[
x(s)-x_{\mathrm{Limit}}=s^{-(\alpha-1)}C
\]
for one fixed vector \(C\), namely the value of the integrating-factor expression at the initial tail point \(\bar s\). Thus the conclusion describes all possible trajectories \(x\) on the tail: they are exactly \(x_{\mathrm{Limit}}\) plus a scalar multiple of the decaying factor \(s^{-(\alpha-1)}\).

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
The proof begins by recording the positivity of the exponent:
\[
1<\alpha \implies 0<\alpha-1.
\]
In Lean this is `have _hp : 0 < α - 1 := sub_pos.mpr hα`. This positivity is natural for the integrating factor, although the later algebra mainly uses the positivity of the base \(s\), not of the exponent.

Next the proof defines the integrating-factor function
\[
F(t)=t^{\alpha-1}\cdot\bigl(x(t)-x_{\mathrm{Limit}}\bigr).
\]
In Lean this is
`let F : ℝ → H := fun t => Real.rpow t (α - 1) • (x t - xLimit)`.
The scalar \(t^{\alpha-1}\) is the real power `Real.rpow t (α - 1)`. The purpose of \(F\) is to absorb the coefficient \((\alpha-1)/s\) in the ODE.

The proof then establishes that \(F\) has derivative zero at every point of the tail. The relevant claim is
\[
\forall s\in[\bar s,\infty),\quad F'(s)=0.
\]
In Lean this is `hFzero : ∀ s ∈ Set.Ici sbar, HasDerivAt F 0 s`.

To prove this, the proof fixes an arbitrary \(s\in[\bar s,\infty)\). The tactic `intro s hs` introduces \(s\) and the hypothesis \(hs:s\in[\bar s,\infty)\). Since \(\bar s>0\) and \(\bar s\le s\), it obtains
\[
0<s
\]
by `lt_of_lt_of_le hpositiveTime hs`, stored as `hspos`.

Then `havg := haverage s hs` extracts the conjunction saying that \(x\) has derivative \(dx(s)\) at \(s\), and that
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-y(s)\bigr)=0.
\]
Using the hypothesis `hstab s hs`, which says \(y(s)=x_{\mathrm{Limit}}\), the proof rewrites \(y(s)\) to \(x_{\mathrm{Limit}}\). After this rewrite, the ODE hypothesis becomes
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-x_{\mathrm{Limit}}\bigr)=0.
\]

At this point the proof applies the cited private theorem `integrating_factor_deriv_zero`. Its statement, specialized to \(p=\alpha-1\), says: if \(0<s\), if \(x\) has derivative \(dx(s)\) at \(s\), and if
\[
dx(s)+\frac{\alpha-1}{s}\bigl(x(s)-x_{\mathrm{Limit}}\bigr)=0,
\]
then the function
\[
t\mapsto t^{\alpha-1}\cdot\bigl(x(t)-x_{\mathrm{Limit}}\bigr)
\]
has derivative \(0\) at \(s\). Concretely, the product rule gives
\[
F'(s)=(\alpha-1)s^{\alpha-2}\bigl(x(s)-x_{\mathrm{Limit}}\bigr)
+s^{\alpha-1}dx(s),
\]
which is
\[
s^{\alpha-2}\left((\alpha-1)\bigl(x(s)-x_{\mathrm{Limit}}\bigr)+s\,dx(s)\right).
\]
Multiplying the ODE by \(s\) gives
\[
s\,dx(s)+(\alpha-1)\bigl(x(s)-x_{\mathrm{Limit}}\bigr)=0,
\]
so the derivative is indeed zero. This proves `hFzero`.

The proof now chooses the constant
\[
C=F(\bar s).
\]
In Lean this is `refine ⟨F sbar, ?_⟩`, where the existential witness is \(F(\bar s)\). It remains to prove that for every \(s\in[\bar s,\infty)\),
\[
x(s)=x_{\mathrm{Limit}}+\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(\bar s).
\]
The tactic `intro s hs` introduces an arbitrary such \(s\).

The proof next prepares to use the constancy theorem for functions with zero derivative on a convex set. First it shows that \(F\) is differentiable within the tail at every point of the tail:
\[
\forall t\in[\bar s,\infty),\quad
F\text{ is differentiable within }[\bar s,\infty)\text{ at }t.
\]
This is `hdiff`. It is obtained from `hFzero t ht`: since \(F\) has a derivative at \(t\), it is differentiable at \(t\), hence also differentiable within the subset \([\bar s,\infty)\).

Second, it shows that the within-derivative of \(F\) is zero everywhere on the tail:
\[
\forall t\in[\bar s,\infty),\quad
\operatorname{fderivWithin}_{\mathbb R} F\,[\bar s,\infty)\,t=0.
\]
This is `hderiv`. The proof uses `HasFDerivWithinAt.fderivWithin`: from \(F'(t)=0\) one gets a within-derivative \(0\) on the tail, and since the interval \([\bar s,\infty)\) is uniquely differentiable at each of its points, the within Fréchet derivative is exactly that zero derivative. The relevant uniqueness fact is supplied by `uniqueDiffOn_Ici sbar t ht`. The tactic `simpa` then simplifies the derivative expression to \(0\).

Now the proof applies constancy on a convex set. The interval \([\bar s,\infty)\) is convex, as given by `convex_Ici sbar`. The theorem `is_const_of_fderivWithin_eq_zero` says that if a function is differentiable within a convex set at every point and its within-derivative is zero there, then the function is constant on that set. Applying it to \(F\), \(hdiff\), and \(hderiv\), and using the two points \(s\) and \(\bar s\) of \([\bar s,\infty)\), gives
\[
F(s)=F(\bar s).
\]
In Lean the membership \(s\in[\bar s,\infty)\) is `hs`, and \(\bar s\in[\bar s,\infty)\) is proved by `Set.mem_Ici.mpr le_rfl`, since \(\bar s\le\bar s\).

The proof then recalls that \(s>0\), again from \(\bar s>0\) and \(\bar s\le s\), and proves that
\[
s^{\alpha-1}\ne0.
\]
This follows from `Real.rpow_pos_of_pos hspos (α - 1)`: because the base \(s\) is positive, the real power \(s^{\alpha-1}\) is positive, hence nonzero.

Next, the equality \(F(s)=F(\bar s)\) is multiplied on the left by the scalar \(\bigl(s^{\alpha-1}\bigr)^{-1}\). In Lean this is done with `congrArg`:
\[
\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(s)
=
\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(\bar s).
\]
The resulting equality is called `hdiv`.

The goal is changed to the desired identity with \(C=F(\bar s)\):
\[
x(s)=x_{\mathrm{Limit}}+\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(\bar s).
\]
The equality `hdiv` is then rewritten using the definition of \(F\) at \(s\):
\[
F(s)=s^{\alpha-1}\cdot\bigl(x(s)-x_{\mathrm{Limit}}\bigr).
\]
Thus `hdiv` becomes
\[
\bigl(s^{\alpha-1}\bigr)^{-1}\cdot
\left(s^{\alpha-1}\cdot\bigl(x(s)-x_{\mathrm{Limit}}\bigr)\right)
=
\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(\bar s).
\]

The proof simplifies the left-hand side by rewriting with `smul_smul`, `inv_mul_cancel₀ hpow_ne`, and `one_smul`. The first rewrites associativity of scalar multiplication:
\[
a^{-1}\cdot(a\cdot z)=(a^{-1}a)\cdot z.
\]
The second uses \(a\neq0\) to simplify \(a^{-1}a=1\). The third removes the scalar \(1\). Hence `hdiv` becomes
\[
x(s)-x_{\mathrm{Limit}}
=
\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(\bar s).
\]
Finally, `exact sub_eq_iff_eq_add'.mp hdiv` applies the elementary equivalence
\[
a-b=c \iff a=b+c
\]
to convert this into
\[
x(s)=x_{\mathrm{Limit}}+\bigl(s^{\alpha-1}\bigr)^{-1}\cdot F(\bar s).
\]
This is exactly the required formula with \(C=F(\bar s)\), completing the existential proof.

No `linarith` call occurs in this proof. The positivity and order facts are handled by `sub_pos.mpr`, `lt_of_lt_of_le`, and the real-power positivity lemma.

