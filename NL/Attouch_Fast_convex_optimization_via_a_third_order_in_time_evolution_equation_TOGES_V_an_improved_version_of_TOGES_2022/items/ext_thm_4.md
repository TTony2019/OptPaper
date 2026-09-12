## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_thm_4.lean`

## Lean statement
```lean
theorem scalar_differential_comparison (E b : ℝ → ℝ) (t0 a : ℝ)
    (hIntegrable : ∀ t ≥ t0, IntervalIntegrable b MeasureTheory.volume t0 t)
    (hDifferentiable : ∀ t ≥ t0, HasDerivAt E (deriv E t) t)
    (h : ∀ t ≥ t0, deriv E t + a * E t ≤ b t) :
    ∀ t ≥ t0, E t ≤ Real.exp (-a * (t - t0)) * E t0 +
      ∫ s in t0..t, Real.exp (-a * (t - s)) * b s
```

## Statement explanation
The declaration is a scalar comparison theorem for a first-order linear differential inequality. It takes two real-valued functions $E,b:\mathbb R\to\mathbb R$ and real parameters $t_0,a$. The hypothesis `hIntegrable` says that for every $t\ge t_0$, the function $b$ is interval integrable on $[t_0,t]$ with respect to Lebesgue measure. The hypothesis `hDifferentiable` says that for every $t\ge t_0$, the function $E$ has derivative $\mathrm{deriv} E(t)$ at $t$; equivalently, $E$ is differentiable at every such $t$, with derivative given by the value of the derivative function. The hypothesis `h` says that on the same half-line,

$$
\mathrm{deriv} E(t)+aE(t)\le b(t).
$$

The conclusion is that for every $t\ge t_0$,

$$
E(t)\le e^{-a(t-t_0)}E(t_0)+\int_{t_0}^{t} e^{-a(t-s)}b(s)\,ds.
$$

Thus, if $E$ satisfies the differential inequality $E'+aE\le b$, then $E(t)$ is bounded above by the explicit solution formula for the equality case $E'+aE=b$ with initial value $E(t_0)$. This is the usual Gronwall-type comparison estimate in the scalar linear case.

## Lean proof
```lean
by
  intro t ht
  rcases ht.eq_or_lt with rfl | htlt
  · simp
  let w : ℝ → ℝ := fun s => Real.exp (a * (s - t0))
  let q : ℝ → ℝ := fun s => w s * E s
  let φ : ℝ → ℝ := fun s => w s * b s
  have hw_cont : Continuous w := by
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))
  have hE_cont : ContinuousOn E (Set.Icc t0 t) := by
    intro s hs
    exact (hDifferentiable s hs.1).continuousAt.continuousWithinAt
  have hq_cont : ContinuousOn q (Set.Icc t0 t) :=
    hw_cont.continuousOn.mul hE_cont
  have hφ_interval : IntervalIntegrable φ MeasureTheory.volume t0 t := by
    exact scalar_differential_weighted_integrable b t0 t a htlt.le (hIntegrable t htlt.le)
  have hφ_int : MeasureTheory.IntegrableOn φ (Set.Icc t0 t) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le htlt.le).mp hφ_interval
  have hq_deriv : ∀ s ∈ Set.Ioo t0 t,
      HasDerivWithinAt q (w s * (deriv E s + a * E s)) (Set.Ioi s) s := by
    intro s hs
    have hlin : HasDerivAt (fun u : ℝ => a * (u - t0)) a s := by
      convert ((hasDerivAt_id s).sub_const t0).const_mul a using 1; ring_nf
    have hw_deriv : HasDerivAt w (w s * a) s := by
      exact (Real.hasDerivAt_exp (a * (s - t0))).comp s hlin
    have hprod := hw_deriv.mul (hDifferentiable s hs.1.le)
    convert hprod.hasDerivWithinAt using 1; dsimp [q, w]; ring_nf
  have hneg_deriv : ∀ s ∈ Set.Ioo t0 t,
      HasDerivWithinAt (fun u => -q u) (-(w s * (deriv E s + a * E s))) (Set.Ioi s) s := by
    intro s hs
    convert (hq_deriv s hs).neg using 1
  have hneg_le : ∀ s ∈ Set.Ioo t0 t,
      -(w s * b s) ≤ -(w s * (deriv E s + a * E s)) := by
    intro s hs
    have hbase := h s hs.1.le
    have hmul : w s * (deriv E s + a * E s) ≤ w s * b s :=
      mul_le_mul_of_nonneg_left hbase (show 0 ≤ w s from Real.exp_nonneg _)
    linarith
  have hcmp := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    (g := fun u => -q u)
    (g' := fun u => -(w u * (deriv E u + a * E u)))
    (φ := fun u => -(w u * b u)) htlt.le hq_cont.neg hneg_deriv hφ_int.neg hneg_le
  have hweighted : w t * E t ≤ E t0 + ∫ s in t0..t, w s * b s := by
    change (∫ y in t0..t, -(w y * b y)) ≤ -q t - -q t0 at hcmp
    rw [intervalIntegral.integral_neg] at hcmp
    dsimp [q] at hcmp
    dsimp [w] at hcmp ⊢
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hcmp
    linarith
  have hcancel := mul_le_mul_of_nonneg_left hweighted (Real.exp_nonneg (-a * (t - t0)))
  have hresult : E t ≤ Real.exp (-a * (t - t0)) * E t0 +
      Real.exp (-a * (t - t0)) * ∫ s in t0..t, w s * b s := by
    dsimp [w] at hcancel
    have hprod : Real.exp (-a * (t - t0)) * Real.exp (a * (t - t0)) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1; ring_nf
    rw [mul_add, ← mul_assoc, hprod, one_mul] at hcancel
    exact hcancel
  have hkernel : Real.exp (-a * (t - t0)) * ∫ s in t0..t, w s * b s =
      ∫ s in t0..t, Real.exp (-a * (t - s)) * b s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [w]
    rw [← mul_assoc, scalar_differential_kernel_identity]
  linarith
```

## Proof explanation
The proof fixes an arbitrary $t\ge t_0$ using `intro t ht`. It then splits into the case $t=t_0$ and the case $t_0<t$ using `rcases ht.eq_or_lt with rfl | htlt`.

In the equality case $t=t_0$, the tactic `simp` proves the desired inequality. The right-hand side becomes

$$
e^{0}E(t_0)+\int_{t_0}^{t_0} e^{-a(t_0-s)}b(s)\,ds
= E(t_0)+0,
$$

because $e^0=1$ and the interval integral over a single point is zero. Hence the conclusion reduces to $E(t_0)\le E(t_0)$.

From now on assume $t_0<t$. The proof introduces three auxiliary functions:

$$
w(s)=e^{a(s-t_0)},\qquad q(s)=w(s)E(s),\qquad \varphi(s)=w(s)b(s).
$$

The plan is to differentiate $q$, use the differential inequality to compare the derivative of $-q$ with $-\varphi$, integrate the comparison over $[t_0,t]$, and then multiply by $e^{-a(t-t_0)}$ to obtain the stated formula.

First, the proof establishes regularity. It shows $w$ is continuous because it is the exponential of the continuous affine function $s\mapsto a(s-t_0)$. It shows $E$ is continuous on $[t_0,t]$: for $s\in[t_0,t]$, the hypothesis $s\ge t_0$ gives differentiability of $E$ at $s$, hence continuity at $s$, hence continuity within the interval. Therefore $q=wE$ is continuous on $[t_0,t]$, since it is a product of continuous functions.

Next the proof obtains integrability of $\varphi=wb$. It invokes the cited result `scalar_differential_weighted_integrable`, which says that if $t_0\le t$ and $b$ is interval integrable on $[t_0,t]$, then the function

$$
s\mapsto e^{a(s-t_0)}b(s)
$$

is also interval integrable on $[t_0,t]$. Here this is applied with the given $b,t_0,t,a$, the inequality $t_0\le t$ from $t_0<t$, and the hypothesis `hIntegrable t htlt.le`. Thus $\varphi$ is interval integrable. The proof then converts interval integrability into integrability on the closed interval $Icc(t_0,t)=[t_0,t]$ using `intervalIntegrable_iff_integrableOn_Icc_of_le`, which is valid because $t_0\le t$. This gives $\varphi$ integrable on $[t_0,t]$, and in particular the negative function $-\varphi$ is integrable there.

The next step computes the derivative of $q$. For $s\in(t_0,t)$, the proof shows that

$$
q'(s)=w(s)\bigl(E'(s)+aE(s)\bigr)
$$

as a right derivative on $(s,\infty)$. The computation is done in three parts. The affine map $u\mapsto a(u-t_0)$ has derivative $a$ at $s$. By the chain rule for the exponential, $w'(s)=w(s)a$. Since $E$ is differentiable at $s$, the product rule gives

$$
q'(s)=w(s)aE(s)+w(s)E'(s)
= w(s)\bigl(E'(s)+aE(s)\bigr).
$$

The Lean commands `convert` and `ring_nf` are used to rewrite the derivative produced by the product rule into this exact algebraic form. Consequently, the derivative of $-q$ is

$$
(-q)'(s)=-w(s)\bigl(E'(s)+aE(s)\bigr),
$$

which the proof obtains by applying `.neg` to the derivative statement for $q$.

The differential hypothesis gives, for $s\in(t_0,t)$,

$$
E'(s)+aE(s)\le b(s).
$$

Multiplying by $w(s)=e^{a(s-t_0)}\ge 0$ preserves the inequality:

$$
w(s)\bigl(E'(s)+aE(s)\bigr)\le w(s)b(s).
$$

Negating reverses it:

$$
-w(s)b(s)\le -w(s)\bigl(E'(s)+aE(s)\bigr).
$$

This is the pointwise comparison used for the integration theorem.

The proof then invokes `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le`. In this application it is used with $g(u)=-q(u)$, with right derivative

$$
g'(u)=-w(u)\bigl(E'(u)+aE(u)\bigr),
$$

and with comparison function

$$
\phi(u)=-w(u)b(u).
$$

The hypotheses supplied are: $t_0\le t$; $g$ is continuous on $[t_0,t]$; $g$ has the stated right derivative on $(t_0,t)$; $\phi$ is integrable on $[t_0,t]$; and $\phi\le g'$ on $(t_0,t)$. Its conclusion in this situation is

$$
\int_{t_0}^{t} -w(s)b(s)\,ds
\le (-q)(t)-(-q)(t_0).
$$

This is the inequality named `hcmp`.

The proof now converts this into a simpler weighted inequality. Using linearity of the interval integral, $\int -wb=-\int wb$. Unfolding $q$ gives

$$
-q(t)-(-q(t_0))=-w(t)E(t)+w(t_0)E(t_0).
$$

Since

$$
w(t_0)=e^{a(t_0-t_0)}=e^0=1,
$$

the inequality becomes

$$
-\int_{t_0}^{t}w(s)b(s)\,ds
\le -w(t)E(t)+E(t_0).
$$

Rearranging by `linarith` yields

$$
w(t)E(t)\le E(t_0)+\int_{t_0}^{t}w(s)b(s)\,ds.
$$

This intermediate inequality is `hweighted`.

Next, the proof multiplies `hweighted` by

$$
e^{-a(t-t_0)}\ge 0.
$$

Using `mul_le_mul_of_nonneg_left`, it obtains

$$
e^{-a(t-t_0)}w(t)E(t)
\le e^{-a(t-t_0)}
\left(E(t_0)+\int_{t_0}^{t}w(s)b(s)\,ds\right).
$$

Since

$$
e^{-a(t-t_0)}w(t)
=
e^{-a(t-t_0)}e^{a(t-t_0)}
=
e^0
=
1,
$$

and the right-hand side distributes, this becomes

$$
E(t)\le e^{-a(t-t_0)}E(t_0)
+
e^{-a(t-t_0)}\int_{t_0}^{t}w(s)b(s)\,ds.
$$

This is `hresult`.

Finally, the proof identifies the remaining integral. It uses `intervalIntegral.integral_const_mul` to move the constant $e^{-a(t-t_0)}$ inside the integral:

$$
e^{-a(t-t_0)}\int_{t_0}^{t}w(s)b(s)\,ds
=
\int_{t_0}^{t}
e^{-a(t-t_0)}w(s)b(s)\,ds.
$$

For each $s$, the cited identity `scalar_differential_kernel_identity` gives

$$
e^{-a(t-t_0)}e^{a(s-t_0)}
=
e^{-a(t-s)},
$$

because the exponents add:

$$
-a(t-t_0)+a(s-t_0)=-a(t-s).
$$

Thus, by `intervalIntegral.integral_congr`,

$$
e^{-a(t-t_0)}\int_{t_0}^{t}w(s)b(s)\,ds
=
\int_{t_0}^{t}e^{-a(t-s)}b(s)\,ds.
$$

Substituting this equality into `hresult` and applying `linarith` gives exactly the claimed bound

$$
E(t)\le e^{-a(t-t_0)}E(t_0)
+
\int_{t_0}^{t}e^{-a(t-s)}b(s)\,ds.
$$

This completes the proof for arbitrary $t\ge t_0$.

