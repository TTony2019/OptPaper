## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_thm_2.lean`

## Lean statement
```lean
theorem integral_jensen_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (F : ConvexDifferentiableObjective H) (a b : ℝ) (g : ℝ → H)
    (hab : a < b) (hg : IntervalIntegrable g volume a b)
    (hFg : IntervalIntegrable (F.f ∘ g) volume a b) :
    F.f ((b - a)⁻¹ • ∫ s in a..b, g s) ≤
      (b - a)⁻¹ * ∫ s in a..b, F.f (g s)
```

## Statement explanation
The theorem `integral_jensen_inequality` is stated for a real Hilbert space $H$, namely a type equipped with a normed additive commutative group structure, a real inner product space structure, and completeness. The main data are a bundled convex differentiable objective $F$, real numbers $a,b$, and a function $g:\mathbb R\to H$. Writing $f=F.f$ for the scalar-valued objective and $\nabla f$ for the gradient supplied by $F$, the assumptions are that $a<b$, that $g$ is interval integrable on $[a,b]$ with respect to Lebesgue measure, and that the composite $f\circ g$ is interval integrable on $[a,b]$. The conclusion is

$$
f\left((b-a)^{-1}\bullet \int_a^b g(s)\,ds\right)
\le
(b-a)^{-1}\int_a^b f(g(s))\,ds .
$$

Here $(b-a)^{-1}\bullet \int_a^b g(s)\,ds$ is the average of the $H$-valued function $g$ over $[a,b]$, while $(b-a)^{-1}\int_a^b f(g(s))\,ds$ is the average of the real-valued function $f\circ g$. Thus the theorem says that the value of the convex objective $f$ at the integral average of $g$ is at most the integral average of the values $f(g(s))$. This is the integral form of Jensen’s inequality for a convex differentiable function on a real Hilbert space.

## Lean proof
```lean
by
  let m : H := (b - a)⁻¹ • ∫ s in a..b, g s
  have hlen_pos : 0 < b - a := sub_pos.mpr hab
  have hlen_ne : b - a ≠ 0 := ne_of_gt hlen_pos
  have hab_le : a ≤ b := hab.le
  have hgI : IntegrableOn g (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp hg
  have hFgI : IntegrableOn (F.f ∘ g) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab_le).mp hFg
  have hIoc_ne_top : volume (Set.Ioc a b) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hconstH : IntegrableOn (fun _ : ℝ => m) (Set.Ioc a b) volume :=
    integrableOn_const (hs := hIoc_ne_top)
  have hsubI : IntegrableOn (fun s => g s - m) (Set.Ioc a b) volume := hgI.sub hconstH
  have hinnerI : IntegrableOn (fun s => inner ℝ (gradient F.f m) (g s - m)) (Set.Ioc a b) volume :=
    (hsubI.const_inner (gradient F.f m))
  have hconstR : IntegrableOn (fun _ : ℝ => F.f m) (Set.Ioc a b) volume :=
    integrableOn_const (hs := hIoc_ne_top)
  have hleftI : IntegrableOn (fun s => F.f m + inner ℝ (gradient F.f m) (g s - m))
      (Set.Ioc a b) volume := hconstR.add hinnerI
  have hpoint : ∀ s : ℝ, F.f m + inner ℝ (gradient F.f m) (g s - m) ≤ F.f (g s) := by
    intro s
    exact F.firstOrder m (g s)
  have hmono : ∫ s in Set.Ioc a b, F.f m + inner ℝ (gradient F.f m) (g s - m) ≤
      ∫ s in Set.Ioc a b, F.f (g s) :=
    integral_mono hleftI hFgI hpoint
  have hsub_integral : ∫ s in Set.Ioc a b, g s - m =
      (∫ s in Set.Ioc a b, g s) - ∫ _ in Set.Ioc a b, m :=
    integral_sub hgI hconstH
  have hinner_integral : ∫ s in Set.Ioc a b, inner ℝ (gradient F.f m) (g s - m) =
      inner ℝ (gradient F.f m) (∫ s in Set.Ioc a b, g s - m) :=
    integral_inner hsubI (gradient F.f m)
  have hconstR_integral : ∫ _ in Set.Ioc a b, F.f m = (b - a) * F.f m := by
    rw [← intervalIntegral.integral_of_le hab_le, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  have hconstH_integral : ∫ _ in Set.Ioc a b, m = (b - a) • m := by
    rw [← intervalIntegral.integral_of_le hab_le, intervalIntegral.integral_const]
  have hleft_calc : ∫ s in Set.Ioc a b, F.f m + inner ℝ (gradient F.f m) (g s - m) =
      (b - a) * F.f m +
        inner ℝ (gradient F.f m) ((∫ s in Set.Ioc a b, g s) - (b - a) • m) := by
    rw [integral_add hconstR hinnerI, hinner_integral, hsub_integral,
      hconstR_integral, hconstH_integral]
  have hrem : inner ℝ (gradient F.f m) ((∫ s in Set.Ioc a b, g s) - (b - a) • m) = 0 := by
    dsimp [m]
    rw [← intervalIntegral.integral_of_le hab_le]
    rw [smul_smul]
    simp [mul_inv_cancel₀ hlen_ne]
  have hraw : (b - a) * F.f m ≤ ∫ s in Set.Ioc a b, F.f (g s) := by
    rw [hleft_calc, hrem, add_zero] at hmono
    exact hmono
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hlen_pos.le)
  rw [← intervalIntegral.integral_of_le hab_le] at hscaled
  have hfinal : F.f m ≤ (b - a)⁻¹ * ∫ s in a..b, F.f (g s) := by
    convert hscaled using 1
    all_goals field_simp [hlen_ne]
  simpa [m] using hfinal
```

## Proof explanation
The proof begins by defining the average point

$$
m := (b-a)^{-1}\bullet \int_a^b g(s)\,ds .
$$

The goal is then to prove $f(m)\le (b-a)^{-1}\int_a^b f(g(s))\,ds$, which is exactly the original statement after unfolding $m$.

First, the proof records elementary consequences of $a<b$: $b-a>0$, hence $b-a\neq 0$, and also $a\le b$. The positivity is used later to divide by $b-a$ and to multiply an inequality by the nonnegative number $(b-a)^{-1}$.

Next, the interval-integrability hypotheses are converted to integrability on the half-open set $(a,b]$. The lemma `intervalIntegrable_iff_integrableOn_Ioc_of_le` says that, when $a\le b$, interval integrability over $a..b$ is equivalent to integrability over $(a,b]$ with respect to Lebesgue measure. Applying this equivalence to $hg$ gives that $g$ is integrable on $(a,b]$, and applying it to $hFg$ gives that $f\circ g$ is integrable on $(a,b]$. This is useful because the monotonicity and linearity lemmas used below are stated for integrals over a set.

The proof then notes that $(a,b]$ has finite Lebesgue measure, so its measure is not $\top$. Consequently, constant functions are integrable on $(a,b]$. This gives integrability of the constant function $s\mapsto m$ with values in $H$, and also integrability of the constant function $s\mapsto f(m)$ with values in $\mathbb R$.

From these, the proof builds integrability of the functions appearing in the first-order inequality. Since $g$ and the constant $m$ are integrable on $(a,b]$, their difference $s\mapsto g(s)-m$ is integrable. Taking the inner product with the fixed vector $\nabla f(m)$, the function

$$
s\mapsto \langle \nabla f(m), g(s)-m\rangle
$$

is integrable. Adding the constant function $f(m)$, the function

$$
s\mapsto f(m)+\langle \nabla f(m), g(s)-m\rangle
$$

is integrable on $(a,b]$.

The key pointwise estimate is the first-order convexity inequality supplied by `F.firstOrder`. For every $s$, it gives

$$
f(m)+\langle \nabla f(m), g(s)-m\rangle \le f(g(s)).
$$

This is the supporting-hyperplane inequality for the convex differentiable function $f$ at the point $m$, applied to the point $g(s)$. In the proof, `intro s` introduces an arbitrary $s$, and `exact F.firstOrder m (g s)` closes the goal using precisely this inequality.

Because the left-hand function is integrable, $f\circ g$ is integrable on $(a,b]$, and the pointwise inequality holds everywhere, the integral monotonicity lemma `integral_mono` yields

$$
\int_{(a,b]} \left(f(m)+\langle \nabla f(m), g(s)-m\rangle\right)\,ds
\le
\int_{(a,b]} f(g(s))\,ds .
$$

The proof now computes the integral on the left. Linearity of the integral gives

$$
\int_{(a,b]} (g(s)-m)\,ds
=\left(\int_{(a,b]} g(s)\,ds\right)-\int_{(a,b]} m\,ds .
$$

Also, since the inner product is linear in its second argument, the integral of the inner product equals the inner product with the integral:

$$
\int_{(a,b]} \langle \nabla f(m), g(s)-m\rangle\,ds
=\left\langle \nabla f(m), \int_{(a,b]} (g(s)-m)\,ds \right\rangle .
$$

The integral of the constant real function $f(m)$ over $(a,b]$ is $(b-a)f(m)$, and the integral of the constant vector $m$ over $(a,b]$ is $(b-a)\bullet m$. Combining these computations, the integral of the affine lower bound is

$$
(b-a)f(m)
+\left\langle \nabla f(m),
\left(\int_{(a,b]} g(s)\,ds\right)-(b-a)\bullet m
\right\rangle .
$$

The inner-product term is zero. Indeed, by definition of $m$,

$$
m=(b-a)^{-1}\bullet \int_a^b g(s)\,ds,
$$

so

$$
(b-a)\bullet m
=(b-a)\bullet\left((b-a)^{-1}\bullet \int_a^b g(s)\,ds\right)
=\int_a^b g(s)\,ds.
$$

Thus the difference inside the inner product is zero, and therefore the inner product is zero. Consequently, the integral on the left reduces to $(b-a)f(m)$, and the earlier monotonicity inequality becomes

$$
(b-a)f(m)\le \int_{(a,b]} f(g(s))\,ds .
$$

The proof then multiplies this inequality by the nonnegative scalar $(b-a)^{-1}$. The lemma `mul_le_mul_of_nonneg_left` is used here: if $c\ge 0$ and $x\le y$, then $cx\le cy$. Since $b-a>0$, its inverse is nonnegative. After this multiplication, the left-hand side is

$$
(b-a)^{-1}\bigl((b-a)f(m)\bigr)=f(m),
$$

because $b-a\neq 0$. The right-hand side becomes

$$
(b-a)^{-1}\int_{(a,b]} f(g(s))\,ds .
$$

Rewriting the integral over $(a,b]$ back to the interval integral over $a..b$, using the same relation between interval integrals and integrals over $(a,b]$, gives

$$
f(m)\le (b-a)^{-1}\int_a^b f(g(s))\,ds .
$$

Finally, `simpa [m] using hfinal` unfolds the definition of $m$, converting this inequality into the exact stated conclusion

$$
f\left((b-a)^{-1}\bullet \int_a^b g(s)\,ds\right)
\le
(b-a)^{-1}\int_a^b f(g(s))\,ds .
$$

The tactic `field_simp [hlen_ne]` is used in the final simplification to clear the denominator $b-a$, justified by $b-a\neq 0$. The commands `rw` rewrite goals or hypotheses using equalities, `simp` simplifies arithmetic and inner-product identities, `dsimp` unfolds local definitions, `convert` changes a goal into an equivalent one up to definitional simplification, and `exact` closes a goal by precisely supplying the required term.

