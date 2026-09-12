## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/rem_4.lean`

## Lean statement
```lean
theorem rem_4_refinement_bound (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T ∈ Set.Ioo (0 : ℝ) T₀, ∀ θ₁ : ℝ, 0 ≤ θ₁ →
      ∀ A₀ B₀ c : ℝ, 0 ≤ A₀ → 0 ≤ B₀ → 0 ≤ c →
        (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀ + T ^ 2 * θ₁ * c) ≤
          Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) *
              Real.sqrt (A₀ ^ 2 + B₀ ^ 2) +
            (θ₁ / Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2)) *
              (Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) - 1) * c
```

## Statement explanation
The declaration `rem_4_refinement_bound` is a theorem about two real parameters \(\alpha\) and \(\gamma\). It assumes that
\[
\alpha>0,\qquad \gamma\ge 0.
\]
From these assumptions it asserts the existence of a positive real number \(T_0\) such that for every
\[
T\in(0,T_0),
\]
every \(\theta_1\ge 0\), and every \(A_0,B_0,c\ge 0\), the following inequality holds:
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}\bigl(A_0+T B_0+T^2\theta_1 c\bigr)
\le
\exp\!\left(T\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}\right)\sqrt{A_0^2+B_0^2}
+
\frac{\theta_1}{\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}}
\left(\exp\!\left(T\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}\right)-1\right)c.
\]
If one sets
\[
m=\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}},
\]
then the right-hand side is
\[
\exp(mT)\sqrt{A_0^2+B_0^2}
+
\frac{\theta_1}{m}\bigl(\exp(mT)-1\bigr)c.
\]
The statement says that on a sufficiently small time interval \((0,T_0)\), the factor
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\]
multiplying \(A_0+T B_0+T^2\theta_1 c\) is controlled by an exponential term times the Euclidean norm \(\sqrt{A_0^2+B_0^2}\), plus a term proportional to \(\theta_1 c\). The number \(T_0\) is uniform in \(T,\theta_1,A_0,B_0,c\); it depends only on \(\alpha\) and \(\gamma\). In the proof, the denominator \(\alpha-\alpha\gamma T-T^2\) is shown to be positive on \((0,T_0)\), so the multiplier is nonnegative.

## Lean proof
```lean
by
  obtain ⟨T₀, hT₀, hT⟩ := rem_4_refinement_threshold α γ hα hγ
  refine ⟨T₀, hT₀, ?_⟩
  intro T hTmem θ₁ hθ₁ A₀ B₀ c hA hB hc
  obtain ⟨hs, hcoeff₁, hcoeff₂⟩ := hT T hTmem
  set m : ℝ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) with hm
  have hm_pos : 0 < m := by
    rw [hm]
    exact Real.sqrt_pos.mpr (by positivity)
  have hcoeff₁' : (α / (α - α * γ * T - T ^ 2)) * Real.sqrt (1 + T ^ 2) ≤
      Real.exp (m * T) := by
    rw [hm]
    exact hcoeff₁
  have hcoeff₂' : (α / (α - α * γ * T - T ^ 2)) * T ^ 2 ≤
      (Real.exp (m * T) - 1) / m := by
    rw [hm]
    exact hcoeff₂
  have hden_pos : 0 < α - α * γ * T - T ^ 2 := by
    have hcore : α * γ * T + T ^ 2 < α := by
      calc
        α * γ * T + T ^ 2 = α * (γ * T + T ^ 2 / α) := by field_simp [hα.ne']
        _ < α * 1 := mul_lt_mul_of_pos_left hs hα
        _ = α := by ring
    nlinarith
  have hg_nonneg : 0 ≤ α / (α - α * γ * T - T ^ 2) := div_nonneg hα.le hden_pos.le
  have hcs : A₀ + T * B₀ ≤ Real.sqrt (1 + T ^ 2) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) := by
    have h2 : (A₀ + T * B₀) ^ 2 ≤ (1 + T ^ 2) * (A₀ ^ 2 + B₀ ^ 2) := by
      nlinarith [sq_nonneg (T * A₀ - B₀)]
    calc
      A₀ + T * B₀ ≤ Real.sqrt ((1 + T ^ 2) * (A₀ ^ 2 + B₀ ^ 2)) :=
        Real.le_sqrt_of_sq_le h2
      _ = Real.sqrt (1 + T ^ 2) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) :=
        Real.sqrt_mul (by positivity) _
  have hmain₁ : (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀) ≤
      Real.exp (m * T) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) := by
    calc
      (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀) ≤
          (α / (α - α * γ * T - T ^ 2)) *
            (Real.sqrt (1 + T ^ 2) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hg_nonneg
      _ = ((α / (α - α * γ * T - T ^ 2)) * Real.sqrt (1 + T ^ 2)) *
            Real.sqrt (A₀ ^ 2 + B₀ ^ 2) := by ring
      _ ≤ Real.exp (m * T) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff₁' (Real.sqrt_nonneg _)
  have hmain₂ : (α / (α - α * γ * T - T ^ 2)) * (T ^ 2 * θ₁ * c) ≤
      (θ₁ / m) * (Real.exp (m * T) - 1) * c := by
    calc
      (α / (α - α * γ * T - T ^ 2)) * (T ^ 2 * θ₁ * c) =
          ((α / (α - α * γ * T - T ^ 2)) * T ^ 2) * (θ₁ * c) := by ring
      _ ≤ ((Real.exp (m * T) - 1) / m) * (θ₁ * c) :=
        mul_le_mul_of_nonneg_right hcoeff₂' (mul_nonneg hθ₁ hc)
      _ = (θ₁ / m) * (Real.exp (m * T) - 1) * c := by ring
  calc
    (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀ + T ^ 2 * θ₁ * c) =
        (α / (α - α * γ * T - T ^ 2)) * (A₀ + T * B₀) +
          (α / (α - α * γ * T - T ^ 2)) * (T ^ 2 * θ₁ * c) := by ring
    _ ≤ Real.exp (m * T) * Real.sqrt (A₀ ^ 2 + B₀ ^ 2) +
          (θ₁ / m) * (Real.exp (m * T) - 1) * c := add_le_add hmain₁ hmain₂
    _ = Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) *
            Real.sqrt (A₀ ^ 2 + B₀ ^ 2) +
          (θ₁ / Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2)) *
            (Real.exp (Real.sqrt (1 + 2 * γ ^ 2 + 2 / α ^ 2) * T) - 1) * c := by
      rw [hm]
```

## Proof explanation
The proof begins by invoking the threshold result `rem_4_refinement_threshold`. For the same real numbers \(\alpha,\gamma\), with \(\alpha>0\) and \(\gamma\ge 0\), that result supplies a positive real \(T_0\) such that for every \(T\in(0,T_0)\), three facts hold:
\[
\gamma T+\frac{T^2}{\alpha}<1,
\]
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}\sqrt{1+T^2}
\le
\exp\!\left(T\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}\right),
\]
and
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}T^2
\le
\frac{\exp\!\left(T\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}\right)-1}
{\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}}.
\]
The proof calls this theorem with `obtain`, unpacking the existential statement into a witness \(T_0\), its positivity \(hT_0\), and the universal property \(hT\). It then uses `refine` to choose the same \(T_0\) for the target theorem, leaving the inequality to be proved.

Next, the proof introduces the universally quantified data with `intro`: a real \(T\) satisfying \(0<T<T_0\), a real \(\theta_1\) with \(0\le \theta_1\), and real numbers \(A_0,B_0,c\) with \(0\le A_0\), \(0\le B_0\), and \(0\le c\). The membership hypothesis says precisely that \(T\in(0,T_0)\). Applying \(hT\) to this \(T\) and its interval membership yields three inequalities: the smallness condition \(h_s\), the bound \(hcoeff_1\) involving \(\sqrt{1+T^2}\), and the bound \(hcoeff_2\) involving \(T^2\).

The proof then defines
\[
m=\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}}.
\]
It proves \(m>0\) by rewriting \(m\) to its defining square root and applying `Real.sqrt_pos.mpr`, which says that a positive real has a positive square root. The positivity of the radicand \(1+2\gamma^2+2/\alpha^2\) follows because \(\alpha>0\), so \(2/\alpha^2>0\), while \(2\gamma^2\ge0\). This positivity is recorded, although the later inequalities are already stated with division by \(m\).

The two threshold inequalities are then restated with \(m\) in place of the square root. This gives
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}\sqrt{1+T^2}\le \exp(mT)
\]
and
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}T^2
\le
\frac{\exp(mT)-1}{m}.
\]

The proof next shows that the denominator is positive:
\[
0<\alpha-\alpha\gamma T-T^2.
\]
It first proves
\[
\alpha\gamma T+T^2<\alpha.
\]
The equality
\[
\alpha\gamma T+T^2=\alpha\left(\gamma T+\frac{T^2}{\alpha}\right)
\]
is obtained with `field_simp`, using \(\alpha\ne0\) from \(\alpha>0\). Since \(h_s\) says
\[
\gamma T+\frac{T^2}{\alpha}<1
\]
and \(\alpha>0\), multiplying by \(\alpha\) with `mul_lt_mul_of_pos_left` gives
\[
\alpha\left(\gamma T+\frac{T^2}{\alpha}\right)<\alpha\cdot 1=\alpha.
\]
Thus \(\alpha\gamma T+T^2<\alpha\), and `nlinarith` rearranges this to \(0<\alpha-\alpha\gamma T-T^2\). Consequently, the multiplier
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
\]
is nonnegative, because both numerator \(\alpha\) and denominator \(\alpha-\alpha\gamma T-T^2\) are nonnegative; this is the `div_nonneg` step.

The proof then establishes the two-dimensional Cauchy–Schwarz estimate
\[
A_0+T B_0
\le
\sqrt{1+T^2}\sqrt{A_0^2+B_0^2}.
\]
It proves the square inequality
\[
(A_0+T B_0)^2\le (1+T^2)(A_0^2+B_0^2)
\]
by `nlinarith`, using the nonnegativity of \((T A_0-B_0)^2\). Indeed,
\[
(1+T^2)(A_0^2+B_0^2)-(A_0+T B_0)^2=(T A_0-B_0)^2\ge0.
\]
Then `Real.le_sqrt_of_sq_le` converts \(X^2\le Y\) into \(X\le\sqrt Y\), giving
\[
A_0+T B_0\le \sqrt{(1+T^2)(A_0^2+B_0^2)}.
\]
Finally, `Real.sqrt_mul` splits this as
\[
\sqrt{(1+T^2)(A_0^2+B_0^2)}
=
\sqrt{1+T^2}\sqrt{A_0^2+B_0^2},
\]
valid because \(1+T^2\ge0\).

Using this Cauchy–Schwarz estimate and the nonnegativity of
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2},
\]
the proof derives the first main bound
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}(A_0+T B_0)
\le
\exp(mT)\sqrt{A_0^2+B_0^2}.
\]
The multiplication step uses `mul_le_mul_of_nonneg_left`. Then the expression is rearranged by `ring` to
\[
\left(\frac{\alpha}{\alpha-\alpha\gamma T-T^2}\sqrt{1+T^2}\right)
\sqrt{A_0^2+B_0^2}.
\]
The previously established bound for the coefficient times \(\sqrt{1+T^2}\), together with \(\sqrt{A_0^2+B_0^2}\ge0\) from `Real.sqrt_nonneg`, gives the desired estimate.

For the second main bound, the proof rewrites
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}(T^2\theta_1 c)
=
\left(\frac{\alpha}{\alpha-\alpha\gamma T-T^2}T^2\right)(\theta_1 c).
\]
Since \(\theta_1\ge0\) and \(c\ge0\), the product \(\theta_1 c\) is nonnegative. Multiplying the threshold estimate for the \(T^2\)-term by \(\theta_1 c\) with `mul_le_mul_of_nonneg_right` yields
\[
\left(\frac{\alpha}{\alpha-\alpha\gamma T-T^2}T^2\right)(\theta_1 c)
\le
\frac{\exp(mT)-1}{m}(\theta_1 c).
\]
A final `ring` rewrite turns the right-hand side into
\[
\frac{\theta_1}{m}(\exp(mT)-1)c.
\]

Finally, the proof combines the two estimates. It first rewrites
\[
\frac{\alpha}{\alpha-\alpha\gamma T-T^2}
(A_0+T B_0+T^2\theta_1 c)
\]
as the sum of the two separately bounded terms using `ring`. Then `add_le_add` combines the bound for \(A_0+T B_0\) and the bound for \(T^2\theta_1 c\). The resulting expression is
\[
\exp(mT)\sqrt{A_0^2+B_0^2}
+
\frac{\theta_1}{m}(\exp(mT)-1)c.
\]
The last `rw [hm]` replaces \(m\) by
\[
\sqrt{1+2\gamma^2+\frac{2}{\alpha^2}},
\]
which is exactly the expression appearing in the statement of `rem_4_refinement_bound`.

