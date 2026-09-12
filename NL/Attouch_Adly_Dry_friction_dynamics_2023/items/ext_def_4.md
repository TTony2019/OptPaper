## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_def_4.lean`

## Lean statement
```lean
theorem quadraticTimeScale_isIncreasingC1TimeScaleOn {s₀ α : ℝ}
    (hα : 1 < α) (hs₀ : 0 < s₀) :
    IsIncreasingC1TimeScaleOn
      (fun s : ℝ => s ^ 2 / (2 * (α - 1)))
      (fun s : ℝ => s / (α - 1)) s₀
```

## Statement explanation
The theorem `quadraticTimeScale_isIncreasingC1TimeScaleOn` has two implicit real parameters, `s₀` and `α`, written mathematically as \(s_0\) and \(\alpha\). It assumes
\[
h_\alpha : 1<\alpha
\qquad\text{and}\qquad
h_{s_0}:0<s_0 .
\]
Its conclusion is that the predicate `IsIncreasingC1TimeScaleOn` holds for the two real functions
\[
f(s)=\frac{s^2}{2(\alpha-1)},
\qquad
g(s)=\frac{s}{\alpha-1},
\]
and for the point \(s_0\). Thus the function \(f\) is presented as a quadratic time scale, and \(g\) is its proposed derivative.

The defining body of `IsIncreasingC1TimeScaleOn` is not displayed in the supplied source. The proof unpacks the predicate with `refine ⟨?_, ?_⟩`, so it has exactly two obligations. From the way the proof introduces variables, the first obligation is a strict monotonicity statement: for points \(a,b\) in the domain, with \(s_0\le a\), \(s_0\le b\), and \(a<b\), one must prove
\[
f(a)<f(b).
\]
The second obligation is a differentiability statement: for an admissible point \(s\), with the domain hypothesis named `hs`, one must prove that \(f\) has derivative \(g(s)\) at \(s\), i.e.
\[
\operatorname{HasDerivAt} f \,(g(s))\, s .
\]
The proof actually proves the derivative statement without using the content of `hs`.

Mathematically, the theorem says that for \(\alpha>1\) and \(s_0>0\), the map
\[
s\mapsto \frac{s^2}{2(\alpha-1)}
\]
is a strictly increasing \(C^1\) time scale on the positive part of the real line starting at \(s_0\), with derivative
\[
s\mapsto \frac{s}{\alpha-1}.
\]
The positivity of \(s_0\) is used to ensure every admissible point \(a\) is positive, so that \(a<b\) implies \(a^2<b^2\). The positivity of \(\alpha-1\) is used to divide by \(2(\alpha-1)\) without changing inequalities and to know that the relevant denominators are nonzero.

## Lean proof
```lean
by
  have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
  have hαsub : 0 < α - 1 := sub_pos.mpr hα
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    apply (div_lt_div_iff_of_pos_right hden).mpr
    have ha0 : 0 < a := lt_of_lt_of_le hs₀ ha
    have habsq : a ^ 2 < b ^ 2 := by nlinarith
    exact habsq
  · intro s hs
    convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1
    · field_simp [ne_of_gt hαsub]
      ring
```

## Proof explanation
The proof begins by establishing the positivity facts needed later. The command
`have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)`
proves
\[
0<2(\alpha-1).
\]
Here `sub_pos.mpr hα` uses the hypothesis \(1<\alpha\) to produce
\[
0<\alpha-1,
\]
because \(0<a-b\) is equivalent to \(b<a\) with \(a=\alpha\) and \(b=1\). The tactic `norm_num` proves \(0<2\), and `mul_pos` combines \(0<2\) and \(0<\alpha-1\) to conclude that their product is positive. This positivity is essential because the proof will later divide an inequality by \(2(\alpha-1)\).

Next,
`have hαsub : 0 < α - 1 := sub_pos.mpr hα`
records the same fact
\[
0<\alpha-1
\]
separately. It will be used to know that \(\alpha-1\ne0\) when clearing denominators.

The command
`refine ⟨?_, ?_⟩`
splits the `IsIncreasingC1TimeScaleOn` predicate into its two components.

For the first component, the proof introduces
`intro a ha b hb hab`.
The hypothesis used from `ha` is the lower-bound condition \(s_0\le a\). The hypothesis `hab` is the ordering condition \(a<b\). The proof does not need the further domain information in `hb`.

The goal at this point is to prove the monotonicity inequality for \(f\), namely
\[
\frac{a^2}{2(\alpha-1)}<\frac{b^2}{2(\alpha-1)}.
\]
The command
`apply (div_lt_div_iff_of_pos_right hden).mpr`
uses the fact that \(2(\alpha-1)>0\). For a positive denominator \(c\), the inequality \(x/c<y/c\) is equivalent to \(x<y\). Therefore the goal reduces to proving
\[
a^2<b^2.
\]

Then
`have ha0 : 0 < a := lt_of_lt_of_le hs₀ ha`
uses \(0<s_0\) and \(s_0\le a\) to conclude \(0<a\). This is the transitivity step: a strict inequality followed by a non-strict inequality gives a strict inequality.

The command
`have habsq : a ^ 2 < b ^ 2 := by nlinarith`
proves
\[
a^2<b^2
\]
from the available arithmetic hypotheses, in particular \(0<a\) and \(a<b\). Concretely, if \(0<a<b\), then \(b^2-a^2=(b-a)(b+a)>0\), hence \(a^2<b^2\). The tactic `nlinarith` discharges this nonlinear polynomial inequality. Finally,
`exact habsq`
closes the reduced goal \(a^2<b^2\), completing the monotonicity obligation.

For the second component, the proof introduces
`intro s hs`.
The hypothesis `hs` is the domain condition for the differentiability part, but the proof does not use its content. The goal is to show that the function
\[
s\mapsto \frac{s^2}{2(\alpha-1)}
\]
has derivative
\[
\frac{s}{\alpha-1}
\]
at the point \(s\).

The command
`convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1`
combines two derivative facts. First, `hasDerivAt_pow 2 s` gives the power rule for \(x\mapsto x^2\) at \(s\), whose derivative is \(2s\) in ordinary notation. Second, `.div_const (2 * (α - 1))` applies the rule that if a function \(u\) has derivative \(u'\), then the function \(x\mapsto u(x)/c\) has derivative \(u'/c\). Thus it supplies the derivative
\[
\frac{2s}{2(\alpha-1)}
\]
for the function \(x\mapsto x^2/(2(\alpha-1))\) at \(s\). The `convert ... using 1` command matches this result with the required derivative
\[
\frac{s}{\alpha-1},
\]
leaving the equality of these two derivative expressions to be proved.

The remaining subgoal is therefore
\[
\frac{2s}{2(\alpha-1)}=\frac{s}{\alpha-1}.
\]
The command
`field_simp [ne_of_gt hαsub]`
uses \(\alpha-1>0\) to obtain \(\alpha-1\ne0\), allowing it to clear denominators in this equality. The command
`ring`
then proves the resulting polynomial identity in \(s\) and \(\alpha\). This completes the differentiability obligation.

Thus the proof establishes both required components: the strict increase of the quadratic time scale on the relevant positive domain, and the claimed derivative \(s/(\alpha-1)\).

