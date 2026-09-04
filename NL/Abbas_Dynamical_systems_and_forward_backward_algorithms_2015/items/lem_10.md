## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_10.lean`

## Lean statement
```lean
theorem averaged_composition_constant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T1 T2 : H → H) (alpha1 alpha2 : ℝ)
    (halpha1 : 0 < alpha1 ∧ alpha1 < 1) (halpha2 : 0 < alpha2 ∧ alpha2 < 1)
    (hT1 : IsAveragedOperator T1 alpha1 halpha1) (hT2 : IsAveragedOperator T2 alpha2 halpha2) :
    let delta
```

## Statement explanation
The theorem involves a type \(H\) equipped with a normed additive commutative group structure and a real inner product space structure. It considers two self-maps \(T_1,T_2:H\to H\), real parameters \(\alpha_1,\alpha_2\), and hypotheses

- \(h\alpha_1:0<\alpha_1\wedge \alpha_1<1\),
- \(h\alpha_2:0<\alpha_2\wedge \alpha_2<1\),
- \(h_{T_1}:\) \(T_1\) is \(\alpha_1\)-averaged, expressed as `IsAveragedOperator T1 alpha1 halpha1`,
- \(h_{T_2}:\) \(T_2\) is \(\alpha_2\)-averaged, expressed as `IsAveragedOperator T2 alpha2 halpha2`.

The conclusion defines a real number
\[
\delta = \frac12+\frac12\min\left(\frac1{\alpha_1},\frac1{\alpha_2}\right),
\]
then defines
\[
\alpha=\frac1\delta,
\]
and asserts that the composition \(T_1\circ T_2\) is \(\alpha\)-averaged. Because the predicate `IsAveragedOperator` requires a proof that the averaging parameter lies strictly between \(0\) and \(1\), the statement also includes an inline proof of
\[
0<\alpha<1.
\]

## Lean proof
```lean
(1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)
    let alpha := 1 / delta
    IsAveragedOperator (T1 ∘ T2) alpha (by
      change 0 < 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) ∧
        1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) < 1
      have hrecip1 : 1 < (1 / alpha1 : ℝ) := (one_lt_div halpha1.1).mpr halpha1.2
      have hrecip2 : 1 < (1 / alpha2 : ℝ) := (one_lt_div halpha2.1).mpr halpha2.2
      have hdelta_gt_one :
          1 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
        nlinarith [lt_min hrecip1 hrecip2]
      have hdelta_pos :
          0 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
        linarith
      exact ⟨one_div_pos.mpr hdelta_pos,
        (div_lt_one hdelta_pos).mpr hdelta_gt_one⟩) := by
  dsimp only
  have hrecip1 : 1 < (1 / alpha1 : ℝ) := (one_lt_div halpha1.1).mpr halpha1.2
  have hrecip2 : 1 < (1 / alpha2 : ℝ) := (one_lt_div halpha2.1).mpr halpha2.2
  have hdelta_gt_one : 1 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
    nlinarith [lt_min hrecip1 hrecip2]
  have hdelta_pos : 0 < (1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2) := by
    linarith
  have halpha :
      0 < 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) ∧
        1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) < 1 :=
    ⟨one_div_pos.mpr hdelta_pos, (div_lt_one hdelta_pos).mpr hdelta_gt_one⟩
  let U1 : ↥(Set.univ : Set H) → ↥(Set.univ : Set H) :=
    fun x => ⟨T1 (x : H), Set.mem_univ _⟩
  let U2 : ↥(Set.univ : Set H) → ↥(Set.univ : Set H) :=
    fun x => ⟨T2 (x : H), Set.mem_univ _⟩
  have hU1 : AveragedWith alpha1 (fun x : Set.univ => (U1 x : H)) := by
    simpa [U1] using
      (isAveragedOperator_iff_averagedWith T1 alpha1 halpha1).mp hT1
  have hU2 : AveragedWith alpha2 (fun x : Set.univ => (U2 x : H)) := by
    simpa [U2] using
      (isAveragedOperator_iff_averagedWith T2 alpha2 halpha2).mp hT2
  let c : ℝ := compositionAveragingConstant alpha1 alpha2
  have hcomp : AveragedWith c (fun x : Set.univ => (U1 (U2 x) : H)) := by
    simpa [c] using (averagedWith_comp (T₁ := U1) (T₂ := U2) hU1 hU2)
  have hden_pos : 0 < 1 - alpha1 * alpha2 := by
    nlinarith [halpha1.1, halpha1.2, halpha2.1, halpha2.2]
  have h_c_le_alpha :
      c ≤ 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)) := by
    rcases le_total alpha1 alpha2 with h12 | h21
    · have hrecip : 1 / alpha2 ≤ 1 / alpha1 := one_div_le_one_div_of_le halpha1.1 h12
      rw [min_eq_right hrecip]
      dsimp [c, compositionAveragingConstant]
      have hsum_pos : 0 < 1 + alpha2 := by linarith [halpha2.1]
      have hpaper_alpha : 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (1 / alpha2)) =
          2 * alpha2 / (1 + alpha2) := by
        field_simp [ne_of_gt halpha2.1, ne_of_gt hsum_pos]
        rw [add_comm alpha2 1]
        exact div_self (ne_of_gt hsum_pos)
      have hnonneg : 0 ≤ (alpha2 - alpha1) * (1 - alpha2) :=
        mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr halpha2.2.le)
      rw [hpaper_alpha]
      apply (div_le_div_iff₀ hden_pos hsum_pos).2
      nlinarith
    · have hrecip : 1 / alpha1 ≤ 1 / alpha2 := one_div_le_one_div_of_le halpha2.1 h21
      rw [min_eq_left hrecip]
      dsimp [c, compositionAveragingConstant]
      have hsum_pos : 0 < 1 + alpha1 := by linarith [halpha1.1]
      have hpaper_alpha : 1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (1 / alpha1)) =
          2 * alpha1 / (1 + alpha1) := by
        field_simp [ne_of_gt halpha1.1, ne_of_gt hsum_pos]
        rw [add_comm alpha1 1]
        exact div_self (ne_of_gt hsum_pos)
      have hnonneg : 0 ≤ (alpha1 - alpha2) * (1 - alpha1) :=
        mul_nonneg (sub_nonneg.mpr h21) (sub_nonneg.mpr halpha1.2.le)
      rw [hpaper_alpha]
      apply (div_le_div_iff₀ hden_pos hsum_pos).2
      nlinarith
  have hpaper : AveragedWith (1 / ((1 / 2 : ℝ) + (1 / 2 : ℝ) * min (1 / alpha1) (1 / alpha2)))
      (fun x : Set.univ => (U1 (U2 x) : H)) :=
    averagedWith_mono_parameter hcomp halpha h_c_le_alpha
  simpa [U1, U2, Function.comp_def] using hpaper
```

## Proof explanation
The theorem statement itself first verifies the required parameter bounds for \(\alpha=1/\delta\). The inline proof uses `change` to rewrite the goal as
\[
0<\frac1\delta\wedge \frac1\delta<1,
\]
where \(\delta\) is expanded. It derives
\[
1<\frac1{\alpha_1}
\]
and
\[
1<\frac1{\alpha_2}
\]
from \(0<\alpha_1<1\) and \(0<\alpha_2<1\) using `one_lt_div`. Then `lt_min` gives
\[
1<\min\left(\frac1{\alpha_1},\frac1{\alpha_2}\right),
\]
and `nlinarith` proves
\[
1<\frac12+\frac12\min\left(\frac1{\alpha_1},\frac1{\alpha_2}\right).
\]
This is `hdelta_gt_one`. From it, `linarith` proves that \(\delta>0\). Finally, `one_div_pos` proves \(1/\delta>0\), and `div_lt_one` combined with \(1<\delta\) proves \(1/\delta<1\).

The main proof begins with `dsimp only`, which unfolds the local definitions `delta` and `alpha` in the goal. It then repeats the inequalities \(1<1/\alpha_1\), \(1<1/\alpha_2\), \(\delta>1\), \(\delta>0\), and the valid parameter bounds for \(\alpha=1/\delta\). These are recorded as local hypotheses for later use.

The proof then moves the maps to the full subtype \(\operatorname{Set.univ}\) of \(H\). It defines
\[
U_1,U_2:\operatorname{Set.univ}\to \operatorname{Set.univ}
\]
by
\[
U_i(x)=\langle T_i(x),\operatorname{mem\_univ}(x)\rangle,
\]
so \(U_i\) is essentially \(T_i\) viewed on the whole-space subtype. The commands `simpa [U1] using ...` and `simpa [U2] using ...` convert the given `IsAveragedOperator` hypotheses \(h_{T_1},h_{T_2}\) into corresponding `AveragedWith` statements for \(U_1,U_2\), using the lemma `isAveragedOperator_iff_averagedWith`.

Next, the proof introduces a library constant
\[
c:=\operatorname{compositionAveragingConstant}(\alpha_1,\alpha_2).
\]
Using the composition lemma `averagedWith_comp`, it proves that the composition \(U_1\circ U_2\) is \(c\)-averaged:
\[
\operatorname{AveragedWith} c\;(\lambda x,\ (U_1(U_2 x):H)).
\]
This is the local hypothesis `hcomp`.

The proof then compares \(c\) with the desired parameter \(1/\delta\). First it proves
\[
0<1-\alpha_1\alpha_2
\]
by `nlinarith` from \(0<\alpha_1<1\) and \(0<\alpha_2<1\). Then it proves
\[
c\le \frac1\delta.
\]
This is the main algebraic estimate. It splits on whether \(\alpha_1\le \alpha_2\) or \(\alpha_2\le \alpha_1\) using `rcases le_total alpha1 alpha2 with h12 | h21`.

In the first case, \(\alpha_1\le \alpha_2\). Then
\[
\frac1{\alpha_2}\le \frac1{\alpha_1},
\]
so `rw [min_eq_right hrecip]` replaces
\[
\min\left(\frac1{\alpha_1},\frac1{\alpha_2}\right)
\]
by \(1/\alpha_2\). After `dsimp [c, compositionAveragingConstant]`, the proof uses `field_simp` to show
\[
\frac1{\frac12+\frac12\cdot \frac1{\alpha_2}}
=
\frac{2\alpha_2}{1+\alpha_2}.
\]
It also proves the nonnegativity
\[
0\le (\alpha_2-\alpha_1)(1-\alpha_2)
\]
from \(\alpha_1\le \alpha_2\) and \(\alpha_2<1\). It then uses the positive-denominator fraction comparison lemma `div_le_div_iff₀` and finishes the inequality with `nlinarith`.

The second case, \(\alpha_2\le \alpha_1\), is symmetric. It uses
\[
\frac1{\alpha_1}\le \frac1{\alpha_2},
\]
replaces the minimum by \(1/\alpha_1\), proves
\[
\frac1{\frac12+\frac12\cdot \frac1{\alpha_1}}
=
\frac{2\alpha_1}{1+\alpha_1},
\]
and uses the nonnegativity
\[
0\le (\alpha_1-\alpha_2)(1-\alpha_1)
\]
to finish again by `nlinarith`.

Thus the proof has
\[
c\le \frac1\delta.
\]
Since \(hcomp\) says the composition is \(c\)-averaged, and the desired parameter \(\alpha=1/\delta\) satisfies \(0<\alpha<1\), the monotonicity lemma
\[
\operatorname{averagedWith\_mono\_parameter}
\]
is applied with `hcomp`, `halpha`, and `h_c_le_alpha` to conclude that the composition is also \(1/\delta\)-averaged:
\[
\operatorname{AveragedWith}\left(\frac1\delta\right)\;(\lambda x,\ (U_1(U_2 x):H)).
\]
Finally, `simpa [U1, U2, Function.comp_def]` simplifies this statement back to the desired goal, showing that \(T_1\circ T_2\) is \(\alpha\)-averaged.

