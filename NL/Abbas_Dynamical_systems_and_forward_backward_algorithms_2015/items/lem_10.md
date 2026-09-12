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
The declaration `averaged_composition_constant` is set in a real inner product space $H$. It takes two self-maps $T_1,T_2:H\to H$, two real numbers $\alpha_1,\alpha_2$, hypotheses

$$
0<\alpha_1<1,\qquad 0<\alpha_2<1,
$$

and hypotheses that $T_1$ is an $\alpha_1$-averaged operator and $T_2$ is an $\alpha_2$-averaged operator.

The relevant notion of averagedness is `AveragedWith`: for a map $T:D\to H$ on a set $D\subseteq H$, being $\alpha$-averaged means that $\alpha\in(0,1)$ and there exists a $1$-Lipschitz map $R:D\to H$ such that

$$
T(x)=(1-\alpha)x+\alpha R(x)
$$

for every $x\in D$. Thus $T$ is a convex combination, with weight $\alpha$, of the identity and a nonexpansive map. The definition `IsAveragedOperator T α hα` is the whole-space version of this condition, where $D$ is the universal subset of $H$. The proof argument $hα$ records $0<\alpha<1$, although the definition itself is just the corresponding `AveragedWith` statement on the whole space.

The conclusion introduces

$$
\delta=\frac12+\frac12\min\!\left(\frac1{\alpha_1},\frac1{\alpha_2}\right),
\qquad
\alpha=\frac1\delta,
$$

and asserts that the composition $T_1\circ T_2$ is an $\alpha$-averaged operator. Equivalently,

$$
\alpha=\frac{2}{1+\min(1/\alpha_1,1/\alpha_2)}.
$$

The declaration also contains the necessary proof that this $\alpha$ lies in $(0,1)$. In ordinary language: the composition of an $\alpha_1$-averaged map and an $\alpha_2$-averaged map is again averaged, and one explicit admissible averaging parameter for the composition is the reciprocal of the average of $1$ and the smaller of the two reciprocals $1/\alpha_1,1/\alpha_2$.

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
The proof first discharges the side condition that the proposed number

$$
\alpha=\frac1{\frac12+\frac12\min(1/\alpha_1,1/\alpha_2)}
$$

lies in $(0,1)$. The nested proof uses `change` to replace the let-bound expression for $\alpha$ by the explicit reciprocal. Since $0<\alpha_1<1$, the lemma `one_lt_div` applied with the positive denominator $\alpha_1$ gives the equivalence

$$
1<\frac1{\alpha_1}\iff \alpha_1<1,
$$

so the hypothesis $\alpha_1<1$ yields $1<1/\alpha_1$. Similarly, from $0<\alpha_2<1$, one obtains $1<1/\alpha_2$. The lemma `lt_min` then gives

$$
1<\min\!\left(\frac1{\alpha_1},\frac1{\alpha_2}\right).
$$

Therefore

$$
\delta=\frac12+\frac12\min\!\left(\frac1{\alpha_1},\frac1{\alpha_2}\right)>1,
$$

which `nlinarith` verifies. Hence also $\delta>0$, and then `one_div_pos` gives $0<1/\delta$, while `div_lt_one`, using positivity of $\delta$, gives

$$
\frac1\delta<1 \iff 1<\delta.
$$

Thus $0<\alpha<1$. The main proof repeats the same reciprocal, minimum, and positivity estimates to obtain the fact named `halpha`.

Next the proof passes from whole-space maps to maps on the universal subtype. It defines

$$
U_1(x)=T_1(x),\qquad U_2(x)=T_2(x)
$$

for $x$ in the subtype `Set.univ` of $H$. The equivalence `isAveragedOperator_iff_averagedWith` states that for a map $T:H\to H$ and a parameter $\alpha$ with $0<\alpha<1$, being an averaged operator on all of $H$ is equivalent to being $\alpha$-averaged as a map on the universal subset. Applying this equivalence to `hT1` and `hT2` gives

$$
\text{`AveragedWith` }\alpha_1\ U_1,\qquad
\text{`AveragedWith` }\alpha_2\ U_2.
$$

The proof then sets

$$
c=\operatorname{compositionAveragingConstant}(\alpha_1,\alpha_2)
=\frac{\alpha_1+\alpha_2-2\alpha_1\alpha_2}{1-\alpha_1\alpha_2}.
$$

The cited theorem `averagedWith_comp` says that if $U_1$ is $\alpha_1$-averaged and $U_2$ is $\alpha_2$-averaged, then their composition $U_1\circ U_2$ is averaged with parameter $c$. This gives the fact `hcomp`.

The proof also records that

$$
1-\alpha_1\alpha_2>0,
$$

which follows from $0<\alpha_i<1$; `nlinarith` derives it from the four inequalities $0<\alpha_1$, $\alpha_1<1$, $0<\alpha_2$, $\alpha_2<1$. This positivity is needed because $c$ has denominator $1-\alpha_1\alpha_2$.

The main comparison to be proved is

$$
c\le \frac1{\frac12+\frac12\min(1/\alpha_1,1/\alpha_2)}.
$$

The proof splits into the two cases $\alpha_1\le\alpha_2$ and $\alpha_2\le\alpha_1$, using `le_total`.

If $\alpha_1\le\alpha_2$, then since $\alpha_1>0$, reciprocals reverse the inequality, so

$$
\frac1{\alpha_2}\le\frac1{\alpha_1}.
$$

Thus the minimum is $1/\alpha_2$, and the right-hand side becomes

$$
\frac1{\frac12+\frac12\cdot\frac1{\alpha_2}}
=\frac{2\alpha_2}{1+\alpha_2}.
$$

The lemma `field_simp` clears denominators in this algebraic identity, using $\alpha_2>0$ and $1+\alpha_2>0$. To prove

$$
\frac{\alpha_1+\alpha_2-2\alpha_1\alpha_2}{1-\alpha_1\alpha_2}
\le \frac{2\alpha_2}{1+\alpha_2},
$$

the proof uses `div_le_div_iff₀` with positive denominators to reduce to the cross-multiplied inequality

$$
(\alpha_1+\alpha_2-2\alpha_1\alpha_2)(1+\alpha_2)
\le 2\alpha_2(1-\alpha_1\alpha_2).
$$

The difference of the right side minus the left side is

$$
(\alpha_2-\alpha_1)(1-\alpha_2),
$$

which is nonnegative because $\alpha_1\le\alpha_2$ and $\alpha_2<1$. This nonnegativity is `hnonneg`, and `nlinarith` closes the inequality.

The case $\alpha_2\le\alpha_1$ is symmetric. Then

$$
\frac1{\alpha_1}\le\frac1{\alpha_2},
$$

so the minimum is $1/\alpha_1$, and the right-hand side becomes

$$
\frac1{\frac12+\frac12\cdot\frac1{\alpha_1}}
=\frac{2\alpha_1}{1+\alpha_1}.
$$

After cross-multiplication, the difference of the right and left sides is

$$
(\alpha_1-\alpha_2)(1-\alpha_1)\ge 0,
$$

again because $\alpha_2\le\alpha_1$ and $\alpha_1<1$. Hence $c\le\alpha$ in both cases.

Once the estimate $c\le\alpha$ is available, the proof applies `averagedWith_mono_parameter`. That lemma says that if a map is $a$-averaged, if $b\in(0,1)$, and if $a\le b$, then the same map is also $b$-averaged. Here $a=c$, $b=\alpha=1/\delta$, and the earlier facts give $c\le\alpha$ and $\alpha\in(0,1)$. Therefore $U_1\circ U_2$ is averaged with parameter $\alpha$, yielding `hpaper`.

Finally, `simpa [U1, U2, Function.comp_def] using hpaper` rewrites the restricted composition $U_1(U_2(x))$ back to $T_1(T_2(x))$, i.e. to $(T_1\circ T_2)(x)$. Thus the averagedness obtained for the restricted maps is exactly the desired conclusion that $T_1\circ T_2$ is an $\alpha$-averaged operator.

