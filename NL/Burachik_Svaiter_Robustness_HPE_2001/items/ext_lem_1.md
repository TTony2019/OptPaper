## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/ext_lem_1.lean`

## Lean statement
```lean
theorem polyak_scalar_convergence (α δ γ : ℕ → ℝ)
    (hα : ∀ k, 0 ≤ α k) (hδ : ∀ k, 0 ≤ δ k) (hγ : ∀ k, 0 ≤ γ k)
    (hsα : Summable α) (hsδ : Summable δ)
    (hrec : ∀ k, γ (k + 1) ≤ α k + Real.sqrt (γ k ^ 2 + δ k)) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto γ Filter.atTop (nhds L)
```

## Statement explanation
The declaration `polyak_scalar_convergence` concerns three real sequences
\(\alpha,\delta,\gamma:\mathbb N\to\mathbb R\). It assumes that all their terms are nonnegative:
\[
\forall k,\ 0\le \alpha_k,\qquad \forall k,\ 0\le \delta_k,\qquad \forall k,\ 0\le \gamma_k.
\]
It also assumes that the series of \(\alpha\) and \(\delta\) are summable:
\[
\sum_{k=0}^{\infty}\alpha_k \text{ converges},\qquad
\sum_{k=0}^{\infty}\delta_k \text{ converges}.
\]
The main recurrence hypothesis is that, for every \(k\),
\[
\gamma_{k+1}\le \alpha_k+\sqrt{\gamma_k^2+\delta_k}.
\]
The conclusion is that there exists a real number \(L\) such that
\[
0\le L
\]
and
\[
\gamma_k\to L\quad\text{as }k\to\infty.
\]
So the theorem says that a nonnegative scalar sequence controlled by a square-root recurrence with nonnegative summable forcing terms \(\alpha\) and \(\delta\) must converge to a nonnegative limit. Summability of \(\alpha\) and \(\delta\) means their tails eventually become small, and the proof uses this to build a monotone bounded majorant for the relevant square-root expression.

## Lean proof
```lean
by
  let q : ℕ → ℝ := fun k => ∑' i : ℕ, δ (i + k)
  let a : ℕ → ℝ := fun k => ∑' i : ℕ, α (i + k)
  obtain ⟨hq_nonneg, hq_shift, hq_zero⟩ := polyak_tail_properties δ hδ hsδ
  obtain ⟨ha_nonneg, ha_shift, ha_zero⟩ := polyak_tail_properties α hα hsα
  have hq_nonneg' : ∀ k, 0 ≤ q k := by simpa [q] using hq_nonneg
  have ha_nonneg' : ∀ k, 0 ≤ a k := by simpa [a] using ha_nonneg
  have hq_shift' : ∀ k, q k = δ k + q (k + 1) := by simpa [q] using hq_shift
  have ha_shift' : ∀ k, a k = α k + a (k + 1) := by simpa [a] using ha_shift
  have hq_zero' : Tendsto q Filter.atTop (nhds 0) := by simpa [q] using hq_zero
  have ha_zero' : Tendsto a Filter.atTop (nhds 0) := by simpa [a] using ha_zero
  let s : ℕ → ℝ := fun k => Real.sqrt (γ k ^ 2 + q k)
  have hs_step : ∀ k, s (k + 1) ≤ α k + s k := by
    intro k
    have hsq : γ (k + 1) ^ 2 ≤ (α k + Real.sqrt (γ k ^ 2 + δ k)) ^ 2 :=
      (sq_le_sq₀ (hγ (k + 1)) (add_nonneg (hα k) (Real.sqrt_nonneg _))).2 (hrec k)
    have hrad : γ (k + 1) ^ 2 + q (k + 1) ≤
        (α k + Real.sqrt (γ k ^ 2 + δ k)) ^ 2 + q (k + 1) := by linarith
    calc
      s (k + 1) ≤ Real.sqrt ((α k + Real.sqrt (γ k ^ 2 + δ k)) ^ 2 + q (k + 1)) := by
        exact Real.sqrt_le_sqrt hrad
      _ ≤ α k + Real.sqrt ((γ k ^ 2 + δ k) + q (k + 1)) :=
        polyak_sqrt_bridge (hα k) (add_nonneg (sq_nonneg _) (hδ k)) (hq_nonneg' _)
      _ = α k + s k := by
        simp only [s]
        rw [show γ k ^ 2 + δ k + q (k + 1) = γ k ^ 2 + (δ k + q (k + 1)) by ring,
          ← hq_shift' k]
  let r : ℕ → ℝ := fun k => s k + a k
  have hr_succ : ∀ k, r (k + 1) ≤ r k := by
    intro k
    dsimp [r]
    linarith [hs_step k, ha_shift' k]
  have hr_anti : Antitone r := antitone_nat_of_succ_le hr_succ
  have hr_nonneg : ∀ k, 0 ≤ r k := fun k => add_nonneg (Real.sqrt_nonneg _) (ha_nonneg' k)
  have hr_bdd : BddBelow (Set.range r) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hr_nonneg k
  let L : ℝ := ⨅ k, r k
  have hr_lim : Tendsto r Filter.atTop (nhds L) := tendsto_atTop_ciInf hr_anti hr_bdd
  have hs_lim : Tendsto s Filter.atTop (nhds L) := by
    simpa [r, sub_eq_add_neg] using hr_lim.sub ha_zero'
  have hL_nonneg : 0 ≤ L := by
    exact ge_of_tendsto' hs_lim fun k => Real.sqrt_nonneg _
  have hdiff : ∀ k, 0 ≤ s k - γ k ∧ s k - γ k ≤ Real.sqrt (q k) := by
    intro k
    have hle : γ k ≤ s k := by
      have hsq : γ k ^ 2 ≤ γ k ^ 2 + q k := le_add_of_nonneg_right (hq_nonneg' k)
      simpa [s, Real.sqrt_sq (hγ k)] using Real.sqrt_le_sqrt hsq
    constructor
    · exact sub_nonneg.mpr hle
    · have hupper := polyak_sqrt_add_tail (hγ k) (hq_nonneg' k)
      change Real.sqrt (γ k ^ 2 + q k) ≤ γ k + Real.sqrt (q k) at hupper
      linarith
  have hsqrtq_zero : Tendsto (fun k => Real.sqrt (q k)) Filter.atTop (nhds 0) := by
    simpa using hq_zero'.sqrt
  have hdiff_zero : Tendsto (fun k => s k - γ k) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrtq_zero
    · exact Filter.Eventually.of_forall fun k => (hdiff k).1
    · exact Filter.Eventually.of_forall fun k => (hdiff k).2
  refine ⟨L, hL_nonneg, ?_⟩
  simpa [sub_eq_add_neg] using hs_lim.sub hdiff_zero
```

## Proof explanation
The proof begins by defining the tails of \(\delta\) and \(\alpha\):
\[
q_k=\sum_{i=0}^{\infty}\delta_{i+k},\qquad
a_k=\sum_{i=0}^{\infty}\alpha_{i+k}.
\]
The theorem `polyak_tail_properties` is then applied to \(\delta\) and \(\alpha\). For a nonnegative summable sequence \(u\), that result says that its tail
\[
t_k=\sum_{i=0}^{\infty}u_{i+k}
\]
satisfies three facts:
\[
\forall k,\ 0\le t_k,\qquad
\forall k,\ t_k=u_k+t_{k+1},\qquad
t_k\to 0.
\]
Applied to \(\delta\), this gives
\[
\forall k,\ 0\le q_k,\qquad
\forall k,\ q_k=\delta_k+q_{k+1},\qquad
q_k\to0.
\]
Applied to \(\alpha\), it gives
\[
\forall k,\ 0\le a_k,\qquad
\forall k,\ a_k=\alpha_k+a_{k+1},\qquad
a_k\to0.
\]
The `simpa` steps after `polyak_tail_properties` simply unfold the definitions of \(q\) and \(a\) so that these tail properties are available in the exact form needed below.

Next, the proof defines
\[
s_k=\sqrt{\gamma_k^2+q_k}.
\]
It proves the key one-step inequality
\[
s_{k+1}\le \alpha_k+s_k.
\]
To do this, it fixes an arbitrary \(k\) using `intro k`. From the recurrence hypothesis,
\[
\gamma_{k+1}\le \alpha_k+\sqrt{\gamma_k^2+\delta_k}.
\]
Both sides are nonnegative: \(\gamma_{k+1}\ge0\) by `hγ`, and
\(\alpha_k+\sqrt{\gamma_k^2+\delta_k}\ge0\) because both summands are nonnegative. Therefore squaring preserves the inequality. The theorem `sq_le_sq₀` is used here: for nonnegative real numbers \(x,y\), the inequality \(x\le y\) implies \(x^2\le y^2\). Hence
\[
\gamma_{k+1}^2\le
\left(\alpha_k+\sqrt{\gamma_k^2+\delta_k}\right)^2.
\]
Adding \(q_{k+1}\) to both sides, which is legitimate by `linarith`, gives
\[
\gamma_{k+1}^2+q_{k+1}\le
\left(\alpha_k+\sqrt{\gamma_k^2+\delta_k}\right)^2+q_{k+1}.
\]
Since the square-root function is monotone on nonnegative arguments, `Real.sqrt_le_sqrt` yields
\[
s_{k+1}
\le
\sqrt{
\left(\alpha_k+\sqrt{\gamma_k^2+\delta_k}\right)^2+q_{k+1}
}.
\]
Now the lemma `polyak_sqrt_bridge` is applied with
\[
u=\alpha_k,\qquad v=\gamma_k^2+\delta_k,\qquad w=q_{k+1}.
\]
That lemma states that for nonnegative \(u,v,w\),
\[
\sqrt{(u+\sqrt v)^2+w}\le u+\sqrt{v+w}.
\]
The hypotheses hold here: \(\alpha_k\ge0\), \(\gamma_k^2+\delta_k\ge0\) because a square is nonnegative and \(\delta_k\ge0\), and \(q_{k+1}\ge0\). Thus
\[
\sqrt{
\left(\alpha_k+\sqrt{\gamma_k^2+\delta_k}\right)^2+q_{k+1}
}
\le
\alpha_k+\sqrt{\gamma_k^2+\delta_k+q_{k+1}}.
\]
Using the tail identity \(q_k=\delta_k+q_{k+1}\), the radicand becomes
\[
\gamma_k^2+\delta_k+q_{k+1}
=\gamma_k^2+q_k.
\]
The proof performs this rearrangement with `ring`, then rewrites with the previously established identity `hq_shift'` using `rw`. Therefore the right-hand side is exactly
\[
\alpha_k+\sqrt{\gamma_k^2+q_k}=\alpha_k+s_k.
\]
This proves \(s_{k+1}\le \alpha_k+s_k\).

The proof then defines a new sequence
\[
r_k=s_k+a_k.
\]
Using \(s_{k+1}\le \alpha_k+s_k\) and the tail identity
\[
a_k=\alpha_k+a_{k+1},
\]
it obtains
\[
r_{k+1}=s_{k+1}+a_{k+1}
\le \alpha_k+s_k+a_{k+1}
=s_k+a_k=r_k.
\]
The `dsimp [r]` unfolds \(r\), and `linarith` combines the two inequalities. Thus \(r\) is nonincreasing. The theorem `antitone_nat_of_succ_le` converts the adjacent-step inequality \(\forall k,\ r_{k+1}\le r_k\) into the statement that \(r\) is antitone, i.e.
\[
i\le j\implies r_j\le r_i.
\]

The sequence \(r\) is also nonnegative, because each \(s_k=\sqrt{\gamma_k^2+q_k}\) is nonnegative and each \(a_k\) is a tail of the nonnegative sequence \(\alpha\). Hence \(0\) is a lower bound for the range of \(r\). The proof defines
\[
L=\inf_{k} r_k.
\]
Since \(r\) is antitone and bounded below, the theorem `tendsto_atTop_ciInf` gives
\[
r_k\to L
\]
as \(k\to\infty\).

Because \(r_k=s_k+a_k\), we have \(s_k=r_k-a_k\). Since \(r_k\to L\) and \(a_k\to0\), subtracting limits gives
\[
s_k\to L-0=L.
\]
This is the step `hr_lim.sub ha_zero'`, followed by `simpa [r, sub_eq_add_neg]` to identify the resulting sequence with \(s\).

The proof then shows that \(L\ge0\). Indeed, every \(s_k\) is a square root, hence \(s_k\ge0\), and \(s_k\to L\). The lemma `ge_of_tendsto'` states that if a sequence converges to \(L\) and every term is at least \(0\), then \(0\le L\). Therefore
\[
0\le L.
\]

To connect \(s_k\) back to \(\gamma_k\), the proof proves for every \(k\) that
\[
0\le s_k-\gamma_k\le \sqrt{q_k}.
\]
First, since \(\gamma_k\ge0\) and \(q_k\ge0\),
\[
\gamma_k^2\le \gamma_k^2+q_k.
\]
Monotonicity of the square root gives
\[
\sqrt{\gamma_k^2}\le \sqrt{\gamma_k^2+q_k}=s_k.
\]
Because \(\gamma_k\ge0\), `Real.sqrt_sq` gives \(\sqrt{\gamma_k^2}=\gamma_k\). Hence \(\gamma_k\le s_k\), so \(s_k-\gamma_k\ge0\). For the upper bound, the lemma `polyak_sqrt_add_tail` is applied with \(x=\gamma_k\) and \(q=q_k\). That lemma says that for nonnegative \(x,q\),
\[
\sqrt{x^2+q}\le x+\sqrt q.
\]
Thus
\[
s_k=\sqrt{\gamma_k^2+q_k}\le \gamma_k+\sqrt{q_k},
\]
which rearranges to
\[
s_k-\gamma_k\le \sqrt{q_k}.
\]

Since \(q_k\to0\), applying the continuous square-root function gives
\[
\sqrt{q_k}\to0.
\]
The proof obtains this as `hq_zero'.sqrt`. The inequalities
\[
0\le s_k-\gamma_k\le \sqrt{q_k}
\]
then allow a squeeze argument. The theorem `tendsto_of_tendsto_of_tendsto_of_le_of_le'` says that if a sequence is eventually bounded between two sequences that both tend to the same limit, then it also tends to that limit. Here the lower bound is the constant sequence \(0\to0\), the upper bound is \(\sqrt{q_k}\to0\), and the middle sequence is \(s_k-\gamma_k\). Hence
\[
s_k-\gamma_k\to0.
\]

Finally, since
\[
\gamma_k=s_k-(s_k-\gamma_k),
\]
and we have shown
\[
s_k\to L,\qquad s_k-\gamma_k\to0,
\]
subtracting the limits gives
\[
\gamma_k\to L.
\]
The final `simpa [sub_eq_add_neg] using hs_lim.sub hdiff_zero` carries out exactly this subtraction and rewrites \(s_k-(s_k-\gamma_k)\) as \(\gamma_k\). Together with \(0\le L\), this proves the existence of the required nonnegative limit \(L\).

