## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/cor_3.lean`

## Lean statement
```lean
theorem hpe_asymptotics {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T)
    (hzero : ∃ xStar, (0 : H) ∈ T xStar) :
    Bornology.IsBounded (Set.range A.x) ∧
    Tendsto (fun k ↦ ‖A.y k - A.x k‖) Filter.atTop (nhds 0) ∧
    Tendsto A.ε Filter.atTop (nhds 0) ∧
    Tendsto (fun k ↦ ‖A.v k‖) Filter.atTop (nhds 0) ∧
    Tendsto (fun k ↦ ‖A.c k • A.v k‖) Filter.atTop (nhds 0)
```

## Statement explanation
The declaration `hpe_asymptotics` is stated for a real inner-product space $H$, a set-valued operator $T:H\to 2^H$, and an HPE-iterate object $A$ associated with $T$. The object $A$ carries sequences $x_k,y_k,v_k\in H$ and scalar sequences $c_k,\sigma_k,\delta_k,\alpha_k,\varepsilon_k\in\mathbb R$. The hypothesis is

$$
\exists x^*\in H,\qquad 0\in T x^*,
$$

so $x^*$ is a zero of the set-valued operator $T$. Under this hypothesis, the theorem concludes the conjunction of five asymptotic statements:

1. the range $\{x_k:k\in\mathbb N\}$ is bounded;
2. $\displaystyle \|y_k-x_k\|\to 0$ as $k\to\infty$;
3. $\displaystyle \varepsilon_k\to 0$;
4. $\displaystyle \|v_k\|\to 0$;
5. $\displaystyle \|c_k v_k\|\to 0$.

Thus the HPE iterates are bounded, and several natural residual or error quantities vanish asymptotically: the displacement between $y_k$ and $x_k$, the scalar error $\varepsilon_k$, the vector $v_k$, and its scaled version $c_k v_k$. The statement does not assert convergence of the sequence $x_k$ itself, only boundedness of its range.

## Lean proof
```lean
by
  rcases hzero with ⟨xStar, hxStar⟩
  rcases hpe_distance_converges A hxStar with ⟨L, hL0, hDist⟩
  have hδ0 : Tendsto A.δ Filter.atTop (nhds 0) := A.summable_delta.tendsto_atTop_zero
  have hα0 : Tendsto A.α Filter.atTop (nhds 0) := A.summable_alpha.tendsto_atTop_zero
  have hxBounded : Bornology.IsBounded (Set.range A.x) := by
    rcases isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ hDist) with ⟨C, hC⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖xStar‖, ?_⟩
    rintro z ⟨k, rfl⟩
    have hk : ‖A.x k - xStar‖ ≤ C := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC _ ⟨k, rfl⟩
    calc
      ‖A.x k‖ = ‖(A.x k - xStar) + xStar‖ := congrArg norm (by abel)
      _ ≤ ‖A.x k - xStar‖ + ‖xStar‖ := norm_add_le _ _
      _ ≤ C + ‖xStar‖ := add_le_add_left hk _
  have hDistSucc : Tendsto (fun k ↦ ‖A.x (k + 1) - xStar‖) Filter.atTop (nhds L) := by
    exact hDist.comp (Filter.tendsto_add_atTop_nat 1)
  have hExactDist : Tendsto (fun k ↦ ‖extragradientStep A k - xStar‖)
      Filter.atTop (nhds L) := by
    have herr0 : Tendsto (fun k ↦ ‖extragradientStep A k - xStar‖ -
        ‖A.x (k + 1) - xStar‖) Filter.atTop (nhds 0) := by
      have hneg0 : Tendsto (fun k ↦ -A.α k) Filter.atTop (nhds 0) := by
        simpa using hα0.neg
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg0 hα0
        (fun k => by
          have h := A.update_error k
          have hrev := abs_norm_sub_norm_le (extragradientStep A k - xStar)
            (A.x (k + 1) - xStar)
          rw [show (extragradientStep A k - xStar) - (A.x (k + 1) - xStar) =
              extragradientStep A k - A.x (k + 1) by abel, norm_sub_rev] at hrev
          have h' : ‖extragradientStep A k - A.x (k + 1)‖ ≤ A.α k := by
            simpa [extragradientStep, norm_sub_rev] using h
          simpa [norm_sub_rev] using (abs_le.mp (hrev.trans h')).1)
        (fun k => by
          have h := A.update_error k
          have hrev := abs_norm_sub_norm_le (extragradientStep A k - xStar)
            (A.x (k + 1) - xStar)
          rw [show (extragradientStep A k - xStar) - (A.x (k + 1) - xStar) =
              extragradientStep A k - A.x (k + 1) by abel, norm_sub_rev] at hrev
          have h' : ‖extragradientStep A k - A.x (k + 1)‖ ≤ A.α k := by
            simpa [extragradientStep, norm_sub_rev] using h
          simpa [norm_sub_rev] using (abs_le.mp (hrev.trans h')).2)
    simpa [sub_add_cancel] using herr0.add hDistSucc
  rcases A.sigma_bound with ⟨σbar, hσbar_pos, hσbar_lt_one, hσ⟩
  let q : ℝ := 1 - σbar ^ 2
  have hq : 0 < q := by dsimp [q]; nlinarith
  have hdispSqLe : ∀ k, q * ‖A.y k - A.x k‖ ^ 2 ≤
      ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 + A.δ k := by
    intro k
    have hs := hσ k
    have hsSq : A.σ k ^ 2 ≤ σbar ^ 2 :=
      (sq_le_sq₀ (A.σ_nonneg k) hσbar_pos.le).mpr hs.2
    have hd := hpe_descent A hxStar k
    dsimp [q]
    nlinarith
  have hright0 : Tendsto (fun k ↦
      ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 + A.δ k)
      Filter.atTop (nhds 0) := by
    have h1 : Tendsto (fun k ↦ ‖xStar - A.x k‖ ^ 2) Filter.atTop (nhds (L ^ 2)) := by
      simpa [norm_sub_rev] using hDist.pow 2
    have h2 : Tendsto (fun k ↦ ‖xStar - extragradientStep A k‖ ^ 2)
        Filter.atTop (nhds (L ^ 2)) := by
      simpa [norm_sub_rev] using hExactDist.pow 2
    simpa using (h1.sub h2).add hδ0
  have hdisp : Tendsto (fun k ↦ ‖A.y k - A.x k‖) Filter.atTop (nhds 0) := by
    refine hpe_tendsto_norm_of_sq_le (u := fun k => ‖A.y k - A.x k‖)
      (b := fun k => (‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 + A.δ k) / q)
      (fun k => norm_nonneg _) ?_ ?_
    · simpa [div_eq_mul_inv] using hright0.mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => q⁻¹) Filter.atTop (nhds q⁻¹))
    · intro k
      exact (le_div_iff₀ hq).mpr (by simpa [mul_comm] using hdispSqLe k)
  have hprod0 : Tendsto (fun k ↦ (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hr0 : Tendsto (fun k ↦ ‖A.y k - A.x k‖ ^ 2) Filter.atTop (nhds 0) :=
      by simpa using hdisp.pow 2
    have hupper : Tendsto (fun k ↦ σbar ^ 2 * ‖A.y k - A.x k‖ ^ 2)
        Filter.atTop (nhds 0) := by simpa using tendsto_const_nhds.mul hr0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro k; positivity
    · intro k
      have hs := hσ k
      have hsSq : A.σ k ^ 2 ≤ σbar ^ 2 :=
        (sq_le_sq₀ (A.σ_nonneg k) hσbar_pos.le).mpr hs.2
      exact mul_le_mul_of_nonneg_right hsSq (sq_nonneg _)
  have hb0 : Tendsto (fun k ↦ A.δ k + (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2)
      Filter.atTop (nhds 0) := by simpa using hδ0.add hprod0
  let R : ℕ → H := fun k => A.c k • A.v k + A.y k - A.x k
  have hRSqLe : ∀ k, ‖R k‖ ^ 2 ≤ A.δ k + (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2 := by
    intro k
    have hr := A.residual_bound k
    dsimp [R]
    nlinarith [mul_nonneg (le_of_lt (A.c_pos k)) (A.ε_nonneg k)]
  have hR0 : Tendsto (fun k ↦ ‖R k‖) Filter.atTop (nhds 0) :=
    hpe_tendsto_norm_of_sq_le (fun k => norm_nonneg _) hb0 hRSqLe
  rcases A.c_lower_bound with ⟨cbar, hcbar_pos, hcbar_le⟩
  have hε0 : Tendsto A.ε Filter.atTop (nhds 0) := by
    refine hpe_tendsto_of_le_div_const (c := 2 * cbar) (by nlinarith) A.ε_nonneg hb0 ?_
    intro k
    have hr := A.residual_bound k
    have hc := hcbar_le k
    nlinarith [sq_nonneg ‖R k‖, mul_nonneg (le_of_lt (A.c_pos k)) (A.ε_nonneg k)]
  have hcv0 : Tendsto (fun k ↦ ‖A.c k • A.v k‖) Filter.atTop (nhds 0) := by
    have hsum : Tendsto (fun k ↦ ‖R k‖ + ‖A.y k - A.x k‖) Filter.atTop (nhds 0) := by
      simpa using hR0.add hdisp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    · intro k; exact norm_nonneg _
    · intro k
      have htri := norm_sub_le (R k) (A.y k - A.x k)
      have heq : A.c k • A.v k = R k - (A.y k - A.x k) := by
        dsimp [R]; abel
      change ‖A.c k • A.v k‖ ≤ ‖R k‖ + ‖A.y k - A.x k‖
      rw [heq]
      exact htri
  have hv0 : Tendsto (fun k ↦ ‖A.v k‖) Filter.atTop (nhds 0) := by
    refine hpe_tendsto_of_le_div_const (c := cbar) hcbar_pos (fun k => norm_nonneg _) hcv0 ?_
    intro k
    calc
      cbar * ‖A.v k‖ ≤ A.c k * ‖A.v k‖ :=
        mul_le_mul_of_nonneg_right (hcbar_le k) (norm_nonneg _)
      _ = ‖A.c k • A.v k‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (A.c_pos k)]
  exact ⟨hxBounded, hdisp, hε0, hv0, hcv0⟩
```

## Proof explanation
The proof proceeds by extracting the assumed zero $x^*$, obtaining convergence of the distance from $x_k$ to $x^*$, and then squeezing several residual sequences to $0$.

1. The hypothesis $hzero$ is destructed by `rcases hzero with ⟨xStar, hxStar⟩`, producing a point $x^*$ and the membership $0\in T x^*$. The theorem `hpe_distance_converges` is then applied to $A$ and $x^*$. Its content is that for an HPE iterate $A$ for $T$ and a zero $x^*$ of $T$, there exists $L\ge 0$ such that

$$
\|x_k-x^*\|\to L.
$$

The proof therefore obtains $L$, the inequality $0\le L$, and the convergence `hDist`.

2. The proof next uses the HPE-iterate fields `A.summable_delta` and `A.summable_alpha`. The invoked lemma `tendsto_atTop_zero` gives, respectively,

$$
\delta_k\to 0,\qquad \alpha_k\to 0.
$$

These are the error-type scalar sequences appearing in the HPE inequalities.

3. To prove boundedness of $\{x_k\}$, the proof uses the fact that a convergent sequence has bounded range. From `hDist`, the real sequence $k\mapsto \|x_k-x^*\|$ is bounded. The lemma `Metric.isBounded_range_of_tendsto` supplies boundedness of this range, and `isBounded_iff_forall_norm_le` converts that into a constant $C$ such that

$$
\|x_k-x^*\|\le C
$$

for every $k$. Then for any $x_k$ in the range,

$$
\|x_k\|
= \|(x_k-x^*)+x^*\|
\le \|x_k-x^*\|+\|x^*\|
\le C+\|x^*\|.
$$

The `calc` block carries out exactly this chain, using the triangle inequality `norm_add_le` and monotonicity of addition. Hence the range of $x$ is bounded.

4. The proof next shows that the exact extragradient point has the same limiting distance to $x^*$ as the actual next iterate. By definition,

$$
\mathrm{extragradientStep} A k=x_k-c_k v_k.
$$

The sequence $k\mapsto \|x_{k+1}-x^*\|$ still tends to $L$, by shifting the index by $1$ using `Filter.tendsto_add_atTop_nat 1`.

The HPE field `A.update_error k` says that the next iterate approximates the extragradient step within $\alpha_k$:

$$
\|(x_k-c_k v_k)-x_{k+1}\|\le \alpha_k.
$$

Using the reverse triangle inequality `abs_norm_sub_norm_le`, the proof obtains

$$
\left|\|x_k-c_kv_k-x^*\|-\|x_{k+1}-x^*\|\right|
\le \|(x_k-c_kv_k)-x_{k+1}\|
\le \alpha_k.
$$

Since both $-\alpha_k\to 0$ and $\alpha_k\to 0$, the squeeze lemma
`tendsto_of_tendsto_of_tendsto_of_le_of_le` gives

$$
\|x_k-c_kv_k-x^*\|-\|x_{k+1}-x^*\|\to 0.
$$

Adding the convergence of the shifted sequence yields

$$
\|x_k-c_kv_k-x^*\|\to L.
$$

This is the convergence `hExactDist`.

5. The field `A.sigma_bound` supplies a number $\bar\sigma$ with

$$
0<\bar\sigma<1
$$

and, for every $k$, the inequality $\sigma_k\le \bar\sigma$. The proof defines

$$
q=1-\bar\sigma^2.
$$

Since $0<\bar\sigma<1$, we have $q>0$.

6. The lemma `hpe_descent` has the following content: for every $k$,

$$
\|x^*-x_k\|^2-\|x^*-(x_k-c_kv_k)\|^2
\ge (1-\sigma_k^2)\|y_k-x_k\|^2-\delta_k.
$$

Because $\sigma_k^2\le \bar\sigma^2$, we have

$$
q=1-\bar\sigma^2\le 1-\sigma_k^2.
$$

Multiplying by the nonnegative quantity $\|y_k-x_k\|^2$ and combining with the descent inequality gives

$$
q\|y_k-x_k\|^2
\le
\|x^*-x_k\|^2-\|x^*-(x_k-c_kv_k)\|^2+\delta_k.
$$

The proof packages this as `hdispSqLe`; the arithmetic is handled by `nlinarith`.

7. The right-hand side of that inequality tends to $0$. Indeed, `hDist` and `hExactDist` show that

$$
\|x^*-x_k\|^2\to L^2,\qquad
\|x^*-(x_k-c_kv_k)\|^2\to L^2.
$$

Their difference therefore tends to $0$, and adding $\delta_k\to 0$ gives

$$
\|x^*-x_k\|^2-\|x^*-(x_k-c_kv_k)\|^2+\delta_k\to 0.
$$

This is `hright0`.

8. To deduce $\|y_k-x_k\|\to 0$, the proof applies `hpe_tendsto_norm_of_sq_le`. That lemma says: if $u_k\ge 0$, $b_k\to 0$, and $u_k^2\le b_k$, then $u_k\to 0$. Here the proof takes

$$
u_k=\|y_k-x_k\|,
\qquad
b_k=\frac{\|x^*-x_k\|^2-\|x^*-(x_k-c_kv_k)\|^2+\delta_k}{q}.
$$

Since $q>0$, $b_k\to 0$. The inequality from `hdispSqLe` is $q u_k^2\le \text{right-hand side}$, which is equivalent to $u_k^2\le b_k$. Hence $u_k\to 0$, i.e.

$$
\|y_k-x_k\|\to 0.
$$

This is `hdisp`.

9. Next the proof shows

$$
\sigma_k^2\|y_k-x_k\|^2\to 0.
$$

Since $\|y_k-x_k\|\to 0$, its square tends to $0$. Also $0\le \sigma_k^2\le \bar\sigma^2$, so

$$
0\le \sigma_k^2\|y_k-x_k\|^2\le \bar\sigma^2\|y_k-x_k\|^2.
$$

The upper bound tends to $0$, so the squeeze theorem gives the desired convergence. Consequently,

$$
b_k:=\delta_k+\sigma_k^2\|y_k-x_k\|^2\to 0.
$$

This is `hb0`.

10. The proof defines the residual

$$
R_k=c_k v_k+y_k-x_k.
$$

Equivalently, $R_k=y_k-(x_k-c_kv_k)$, the difference between $y_k$ and the extragradient step. The HPE field `A.residual_bound k` is used in the form

$$
\|R_k\|^2+2c_k\varepsilon_k
\le
\delta_k+\sigma_k^2\|y_k-x_k\|^2.
$$

Since $c_k\varepsilon_k\ge 0$, this implies

$$
\|R_k\|^2\le \delta_k+\sigma_k^2\|y_k-x_k\|^2=b_k.
$$

Applying `hpe_tendsto_norm_of_sq_le` with $u_k=\|R_k\|$ and the same $b_k\to 0$ gives

$$
\|R_k\|\to 0.
$$

This is `hR0`.

11. To prove $\varepsilon_k\to 0$, the proof uses `A.c_lower_bound`, which supplies $\bar c>0$ such that

$$
\bar c\le c_k
$$

for every $k$. From the residual bound, dropping the nonnegative term $\|R_k\|^2$, we get

$$
2c_k\varepsilon_k\le b_k.
$$

Since $\bar c\le c_k$ and $\varepsilon_k\ge 0$, it follows that

$$
2\bar c\,\varepsilon_k\le 2c_k\varepsilon_k\le b_k.
$$

The lemma `hpe_tendsto_of_le_div_const` says: if $c>0$, $u_k\ge 0$, $b_k\to 0$, and $c u_k\le b_k$, then $u_k\to 0$. Applying it with $c=2\bar c$, $u_k=\varepsilon_k$, and $b_k\to 0$ gives

$$
\varepsilon_k\to 0.
$$

This is `hε0`.

12. To prove $\|c_kv_k\|\to 0$, the proof rearranges

$$
R_k=c_kv_k+y_k-x_k
$$

as

$$
c_kv_k=R_k-(y_k-x_k).
$$

The triangle inequality gives

$$
\|c_kv_k\|\le \|R_k\|+\|y_k-x_k\|.
$$

Both terms on the right tend to $0$, so their sum tends to $0$. Since $\|c_kv_k\|\ge 0$, the squeeze theorem gives

$$
\|c_kv_k\|\to 0.
$$

This is `hcv0`.

13. Finally, to prove $\|v_k\|\to 0$, the proof again applies `hpe_tendsto_of_le_div_const`, now with $c=\bar c$, $u_k=\|v_k\|$, and $b_k=\|c_kv_k\|$. Since $c_k>0$,

$$
\|c_kv_k\|=|c_k|\,\|v_k\|=c_k\|v_k\|.
$$

Because $\bar c\le c_k$ and $\|v_k\|\ge 0$,

$$
\bar c\|v_k\|\le c_k\|v_k\|=\|c_kv_k\|.
$$

Since $\|c_kv_k\|\to 0$, the lemma gives

$$
\|v_k\|\to 0.
$$

This is `hv0`.

14. The final `exact ⟨hxBounded, hdisp, hε0, hv0, hcv0⟩` assembles the five previously proved facts into the conjunction required by the theorem: boundedness of the $x$-range, convergence of $\|y_k-x_k\|$, convergence of $\varepsilon_k$, convergence of $\|v_k\|$, and convergence of $\|c_kv_k\|$.

