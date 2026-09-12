## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/thm_4.lean`

## Lean statement
```lean
theorem inertial_proximal_method_converges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → EReal}
    (u : ℕ → H) (eps lam alpha : ℕ → ℝ)
    (hProper : ERealFunction.IsProper f)
    (hClosed : IsClosed (ERealFunction.epigraph f))
    (hConvex : Convex ℝ (ERealFunction.epigraph f))
    (hBoundedBelow : ∃ m : ℝ, ∀ x : H, (m : EReal) ≤ f x)
    (hEps : ∀ k, 0 ≤ eps k) (hAlpha : ∀ k, 0 ≤ alpha k ∧ alpha k ≤ 1)
    (hLamLower : ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ lam k)
    (hRatioAntitone : Antitone (fun k => alpha k / lam k))
    (hErrors : Summable (fun k => lam k * eps k))
    (hUpdate : ∀ k : ℕ, 0 < k → 0 ∈ (fun p =>
      (lam k)⁻¹ • (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)) + p) ''
      epsilonSubdifferential f (eps k) (u (k + 1))) :
    Tendsto (fun k => (lam k)⁻¹ •
      (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) atTop (nhds 0) ∧
    Tendsto (fun k => Metric.infDist 0
      (epsilonSubdifferential f (eps k) (u (k + 1)))) atTop (nhds 0) ∧
    ((argmin f (by
      rcases hBoundedBelow with ⟨m, hm⟩
      exact ⟨(m : EReal), fun _ ⟨x, hxy⟩ => by simpa [hxy] using hm x⟩)).Nonempty →
      (∃ alphaBar : ℝ, 0 < alphaBar ∧ alphaBar < 1 ∧ ∀ k, alpha k ≤ alphaBar) →
      ((∃ k, 0 < alpha k) → ∃ c : ℝ, ∀ k, lam k ≤ c) →
      ∃ uhat ∈ argmin f (by
        rcases hBoundedBelow with ⟨m, hm⟩
        exact ⟨(m : EReal), fun _ ⟨x, hxy⟩ => by simpa [hxy] using hm x⟩),
        Tendsto (fun k => toWeakSpace ℝ H (u k)) atTop (nhds (toWeakSpace ℝ H uhat)))
```

## Statement explanation
The theorem `inertial_proximal_method_converges` is a convergence result for an inertial proximal algorithm in a real Hilbert space $H$. The data are an extended-real-valued function $f:H\to \overline{\mathbb R}$, called `EReal` in Lean, and three real sequences:

$$
u:\mathbb N\to H,\qquad \varepsilon:\mathbb N\to\mathbb R,\qquad \lambda:\mathbb N\to\mathbb R,\qquad \alpha:\mathbb N\to\mathbb R .
$$

The sequence $u_k$ is the iterated sequence produced by the method, $\lambda_k$ is the proximal step size, $\alpha_k$ is the inertial parameter, and $\varepsilon_k$ is the allowed error in the proximal subproblem at step $k$. The theorem assumes:

- $f$ is proper: it is never $-\infty$, and it is finite somewhere. In the proof, `hProper.1` rules out $f(x)=-\infty$, while `hProper.2` supplies a point where $f$ is not $+\infty$.
- The epigraph $\mathrm{epi} f=\{(x,r): f(x)\le r\}$ is closed.
- The epigraph of $f$ is convex, so $f$ is a convex extended-real function.
- $f$ is bounded below by a finite real number: there exists $m\in\mathbb R$ such that $(m:\overline{\mathbb R})\le f(x)$ for every $x$.
- The errors are nonnegative: $\varepsilon_k\ge 0$ for all $k$.
- The inertial parameters lie in $[0,1]$: $0\le \alpha_k\le 1$ for all $k$.
- The step sizes are bounded below by a positive constant: there is $c>0$ with $c\le \lambda_k$ for all $k$.
- The ratio $\alpha_k/\lambda_k$ is nonincreasing in $k$.
- The sequence $\lambda_k\varepsilon_k$ is summable.
- The proximal/update condition holds: for every $k>0$,

$$
0\in (\lambda_k)^{-1}\bigl(u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}\bigr)
+\partial_{\varepsilon_k} f(u_{k+1}).
$$

Equivalently, there exists $p\in\partial_{\varepsilon_k} f(u_{k+1})$ such that

$$
p=-(\lambda_k)^{-1}\bigl(u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}\bigr).
$$

Here $\partial_{\varepsilon} f(x)$ is the $\varepsilon$-subdifferential:

$$
p\in\partial_{\varepsilon} f(x)
\quad\Longleftrightarrow\quad
\forall y,\quad f(y)\ge f(x)+\langle p,y-x\rangle-\varepsilon.
$$

The set $\mathrm{argmin} f$ is $\{x: f(x)=\inf f\}$, with the infimum taken in $\overline{\mathbb R}$.

The conclusion is a conjunction of three statements. First, the residual sequence tends strongly to zero:

$$
(\lambda_k)^{-1}\bigl(u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}\bigr)\to 0.
$$

Second, the distance from $0$ to the $\varepsilon_k$-subdifferential at $u_{k+1}$ tends to zero:

$$
\mathrm{dist}\bigl(0,\partial_{\varepsilon_k} f(u_{k+1})\bigr)\to 0.
$$

Third, under additional conditions, the iterates converge weakly to a minimizer of $f$. The additional conditions are: the set of minimizers is nonempty; the inertial parameters are bounded above by some $\mathrm{alphaBar}<1$ with $\mathrm{alphaBar}>0$; and if some $\alpha_k$ is positive, then the step sizes $\lambda_k$ are bounded above. Under these hypotheses, there exists

$$
\hat u\in\mathrm{argmin} f
$$

such that

$$
u_k\rightharpoonup \hat u
$$

in the weak topology of $H$. In Lean, this is written using `toWeakSpace ℝ H`.

## Lean proof
```lean
by
  rcases hBoundedBelow with ⟨m, hm⟩
  have hBddBelow : BddBelow (Set.range f) :=
    ⟨(m : EReal), fun _ ⟨x, hxy⟩ => by simpa [hxy] using hm x⟩
  rcases hLamLower with ⟨c, hcPos, hcLower⟩
  have hLamPos (k : ℕ) : 0 < lam k := by
    linarith [hcLower k]
  have hLamNe (k : ℕ) : lam k ≠ 0 := ne_of_gt (hLamPos k)
  have hAlphaNonneg (k : ℕ) : 0 ≤ alpha k := (hAlpha k).1
  have hAlphaLeOne (k : ℕ) : alpha k ≤ 1 := (hAlpha k).2
  have hEpsNonneg (k : ℕ) : 0 ≤ eps k := hEps k
  have hEpsSummable : Summable eps := by
    apply Summable.of_nonneg_of_le (fun k => hEpsNonneg k)
    · intro k
      have hmul : c * eps k ≤ lam k * eps k :=
        mul_le_mul_of_nonneg_right (hcLower k) (hEpsNonneg k)
      calc
        eps k = c⁻¹ * (c * eps k) := by field_simp [ne_of_gt hcPos]
        _ ≤ c⁻¹ * (lam k * eps k) :=
          mul_le_mul_of_nonneg_left hmul (le_of_lt (inv_pos.mpr hcPos))
    · simpa [mul_assoc] using (hErrors.mul_left c⁻¹)
  have hUpdateWitness (k : ℕ) (hk : 0 < k) :
      ∃ p ∈ epsilonSubdifferential f (eps k) (u (k + 1)),
        p = -((lam k)⁻¹ •
          (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) := by
    rcases hUpdate k hk with ⟨p, hp, hpzero⟩
    refine ⟨p, hp, ?_⟩
    exact eq_neg_of_add_eq_zero_right hpzero
  have hIterateLtTop (k : ℕ) (hk : 0 < k) : f (u (k + 1)) < ⊤ := by
    rcases hUpdateWitness k hk with ⟨p, hp, hpEq⟩
    change ∀ y : H, f y ≥ f (u (k + 1)) + (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
    rcases hProper.2 with ⟨y, hy⟩
    by_contra hnot
    have htop : f (u (k + 1)) = ⊤ := top_unique (not_lt.mp hnot)
    have hbound := hp y
    rw [htop] at hbound
    have hyTop : f y = ⊤ := top_unique (by simpa using hbound)
    exact hy.ne hyTop
  have hDescent (k : ℕ) (hk : 1 < k) :
      (f (u (k + 1))).toReal - (f (u k)).toReal ≤
        -(lam k)⁻¹ * ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - u k⟫_ℝ + eps k := by
    rcases hUpdateWitness k (by omega) with ⟨p, hp, hpEq⟩
    change ∀ y : H, f y ≥ f (u (k + 1)) + (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
    have hstep : f (u k) ≥ f (u (k + 1)) +
        (⟪p, u k - u (k + 1)⟫_ℝ : EReal) - eps k := hp (u k)
    have hnextTop := hIterateLtTop k (by omega)
    have hcurrTop : f (u k) < ⊤ := by
      have hprev := hIterateLtTop (k - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hprev
      exact hprev
    have hnextBot : f (u (k + 1)) ≠ ⊥ := hProper.1 _
    have hcurrBot : f (u k) ≠ ⊥ := hProper.1 _
    have hnext : f (u (k + 1)) = ((f (u (k + 1))).toReal : EReal) :=
      (EReal.coe_toReal hnextTop.ne hnextBot).symm
    have hcurr : f (u k) = ((f (u k)).toReal : EReal) :=
      (EReal.coe_toReal hcurrTop.ne hcurrBot).symm
    rw [hnext, hcurr, hpEq] at hstep
    norm_cast at hstep
    have hdiff : u k - u (k + 1) = -(u (k + 1) - u k) := by abel
    rw [hdiff, inner_neg_right, inner_neg_left, inner_smul_left] at hstep
    simp only [starRingEnd_apply, star_trivial, neg_neg] at hstep
    linarith
  have hEnergyStep := alvarez_energy_step u f eps lam alpha hAlpha hLamPos
    hRatioAntitone hDescent
  let E : ℕ → ℝ := fun n =>
    alpha (n + 1) / (2 * lam (n + 1)) * ‖u (n + 2) - u (n + 1)‖ ^ 2 +
      (f (u (n + 2))).toReal
  let W : ℕ → ℝ := fun n =>
    alpha (n + 2) / (2 * lam (n + 2)) *
        ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 +
      (1 - alpha (n + 2)) / lam (n + 2) * ‖u (n + 3) - u (n + 2)‖ ^ 2
  let R : ℕ → ℝ := fun n => eps (n + 2)
  have hWnonneg (n : ℕ) : 0 ≤ W n := by
    dsimp [W]
    have hfirst : 0 ≤ alpha (n + 2) / (2 * lam (n + 2)) := by
      apply div_nonneg (hAlphaNonneg _)
      exact le_of_lt (mul_pos (by norm_num) (hLamPos _))
    have hsecond : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) := by
      exact div_nonneg (sub_nonneg.mpr (hAlphaLeOne _)) (le_of_lt (hLamPos _))
    positivity
  have hElower (n : ℕ) : m ≤ E n := by
    dsimp [E]
    have htop := hIterateLtTop (n + 1) (by omega)
    have hbot : f (u (n + 2)) ≠ ⊥ := hProper.1 _
    have hval : f (u (n + 2)) = ((f (u (n + 2))).toReal : EReal) :=
      (EReal.coe_toReal htop.ne hbot).symm
    have hm' := hm (u (n + 2))
    rw [hval] at hm'
    norm_cast at hm'
    have hkin : 0 ≤ alpha (n + 1) / (2 * lam (n + 1)) *
        ‖u (n + 2) - u (n + 1)‖ ^ 2 := by
      have hcoeff : 0 ≤ alpha (n + 1) / (2 * lam (n + 1)) := by
        apply div_nonneg (hAlphaNonneg _)
        exact le_of_lt (mul_pos (by norm_num) (hLamPos _))
      positivity
    linarith
  have hRnonneg (n : ℕ) : 0 ≤ R n := hEpsNonneg _
  have hRsum : Summable R := by
    simpa [R, Nat.add_comm] using (summable_nat_add_iff 2).mpr hEpsSummable
  have hEstep (n : ℕ) : E (n + 1) + W n ≤ E n + R n := by
    have hs : E (n + 1) ≤ E n - W n + R n := by
      dsimp [E, W, R]
      convert hEnergyStep (n + 2) (by omega) using 1 <;> omega
    linarith
  have hWsum : Summable W :=
    alvarez_telescope_summable E W R m hElower hWnonneg hRnonneg hRsum hEstep
  -- Keep the two dissipations separate.  Besides being the form used in the
  -- paper, these facts are the useful input for both the residual estimate and
  -- the inertial-distance recurrence below.
  let A : ℕ → ℝ := fun n =>
    alpha (n + 2) / (2 * lam (n + 2)) *
      ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2
  let B : ℕ → ℝ := fun n =>
    (1 - alpha (n + 2)) / lam (n + 2) * ‖u (n + 3) - u (n + 2)‖ ^ 2
  have hAnonneg (n : ℕ) : 0 ≤ A n := by
    dsimp [A]
    have hcoeff : 0 ≤ alpha (n + 2) / (2 * lam (n + 2)) := by
      apply div_nonneg (hAlphaNonneg _)
      exact le_of_lt (mul_pos (by norm_num) (hLamPos _))
    positivity
  have hBnonneg (n : ℕ) : 0 ≤ B n := by
    dsimp [B]
    have hcoeff : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) := by
      exact div_nonneg (sub_nonneg.mpr (hAlphaLeOne _)) (le_of_lt (hLamPos _))
    positivity
  have hA_le (n : ℕ) : A n ≤ W n := by
    dsimp [A, B, W]
    have hsecond : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) *
        ‖u (n + 3) - u (n + 2)‖ ^ 2 := by
      exact hBnonneg n
    linarith
  have hB_le (n : ℕ) : B n ≤ W n := by
    dsimp [A, B, W]
    have hfirst : 0 ≤ alpha (n + 2) / (2 * lam (n + 2)) *
        ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 := by
      exact hAnonneg n
    linarith
  have hAsum : Summable A :=
    Summable.of_nonneg_of_le hAnonneg hA_le hWsum
  have hBsum : Summable B :=
    Summable.of_nonneg_of_le hBnonneg hB_le hWsum
  have hA0 : Tendsto A atTop (nhds 0) := hAsum.tendsto_atTop_zero
  have hB0 : Tendsto B atTop (nhds 0) := hBsum.tendsto_atTop_zero
  have hSecondDiffShift : Tendsto (fun n =>
      (alpha (n + 2) / lam (n + 2)) •
        (u (n + 3) - 2 • u (n + 2) + u (n + 1))) atTop (nhds 0) := by
    apply alvarez_tendsto_zero_of_sq_le _ A (2 / c) (by positivity) hA0
    intro n
    have hratio0 : 0 ≤ alpha (n + 2) / lam (n + 2) :=
      div_nonneg (hAlphaNonneg _) (le_of_lt (hLamPos _))
    have hratio : alpha (n + 2) / lam (n + 2) ≤ 1 / c := by
      apply (div_le_div_iff₀ (hLamPos _) hcPos).mpr
      have : alpha (n + 2) * c ≤ c := by
        rw [mul_comm]
        exact mul_le_of_le_one_right hcPos.le (hAlphaLeOne _)
      linarith [hcLower (n + 2)]
    have hcoeff : (alpha (n + 2) / lam (n + 2)) ^ 2 ≤
        2 / c * (alpha (n + 2) / (2 * lam (n + 2))) := by
      calc
        (alpha (n + 2) / lam (n + 2)) ^ 2 =
            (alpha (n + 2) / lam (n + 2)) * (alpha (n + 2) / lam (n + 2)) := by ring
        _ ≤ (alpha (n + 2) / lam (n + 2)) * (1 / c) :=
          mul_le_mul_of_nonneg_left hratio hratio0
        _ = 2 / c * (alpha (n + 2) / (2 * lam (n + 2))) := by
          field_simp [hLamNe _, ne_of_gt hcPos]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio0]
    calc
      (alpha (n + 2) / lam (n + 2) *
          ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖) ^ 2 =
          (alpha (n + 2) / lam (n + 2)) ^ 2 *
            ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 := by ring
      _ ≤ (2 / c * (alpha (n + 2) / (2 * lam (n + 2)))) *
            ‖u (n + 3) - 2 • u (n + 2) + u (n + 1)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = (2 / c) * A n := by simp [A, mul_assoc]
  have hSecondDiff : Tendsto (fun k =>
      (alpha k / lam k) •
        (u (k + 1) - 2 • u k + u (k - 1))) atTop (nhds 0) := by
    have h := alvarez_tendsto_of_nat_add
      (fun k => (alpha k / lam k) •
        (u (k + 1) - 2 • u k + u (k - 1))) 2 0 hSecondDiffShift
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hFirstDiffShift : Tendsto (fun n =>
      ((1 - alpha (n + 2)) / lam (n + 2)) •
        (u (n + 3) - u (n + 2))) atTop (nhds 0) := by
    apply alvarez_tendsto_zero_of_sq_le _ B (1 / c) (by positivity) hB0
    intro n
    have hratio0 : 0 ≤ (1 - alpha (n + 2)) / lam (n + 2) :=
      div_nonneg (sub_nonneg.mpr (hAlphaLeOne _)) (le_of_lt (hLamPos _))
    have hratio : (1 - alpha (n + 2)) / lam (n + 2) ≤ 1 / c := by
      apply (div_le_div_iff₀ (hLamPos _) hcPos).mpr
      nlinarith [hcLower (n + 2), hAlphaNonneg (n + 2)]
    have hcoeff : ((1 - alpha (n + 2)) / lam (n + 2)) ^ 2 ≤
        (1 / c) * ((1 - alpha (n + 2)) / lam (n + 2)) := by
      rw [pow_two]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hratio hratio0
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio0]
    calc
      (((1 - alpha (n + 2)) / lam (n + 2)) *
          ‖u (n + 3) - u (n + 2)‖) ^ 2 =
          ((1 - alpha (n + 2)) / lam (n + 2)) ^ 2 *
            ‖u (n + 3) - u (n + 2)‖ ^ 2 := by ring
      _ ≤ ((1 / c) * ((1 - alpha (n + 2)) / lam (n + 2))) *
            ‖u (n + 3) - u (n + 2)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
      _ = (1 / c) * B n := by simp [B, mul_assoc]
  have hFirstDiff : Tendsto (fun k =>
      ((1 - alpha k) / lam k) • (u (k + 1) - u k)) atTop (nhds 0) := by
    have h := alvarez_tendsto_of_nat_add
      (fun k => ((1 - alpha k) / lam k) • (u (k + 1) - u k)) 2 0 hFirstDiffShift
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hResidual : Tendsto (fun k => (lam k)⁻¹ •
      (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) atTop (nhds 0) := by
    have h := hSecondDiff.add hFirstDiff
    have h' : Tendsto (fun k =>
        (alpha k / lam k) • (u (k + 1) - 2 • u k + u (k - 1)) +
          ((1 - alpha k) / lam k) • (u (k + 1) - u k)) atTop (nhds 0) := by
      simpa using h
    convert h' using 1
    ext k
    rw [alvarez_residual_decomposition]
    simp only [Pi.add_apply, smul_add, smul_smul, div_eq_mul_inv]
    module
  have hResidualNormShift : Tendsto (fun n => ‖(lam (n + 1))⁻¹ •
      (u (n + 2) - (1 + alpha (n + 1)) • u (n + 1) +
        alpha (n + 1) • u n)‖) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
    simpa [Nat.add_sub_cancel] using hResidual.norm.comp hshift
  have hInfDistShift : Tendsto (fun n => Metric.infDist 0
      (epsilonSubdifferential f (eps (n + 1)) (u (n + 2)))) atTop (nhds 0) := by
    apply squeeze_zero (fun n => Metric.infDist_nonneg)
    · intro n
      rcases hUpdateWitness (n + 1) (by omega) with ⟨p, hp, hpEq⟩
      calc
        Metric.infDist 0 (epsilonSubdifferential f (eps (n + 1)) (u (n + 2))) ≤
            dist 0 p := Metric.infDist_le_dist_of_mem hp
        _ = ‖p‖ := by simp
        _ = ‖(lam (n + 1))⁻¹ •
            (u (n + 2) - (1 + alpha (n + 1)) • u (n + 1) +
              alpha (n + 1) • u n)‖ := by
              rw [hpEq, norm_neg]
              simp [Nat.add_sub_cancel]
    · exact hResidualNormShift
  have hInfDist : Tendsto (fun k => Metric.infDist 0
      (epsilonSubdifferential f (eps k) (u (k + 1)))) atTop (nhds 0) := by
    have h := alvarez_tendsto_of_nat_add
      (fun k => Metric.infDist 0 (epsilonSubdifferential f (eps k) (u (k + 1)))) 1 0
      hInfDistShift
    simpa [Nat.add_assoc] using h
  refine ⟨hResidual, hInfDist, ?_⟩
  intro hArgmin hAlphaBar hLamUpper
  rcases hAlphaBar with ⟨alphaBar, hAlphaBarPos, hAlphaBarLt, hAlphaBar⟩
  have hLower : LowerSemicontinuous f :=
    (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph f).2 hClosed
  have hLevelClosed (r : ℝ) : IsClosed (ERealFunction.lowerLevelSet f r) :=
    (ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hLower r
  have hLevelConv (r : ℝ) : Convex ℝ (ERealFunction.lowerLevelSet f r) :=
    alvarez_lower_level_convex hConvex r
  have hinner (z : H) (hz : z ∈ argmin f hBddBelow) (k : ℕ) (hk : 1 ≤ k) :
      ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
        u (k + 1) - z⟫_ℝ ≤ lam k * eps k := by
    rcases hUpdateWitness k (by omega) with ⟨p, hp, hpEq⟩
    change ∀ y : H, f y ≥ f (u (k + 1)) +
      (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
    have hmin : f z ≤ f (u (k + 1)) := by
      have hz_eq : f z = sInf (Set.range f) := hz
      rw [hz_eq]
      exact csInf_le hBddBelow ⟨u (k + 1), rfl⟩
    have hnextTop := hIterateLtTop k (by omega)
    have hnextBot : f (u (k + 1)) ≠ ⊥ := hProper.1 _
    have hzTop : f z < ⊤ := lt_of_le_of_lt hmin hnextTop
    have hzBot : f z ≠ ⊥ := hProper.1 _
    have hnext : f (u (k + 1)) = ((f (u (k + 1))).toReal : EReal) :=
      (EReal.coe_toReal hnextTop.ne hnextBot).symm
    have hzReal : f z = ((f z).toReal : EReal) :=
      (EReal.coe_toReal hzTop.ne hzBot).symm
    have hstep := hp z
    rw [hzReal, hnext] at hstep hmin
    rw [hpEq] at hstep
    norm_cast at hstep hmin
    have hdiff : z - u (k + 1) = -(u (k + 1) - z) := by abel
    rw [hdiff, inner_neg_right, inner_neg_left, inner_smul_left] at hstep
    simp only [starRingEnd_apply, star_trivial, neg_neg] at hstep
    have hresidual : (lam k)⁻¹ *
        ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - z⟫_ℝ ≤ eps k := by
      linarith [hstep, hmin]
    have hlam_nonneg : (0 : ℝ) ≤ lam k := (hLamPos k).le
    have hscaled : lam k *
        ((lam k)⁻¹ *
          ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
            u (k + 1) - z⟫_ℝ) ≤ lam k * eps k :=
      mul_le_mul_of_nonneg_left hresidual hlam_nonneg
    calc
      ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
          u (k + 1) - z⟫_ℝ = lam k * ((lam k)⁻¹ *
          ⟪u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1),
            u (k + 1) - z⟫_ℝ) := by field_simp [hLamNe k]
      _ ≤ lam k * eps k := hscaled
  let delta : ℕ → ℝ := fun k =>
    alpha k * ‖u k - u (k - 1)‖ ^ 2 +
      (alpha k / 2) * ‖u (k + 1) - u k‖ ^ 2 + lam k * eps k
  have hdeltaNonneg (k : ℕ) : 0 ≤ delta k := by
    dsimp [delta]
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (hAlphaNonneg k) (sq_nonneg _)
      · exact mul_nonneg (div_nonneg (hAlphaNonneg k) (by norm_num)) (sq_nonneg _)
    · exact mul_nonneg (le_of_lt (hLamPos k)) (hEpsNonneg k)
  have hrec (z : H) (hz : z ∈ argmin f hBddBelow) (k : ℕ) (hk : 1 ≤ k) :
      (1 / 2 : ℝ) * ‖u (k + 1) - z‖ ^ 2 -
          (1 + alpha k) * ((1 / 2 : ℝ) * ‖u k - z‖ ^ 2) +
          alpha k * ((1 / 2 : ℝ) * ‖u (k - 1) - z‖ ^ 2) ≤ delta k := by
    simpa [delta] using
      alvarez_phi_recurrence_of_inner u alpha lam eps z hAlphaNonneg (hinner z hz) k hk
  set_option maxHeartbeats 800000 in
  have hdeltaSum : Summable delta := by
    by_cases hSomeAlpha : ∃ k, 0 < alpha k
    · rcases hLamUpper hSomeAlpha with ⟨L₀, hL₀⟩
      let L : ℝ := max L₀ 1
      have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
      have hL : ∀ k, lam k ≤ L := fun k => le_trans (hL₀ k) (le_max_left _ _)
      let q : ℝ := (1 - alphaBar) / L
      have hq : 0 < q := div_pos (by linarith) hLpos
      have hqle (k : ℕ) : q ≤ (1 - alpha k) / lam k := by
        dsimp [q]
        apply (div_le_div_iff₀ hLpos (hLamPos k)).mpr
        have h₁ : 0 ≤ 1 - alphaBar := by linarith
        have h₂ : 1 - alphaBar ≤ 1 - alpha k := by linarith [hAlphaBar k]
        calc
          (1 - alphaBar) * lam k ≤ (1 - alphaBar) * L :=
            mul_le_mul_of_nonneg_left (hL k) h₁
          _ ≤ (1 - alpha k) * L :=
            mul_le_mul_of_nonneg_right h₂ (le_of_lt hLpos)
      have hIncShift : Summable (fun n => ‖u (n + 3) - u (n + 2)‖ ^ 2) := by
        apply Summable.of_nonneg_of_le (fun n => sq_nonneg _)
        · intro n
          have hqD := mul_le_mul_of_nonneg_right (hqle (n + 2)) (sq_nonneg (‖u (n + 3) - u (n + 2)‖))
          calc
            ‖u (n + 3) - u (n + 2)‖ ^ 2 =
                q⁻¹ * (q * ‖u (n + 3) - u (n + 2)‖ ^ 2) := by
                  field_simp [ne_of_gt hq]
            _ ≤ q⁻¹ * ((1 - alpha (n + 2)) / lam (n + 2) *
                ‖u (n + 3) - u (n + 2)‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hqD (le_of_lt (inv_pos.mpr hq))
            _ = q⁻¹ * B n := by simp [B, mul_assoc]
        · exact hBsum.mul_left q⁻¹
      have hIncSum : Summable (fun k => ‖u (k + 1) - u k‖ ^ 2) := by
        have h := (summable_nat_add_iff (f := fun k : ℕ => ‖u (k + 1) - u k‖ ^ 2) 2).mp hIncShift
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hPrev : Summable (fun k => alpha k * ‖u k - u (k - 1)‖ ^ 2) := by
        apply Summable.of_nonneg_of_le (fun k => mul_nonneg (hAlphaNonneg k) (sq_nonneg _))
        · intro k
          exact mul_le_of_le_one_left (sq_nonneg _) (hAlphaLeOne k)
        · have hprevBase : Summable (fun k : ℕ => ‖u k - u (k - 1)‖ ^ 2) := by
            apply (summable_nat_add_iff (f := fun k : ℕ => ‖u k - u (k - 1)‖ ^ 2) 1).mp
            simpa [Nat.add_sub_cancel] using hIncSum
          exact hprevBase
      have hNext : Summable (fun k => (alpha k / 2) * ‖u (k + 1) - u k‖ ^ 2) := by
        apply Summable.of_nonneg_of_le (fun k =>
          mul_nonneg (div_nonneg (hAlphaNonneg k) (by norm_num)) (sq_nonneg _))
        · intro k
          have halpha : alpha k / 2 ≤ (1 : ℝ) / 2 := by
            nlinarith [hAlphaLeOne k]
          exact mul_le_mul_of_nonneg_right halpha (sq_nonneg _)
        · exact hIncSum.mul_left (1 / 2 : ℝ)
      exact (hPrev.add hNext).add hErrors
    · have hAlphaZero : ∀ k, alpha k = 0 := by
        intro k
        apply le_antisymm
        · by_contra hnot
          exact hSomeAlpha ⟨k, lt_of_not_ge hnot⟩
        · exact hAlphaNonneg k
      convert hErrors using 1
      funext k
      dsimp [delta]
      rw [hAlphaZero k]
      ring
  have hdist (z : H) (hz : z ∈ argmin f hBddBelow) :
      ∃ l : ℝ, Tendsto (fun k => ‖u k - z‖) atTop (nhds l) :=
    alvarez_norm_converges_of_recurrence u z alpha delta alphaBar hAlphaNonneg hAlphaBar
      hAlphaBarLt hdeltaNonneg hdeltaSum (hrec z hz)
  have hcluster (z : H) :
      IsSequentialClusterPt (fun k => toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H z) →
        z ∈ argmin f hBddBelow := by
    intro hz
    rcases hz.exists_subseq_tendsto with ⟨phi, hphiStrict, hphiWeak⟩
    have hphiTop : Tendsto phi atTop atTop := hphiStrict.tendsto_atTop
    have hSubseqWeak : Tendsto (fun n => toWeakSpace ℝ H (u (phi n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      simpa [Function.comp_def] using hphiWeak
    rcases hArgmin with ⟨z0, hz0⟩
    have hz0_eq : f z0 = sInf (Set.range f) := hz0
    have hdist0 := hdist z0 hz0
    rcases hdist0 with ⟨l0, hdist0⟩
    have huBound : Bornology.IsBounded (Set.range u) :=
      bounded_range_of_convergent_distance_to_point ⟨l0, hdist0⟩
    have hresBound : Tendsto (fun k => (lam k)⁻¹ •
        (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1))) atTop (nhds 0) :=
      hResidual
    have hinnerZero : Tendsto (fun k => ⟪(lam k)⁻¹ •
        (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
        u k - z0⟫_ℝ) atTop (nhds 0) := by
      apply alvarez_inner_tendsto_zero_of_bounded _ _ hresBound
      have huBound' := huBound
      rw [isBounded_iff_forall_norm_le] at huBound' ⊢
      rcases huBound' with ⟨C, hC⟩
      refine ⟨C + ‖z0‖, ?_⟩
      rintro y ⟨k, rfl⟩
      calc
        ‖u k - z0‖ ≤ ‖u k‖ + ‖z0‖ := norm_sub_le _ _
        _ ≤ C + ‖z0‖ := by
          simpa [add_comm] using add_le_add_left (hC _ (Set.mem_range_self k)) ‖z0‖
    have hinnerNext : Tendsto (fun k => ⟪(lam k)⁻¹ •
        (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
        u (k + 1) - z0⟫_ℝ) atTop (nhds 0) := by
      apply alvarez_inner_tendsto_zero_of_bounded _ _ hresBound
      have huBound' := huBound
      rw [isBounded_iff_forall_norm_le] at huBound' ⊢
      rcases huBound' with ⟨C, hC⟩
      refine ⟨C + ‖z0‖, ?_⟩
      rintro y ⟨k, rfl⟩
      calc
        ‖u (k + 1) - z0‖ ≤ ‖u (k + 1)‖ + ‖z0‖ := norm_sub_le _ _
        _ ≤ C + ‖z0‖ := by
          simpa [add_comm] using add_le_add_left (hC _ (Set.mem_range_self (k + 1))) ‖z0‖
    have hEpsZero : Tendsto eps atTop (nhds 0) := hEpsSummable.tendsto_atTop_zero
    have hz0Top : f z0 < ⊤ := by
      have hmin : f z0 ≤ f (u 2) := by
        rw [hz0_eq]
        exact csInf_le hBddBelow ⟨u 2, rfl⟩
      exact lt_of_le_of_lt hmin (hIterateLtTop 1 (by omega))
    have hz0Bot : f z0 ≠ ⊥ := hProper.1 _
    have hz0Real : f z0 = ((f z0).toReal : EReal) :=
      (EReal.coe_toReal hz0Top.ne hz0Bot).symm
    have hgapLower (k : ℕ) (hk : 1 < k) :
        0 ≤ (f (u k)).toReal - (f z0).toReal := by
      have hmin : f z0 ≤ f (u k) := by
        rw [hz0_eq]
        exact csInf_le hBddBelow ⟨u k, rfl⟩
      have htop : f (u k) < ⊤ := by
        have heq : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
        rw [← heq]
        exact hIterateLtTop (k - 1) (by omega)
      have hbot : f (u k) ≠ ⊥ := hProper.1 _
      have hreal : f (u k) = ((f (u k)).toReal : EReal) :=
        (EReal.coe_toReal htop.ne hbot).symm
      rw [hz0Real, hreal] at hmin
      norm_cast at hmin
      linarith
    have hgapUpper (k : ℕ) (hk : 1 < k) :
        (f (u (k + 1))).toReal - (f z0).toReal ≤
          -⟪(lam k)⁻¹ •
            (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
            u (k + 1) - z0⟫_ℝ + eps k := by
      rcases hUpdateWitness k (by omega) with ⟨p, hp, hpEq⟩
      change ∀ y : H, f y ≥ f (u (k + 1)) +
        (⟪p, y - u (k + 1)⟫_ℝ : EReal) - eps k at hp
      have hstep := hp z0
      have hnextTop := hIterateLtTop k (by omega)
      have hnextBot : f (u (k + 1)) ≠ ⊥ := hProper.1 _
      have hnext : f (u (k + 1)) = ((f (u (k + 1))).toReal : EReal) :=
        (EReal.coe_toReal hnextTop.ne hnextBot).symm
      rw [hz0Real, hnext, hpEq] at hstep
      norm_cast at hstep
      have hdiff : z0 - u (k + 1) = -(u (k + 1) - z0) := by abel
      rw [hdiff, inner_neg_right, inner_neg_left, inner_smul_left] at hstep
      simp only [starRingEnd_apply, star_trivial, neg_neg] at hstep
      rw [real_inner_smul_left]
      linarith
    have hgap : Tendsto (fun k => (f (u k)).toReal - (f z0).toReal) atTop (nhds 0) := by
      have hupper : Tendsto (fun k => -⟪(lam k)⁻¹ •
          (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)),
          u (k + 1) - z0⟫_ℝ + eps k) atTop (nhds 0) := by
        simpa using hinnerNext.neg.add hEpsZero
      have hshift : Tendsto (fun k : ℕ => k + 2) atTop atTop :=
        tendsto_atTop_mono (fun k => by
          simpa only [id_eq] using Nat.le_add_right k 2) tendsto_id
      have hupperShift : Tendsto (fun k => -⟪(lam (k + 2))⁻¹ •
          (u (k + 3) - (1 + alpha (k + 2)) • u (k + 2) + alpha (k + 2) • u (k + 1)),
          u (k + 3) - z0⟫_ℝ + eps (k + 2)) atTop (nhds 0) := by
        simpa using hupper.comp hshift
      have hgapShift : Tendsto (fun k => (f (u (k + 3))).toReal - (f z0).toReal)
          atTop (nhds 0) := by
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupperShift
        · filter_upwards [Filter.eventually_atTop.2 ⟨2, by intro k hk; exact hgapLower (k + 3) (by omega)⟩]
          intro k hk
          exact hk
        · filter_upwards [] with k
          simpa using hgapUpper (k + 2) (by omega)
      have h := alvarez_tendsto_of_nat_add
        (fun k => (f (u k)).toReal - (f z0).toReal) 3 0 hgapShift
      simpa [Nat.add_assoc] using h
    have hgapPhi : Tendsto (fun n => (f (u (phi n))).toReal - (f z0).toReal)
        atTop (nhds 0) := hgap.comp hphiTop
    have hz_le_add (d : ℝ) (hd : 0 < d) :
        f z ≤ ((f z0).toReal + d : EReal) := by
      have hev : ∀ᶠ n in atTop,
          (f (u (phi n))).toReal - (f z0).toReal < d :=
        (tendsto_order.1 hgapPhi).2 d hd
      rcases Filter.eventually_atTop.1 hev with ⟨N, hN⟩
      let M : ℕ := max N 2
      have hshiftM : Tendsto (fun n : ℕ => n + M) atTop atTop :=
        tendsto_atTop_mono (fun n => by
          simpa only [id_eq] using Nat.le_add_right n M) tendsto_id
      have hgapPhiM : Tendsto (fun n =>
          (f (u (phi (n + M)))).toReal - (f z0).toReal) atTop (nhds 0) := by
        simpa [Function.comp_def] using hgapPhi.comp hshiftM
      have hSubseqWeakM : Tendsto (fun n =>
          toWeakSpace ℝ H (u (phi (n + M)))) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa [Function.comp_def] using hSubseqWeak.comp hshiftM
      have hphi2 : 2 ≤ phi 2 := by
        have h01 := hphiStrict (by omega : 0 < 1)
        have h12 := hphiStrict (by omega : 1 < 2)
        omega
      have hmem : ∀ n, u (phi (n + M)) ∈
          ERealFunction.lowerLevelSet f ((f z0).toReal + d) := by
        intro n
        have hn : (f (u (phi (n + M)))).toReal - (f z0).toReal < d := by
          apply hN
          dsimp [M]
          omega
        rw [ERealFunction.mem_lowerLevelSet_iff]
        have hphiM : 2 ≤ phi (n + M) := by
          apply le_trans hphi2
          exact hphiStrict.monotone (by dsimp [M]; omega)
        have htop : f (u (phi (n + M))) < ⊤ := by
          have heq : phi (n + M) - 1 + 1 = phi (n + M) :=
            Nat.sub_add_cancel (by omega)
          rw [← heq]
          exact hIterateLtTop (phi (n + M) - 1) (by omega)
        have hbot : f (u (phi (n + M))) ≠ ⊥ := hProper.1 _
        rw [(EReal.coe_toReal htop.ne hbot).symm]
        exact_mod_cast (le_of_lt (by linarith))
      have hzlevel := mem_of_tendsto_weakly_of_isClosed_convex
        (hLevelClosed ((f z0).toReal + d)) (hLevelConv ((f z0).toReal + d)) hmem hSubseqWeakM
      rw [ERealFunction.mem_lowerLevelSet_iff] at hzlevel
      exact hzlevel
    have hztop : f z < ⊤ := by
      apply lt_of_le_of_lt (hz_le_add 1 (by norm_num))
      rw [← EReal.coe_add]
      exact EReal.coe_lt_top _
    have hzbot : f z ≠ ⊥ := hProper.1 _
    have hzreal : f z = ((f z).toReal : EReal) :=
      (EReal.coe_toReal hztop.ne hzbot).symm
    have hzLe : f z ≤ f z0 := by
      rw [hzreal, hz0Real]
      apply (EReal.coe_le_coe_iff).mpr
      apply le_of_forall_pos_le_add
      intro d hd
      have h := hz_le_add d hd
      rw [hzreal, ← EReal.coe_add] at h
      exact EReal.coe_le_coe_iff.mp h
    rw [argmin]
    apply le_antisymm
    · simpa [hz0_eq] using hzLe
    · exact csInf_le hBddBelow ⟨z, rfl⟩
  exact opial_lemma hArgmin u hdist hcluster
```

## Proof explanation
The proof begins by extracting the finite lower bound $m$ from `hBoundedBelow`. This gives that the range of $f$ is bounded below in the extended-real sense, so the infimum used in `argmin f` is meaningful. From `hLamLower` the proof extracts $c>0$ and the inequalities $c\le \lambda_k$. The command `linarith` then immediately gives $\lambda_k>0$ for every $k$, hence $\lambda_k\ne0$. This positivity is used repeatedly to clear denominators and to divide by $\lambda_k$.

The proof records the pointwise consequences of the hypotheses: $\alpha_k\ge0$, $\alpha_k\le1$, and $\varepsilon_k\ge0$. It then proves that the error sequence itself is summable. Since $c\le\lambda_k$ and $\varepsilon_k\ge0$,

$$
c\varepsilon_k\le \lambda_k\varepsilon_k.
$$

Multiplying by $c^{-1}>0$ gives

$$
\varepsilon_k=c^{-1}(c\varepsilon_k)\le c^{-1}(\lambda_k\varepsilon_k).
$$

Because $\lambda_k\varepsilon_k$ is summable by `hErrors`, multiplying by the constant $c^{-1}$ preserves summability. The comparison test for nonnegative sequences, invoked through `Summable.of_nonneg_of_le`, gives $\sum \varepsilon_k<\infty$. This is later used to get $\varepsilon_k\to0$ and to handle the case where all $\alpha_k$ vanish.

Next, the update condition `hUpdate` is converted into a concrete witness. For $k>0$, the statement that $0$ lies in the translated $\varepsilon_k$-subdifferential means precisely that there exists

$$
p_k\in\partial_{\varepsilon_k} f(u_{k+1})
$$

such that

$$
(\lambda_k)^{-1}R_k+p_k=0,
$$

where

$$
R_k=u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}.
$$

The proof therefore obtains

$$
p_k=-(\lambda_k)^{-1}R_k.
$$

This is the central optimality relation of the proximal step.

The proof then shows that $f(u_{k+1})<+\infty$ whenever $k>0$. If $f(u_{k+1})=+\infty$, then evaluating the $\varepsilon_k$-subgradient inequality at a point $y$ where $f(y)\ne+\infty$, supplied by properness, would force $f(y)=+\infty$, a contradiction. This finiteness is used constantly to pass between the extended-real value $f(x)$ and its real part $(f(x))_{\mathbb R}$, via `EReal.coe_toReal`.

Using the witness $p_k$, the proof derives the descent inequality

$$
(f(u_{k+1}))_{\mathbb R}-(f(u_k))_{\mathbb R}
\le
-(\lambda_k)^{-1}\langle R_k,u_{k+1}-u_k\rangle+\varepsilon_k.
$$

Indeed, the $\varepsilon_k$-subgradient inequality at $y=u_k$ gives

$$
f(u_k)\ge f(u_{k+1})+\langle p_k,u_k-u_{k+1}\rangle-\varepsilon_k.
$$

Substituting $p_k=-(\lambda_k)^{-1}R_k$ and using $u_k-u_{k+1}=-(u_{k+1}-u_k)$ turns this into the displayed real inequality after converting the finite extended-real values to real numbers. The command `norm_cast` handles the coercion from $\mathbb R$ back to `EReal`, and `linarith` finishes the rearrangement.

With this descent inequality, the proof applies `alvarez_energy_step`. That lemma takes the hypotheses $0\le\alpha_k\le1$, $\lambda_k>0$, antitone $\alpha_k/\lambda_k$, and the above descent inequality. Its conclusion, specialized to the present variables, is the energy estimate

$$
\begin{aligned}
&\frac{\alpha_k}{2\lambda_k}\|u_{k+1}-u_k\|^2+(f(u_{k+1}))_{\mathbb R}\\
&\le
\frac{\alpha_{k-1}}{2\lambda_{k-1}}\|u_k-u_{k-1}\|^2+(f(u_k))_{\mathbb R}\\
&\quad-
\left(
\frac{\alpha_k}{2\lambda_k}\|u_{k+1}-2u_k+u_{k-1}\|^2
+\frac{1-\alpha_k}{\lambda_k}\|u_{k+1}-u_k\|^2
\right)
+\varepsilon_k.
\end{aligned}
$$

This is the discrete energy decrease inequality for the second-order dissipative inertial method.

The proof shifts indices to apply a telescoping summability lemma. It defines

$$
E_n=
\frac{\alpha_{n+1}}{2\lambda_{n+1}}\|u_{n+2}-u_{n+1}\|^2+(f(u_{n+2}))_{\mathbb R},
$$

$$
W_n=
\frac{\alpha_{n+2}}{2\lambda_{n+2}}\|u_{n+3}-2u_{n+2}+u_{n+1}\|^2
+\frac{1-\alpha_{n+2}}{\lambda_{n+2}}\|u_{n+3}-u_{n+2}\|^2,
$$

and

$$
R_n=\varepsilon_{n+2}.
$$

The energy estimate with $k=n+2$ becomes

$$
E_{n+1}+W_n\le E_n+R_n.
$$

The proof checks that $W_n\ge0$, $E_n\ge m$, and $R_n\ge0$, and that $R$ is summable by shifting the summability of $\varepsilon$. Then `alvarez_telescope_summable` is applied. That lemma says that if $E$ is bounded below, $W,R\ge0$, $R$ is summable, and $E_{n+1}+W_n\le E_n+R_n$, then $W$ is summable. Its mathematical content is that summing the inequality gives a bound for $\sum W_n$ in terms of the initial energy and $\sum R_n$, up to the lower bound on $E$. Hence

$$
\sum W_n<\infty.
$$

The proof splits $W=A+B$, where

$$
A_n=
\frac{\alpha_{n+2}}{2\lambda_{n+2}}\|u_{n+3}-2u_{n+2}+u_{n+1}\|^2,
$$

$$
B_n=
\frac{1-\alpha_{n+2}}{\lambda_{n+2}}\|u_{n+3}-u_{n+2}\|^2.
$$

Both are nonnegative and bounded above by $W_n$, so both are summable by comparison. Since nonnegative summable sequences tend to zero, the proof obtains

$$
A_n\to0,\qquad B_n\to0.
$$

From $A_n\to0$, the proof shows that the second difference multiplied by $\alpha/\lambda$ tends to zero:

$$
\frac{\alpha_{n+2}}{\lambda_{n+2}}
\bigl(u_{n+3}-2u_{n+2}+u_{n+1}\bigr)\to0.
$$

It applies `alvarez_tendsto_zero_of_sq_le`, which states that if $q\to0$, $C\ge0$, and $\|v_n\|^2\le Cq_n$ for all $n$, then $v_n\to0$. Here $q=A$ and $C=2/c$. The required bound follows from $\alpha_k\le1$, $\lambda_k\ge c$, hence $\alpha_k/\lambda_k\le1/c$, and then

$$
\left(\frac{\alpha_k}{\lambda_k}\right)^2
\le \frac{2}{c}\cdot\frac{\alpha_k}{2\lambda_k}.
$$

The shift back from $n+2$ to $k$ is made with `alvarez_tendsto_of_nat_add`, which says that convergence of a sequence after adding a fixed natural number is equivalent to convergence of the original sequence.

Similarly, from $B_n\to0$, the proof obtains

$$
\frac{1-\alpha_{n+2}}{\lambda_{n+2}}
\bigl(u_{n+3}-u_{n+2}\bigr)\to0,
$$

again using `alvarez_tendsto_zero_of_sq_le`, now with $C=1/c$. After shifting back,

$$
\frac{1-\alpha_k}{\lambda_k}(u_{k+1}-u_k)\to0.
$$

Adding the two limits gives

$$
\frac{\alpha_k}{\lambda_k}(u_{k+1}-2u_k+u_{k-1})
+\frac{1-\alpha_k}{\lambda_k}(u_{k+1}-u_k)\to0.
$$

The proof then invokes `alvarez_residual_decomposition`, which is the algebraic identity

$$
u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}
=
\alpha_k(u_{k+1}-2u_k+u_{k-1})
+(1-\alpha_k)(u_{k+1}-u_k).
$$

After multiplying by $(\lambda_k)^{-1}$, the left-hand side is exactly the residual $(\lambda_k)^{-1}R_k$. Therefore the residual tends to zero:

$$
(\lambda_k)^{-1}R_k\to0.
$$

This proves the first part of the conclusion.

For the second part, the proof uses the witness $p_k=-(\lambda_k)^{-1}R_k$. Since $p_k$ belongs to $\partial_{\varepsilon_k}f(u_{k+1})$, the distance from $0$ to that subdifferential is at most $\|p_k\|$:

$$
\mathrm{dist}\bigl(0,\partial_{\varepsilon_k}f(u_{k+1})\bigr)
\le \|p_k\|
=\|(\lambda_k)^{-1}R_k\|.
$$

The right-hand side tends to zero by the first conclusion. The proof first shifts by one index and then shifts back using `alvarez_tendsto_of_nat_add`. The squeeze theorem for nonnegative quantities gives

$$
\mathrm{dist}\bigl(0,\partial_{\varepsilon_k}f(u_{k+1})\bigr)\to0.
$$

This proves the second part.

The rest of the proof establishes the conditional weak convergence. The proof assumes that $\mathrm{argmin} f$ is nonempty, that there exists $\mathrm{alphaBar}\in(0,1)$ with $\alpha_k\le\mathrm{alphaBar}$ for all $k$, and that if some $\alpha_k$ is positive then $\lambda_k$ is bounded above.

First, the proof converts the closed epigraph hypothesis into lower semicontinuity of $f$. It uses `lowerSemicontinuous_iff_isClosed_epigraph`, which says that $f$ is lower semicontinuous exactly when its epigraph is closed. Since `hClosed` gives closedness of the epigraph, $f$ is lower semicontinuous. Then `lowerSemicontinuous_iff_isClosed_lowerLevelSet` gives that every lower level set

$$
\mathrm{lowerLevelSet} f(r)=\{x:f(x)\le (r:\overline{\mathbb R})\}
$$

is closed. Next, `alvarez_lower_level_convex` states that convexity of the epigraph of $f$ implies convexity of each lower level set. Therefore every lower level set is closed and convex.

For a minimizer $z\in\mathrm{argmin} f$, the proof derives an inner-product inequality. Using the witness $p_k=-(\lambda_k)^{-1}R_k$, the $\varepsilon_k$-subgradient inequality at $y=z$ gives

$$
f(z)\ge f(u_{k+1})+\langle p_k,z-u_{k+1}\rangle-\varepsilon_k.
$$

Since $z$ minimizes $f$, one has $f(z)\le f(u_{k+1})$. After converting the finite values to real numbers, this yields

$$
\langle R_k,u_{k+1}-z\rangle\le \lambda_k\varepsilon_k.
$$

The proof then applies `alvarez_phi_recurrence_of_inner`. That lemma takes $\alpha_k\ge0$ and the above inner inequality and produces the recurrence

$$
\begin{aligned}
&\frac12\|u_{k+1}-z\|^2
-(1+\alpha_k)\frac12\|u_k-z\|^2
+\alpha_k\frac12\|u_{k-1}-z\|^2\\
&\le
\alpha_k\|u_k-u_{k-1}\|^2
+\frac{\alpha_k}{2}\|u_{k+1}-u_k\|^2
+\lambda_k\varepsilon_k.
\end{aligned}
$$

The right-hand side is exactly the sequence $\delta_k$ defined in the proof:

$$
\delta_k=
\alpha_k\|u_k-u_{k-1}\|^2
+\frac{\alpha_k}{2}\|u_{k+1}-u_k\|^2
+\lambda_k\varepsilon_k.
$$

The proof checks that $\delta_k\ge0$ for every $k$.

It remains to show that $\delta$ is summable. The proof splits into two cases. If there is no $k$ with $\alpha_k>0$, then $\alpha_k=0$ for all $k$, so $\delta_k=\lambda_k\varepsilon_k$, and summability follows from `hErrors`. If some $\alpha_k$ is positive, then the assumed upper bound on $\lambda_k$ gives $\lambda_k\le L_0$. The proof sets $L=\max(L_0,1)>0$ and

$$
q=\frac{1-\mathrm{alphaBar}}{L}>0.
$$

Using $\alpha_k\le\mathrm{alphaBar}$ and $\lambda_k\le L$, it obtains

$$
q\le \frac{1-\alpha_k}{\lambda_k}.
$$

Since

$$
B_n=
\frac{1-\alpha_{n+2}}{\lambda_{n+2}}
\|u_{n+3}-u_{n+2}\|^2
$$

is summable and $q>0$, this forces

$$
\sum_n \|u_{n+3}-u_{n+2}\|^2<\infty.
$$

Shifting the index gives summability of $\|u_{k+1}-u_k\|^2$ and of $\|u_k-u_{k-1}\|^2$. Because $0\le\alpha_k\le1$, the two first terms of $\delta_k$ are bounded by constant multiples of these summable squared differences. The last term $\lambda_k\varepsilon_k$ is summable by `hErrors`. Hence $\delta$ is summable.

Now `alvarez_norm_converges_of_recurrence` is applied to $u$, any minimizer $z$, the sequences $\alpha$ and $\delta$, and the bound $\mathrm{alphaBar}$. Its hypotheses are exactly $0\le\alpha_k$, $\alpha_k\le\mathrm{alphaBar}$, $\mathrm{alphaBar}<1$, $\delta_k\ge0$, $\sum\delta_k<\infty$, and the recurrence above. Its conclusion is that for each minimizer $z$ there exists a real number $l$ such that

$$
\|u_k-z\|\to l.
$$

This is a key stability property of the inertial method: the distance to every minimizer converges.

Next the proof shows that every weak sequential cluster point of $u_k$ is a minimizer. By the definition of `IsSequentialClusterPt`, a weak cluster point $z$ comes with a strictly increasing map $\phi:\mathbb N\to\mathbb N$ such that

$$
u_{\phi(n)}\rightharpoonup z
$$

weakly. Choose any minimizer $z_0$. Since $\|u_k-z_0\|$ converges by the previous step, `bounded_range_of_convergent_distance_to_point` implies that the range of $u$ is bounded. Using this boundedness and the already-proved residual convergence, `alvarez_inner_tendsto_zero_of_bounded` gives

$$
\langle (\lambda_k)^{-1}R_k,u_k-z_0\rangle\to0
$$

and also

$$
\langle (\lambda_k)^{-1}R_k,u_{k+1}-z_0\rangle\to0.
$$

The lemma used here says that if $v_k\to0$ and $x_k$ is bounded, then $\langle v_k,x_k\rangle\to0$.

From the $\varepsilon_k$-subgradient inequality at $z_0$, the proof obtains the upper bound

$$
(f(u_{k+1}))_{\mathbb R}-(f(z_0))_{\mathbb R}
\le
-\langle (\lambda_k)^{-1}R_k,u_{k+1}-z_0\rangle
+\varepsilon_k.
$$

The right-hand side tends to zero because the inner product tends to zero and $\varepsilon_k\to0$, the latter following from summability of $\varepsilon$. On the other hand, since $z_0$ is a minimizer,

$$
0\le (f(u_k))_{\mathbb R}-(f(z_0))_{\mathbb R}
$$

for all sufficiently large $k$. A squeeze argument therefore gives

$$
(f(u_k))_{\mathbb R}-(f(z_0))_{\mathbb R}\to0.
$$

Composing with the subsequence $\phi$ gives

$$
(f(u_{\phi(n)}))_{\mathbb R}-(f(z_0))_{\mathbb R}\to0.
$$

Now fix $d>0$. Since the above gap tends to zero, eventually

$$
(f(u_{\phi(n)}))_{\mathbb R}-(f(z_0))_{\mathbb R}<d.
$$

Thus, for all sufficiently large $n$,

$$
u_{\phi(n)}\in \mathrm{lowerLevelSet} f\bigl((f(z_0))_{\mathbb R}+d\bigr).
$$

The proof shifts the subsequence by a large natural number $M$ to make this membership hold for every term of the shifted subsequence. That lower level set is closed and convex, as established earlier. Since

$$
u_{\phi(n+M)}\rightharpoonup z
$$

weakly, the theorem `mem_of_tendsto_weakly_of_isClosed_convex` implies that the weak limit belongs to the closed convex set. Hence

$$
z\in \mathrm{lowerLevelSet} f\bigl((f(z_0))_{\mathbb R}+d\bigr),
$$

which means

$$
f(z)\le (f(z_0))_{\mathbb R}+d.
$$

Letting $d\downarrow0$ gives $f(z)\le f(z_0)$. Since $z_0$ is a minimizer, $z$ is also a minimizer. Thus every weak sequential cluster point of $u$ lies in $\mathrm{argmin} f$.

Finally, the proof applies `opial_lemma`. In a complete real inner product space, if $C$ is nonempty, if for every $z\in C$ the distance $\|u_k-z\|$ converges, and if every weak sequential cluster point of $u$ belongs to $C$, then there exists $z\in C$ such that $u_k\rightharpoonup z$. Here $C=\mathrm{argmin} f$. The nonemptiness hypothesis is `hArgmin`, the distance-convergence hypothesis is provided by `hdist`, and the cluster-point hypothesis is provided by `hcluster`. The conclusion is exactly

$$
\exists \hat u\in\mathrm{argmin} f,\qquad
u_k\rightharpoonup \hat u
$$

weakly. This completes the proof.

