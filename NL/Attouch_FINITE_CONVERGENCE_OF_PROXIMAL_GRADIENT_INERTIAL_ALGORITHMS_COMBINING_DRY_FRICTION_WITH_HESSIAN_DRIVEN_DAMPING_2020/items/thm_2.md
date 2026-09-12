## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/thm_2.lean`

## Lean statement
```lean
theorem IPAHDD_geometric_and_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (f phi : H → ℝ) (h gamma beta L r : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDD f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta) (xInf : H)
    (hf : ContDiff ℝ 1 f)
    (hL : HasLipschitzGradient (gradient f) L) (hL_nonneg : 0 ≤ L)
    (_hbelow : ∃ c : ℝ, ∀ x, c ≤ f x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hlimit : Filter.Tendsto alg.x Filter.atTop (nhds xInf)) :
    let q
```

## Statement explanation
The theorem is a convergence and finite-termination result for the IPAHDD algorithm in a real Hilbert space $H$. The space $H$ is assumed to be a complete real inner product space, so that gradients, inner products, norms, limits, and proximal operators behave as in Hilbert-space convex analysis. The functions are $f:H\to\mathbb R$ and $\phi:H\to\mathbb R$. The real parameters are $h,\gamma,\beta,L,r$. The hypothesis `hdf : DF_r phi r` is a bundled condition on $\phi$ and $r$; in the proof it is used through the visible consequences that $\phi$ viewed as an extended-real function belongs to the class $\Gamma_0(H)$, that the value of $\phi$ at $0$ is treated as $0$, and that every point of norm $<r$ belongs to the subdifferential $\partial\phi(0)$. The object `alg : IPAHDD f phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta` is the IPAHDD algorithm, with iterate sequence denoted $x_k=\text{alg.x}(k)$, and $x_\infty$ is a point of $H$.

The analytic hypotheses are: $f$ is $C^1$ (`hf : ContDiff ℝ 1 f`); the gradient of $f$ is Lipschitz with constant $L$, meaning

$$
\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|
$$

for all $x,y$, and $L\ge 0$; $f$ is bounded below; $h>0$, $\gamma>0$, $\beta>0$; and

$$
\gamma\ge L\left(\frac h2+\beta\right).
$$

Finally,

$$
\text{alg.x}\to x_\infty
$$

as $k\to\infty$ in the filter sense `Filter.Tendsto alg.x Filter.atTop (nhds xInf)`.

The conclusion binds

$$
q=\frac{1}{\sqrt{1+\frac{2h(\gamma-\beta L)}{1+\beta h L}}}
$$

and asserts a conjunction of two implications. First, if

$$
-\nabla f(x_\infty)\in \mathrm{interior}\bigl(\partial\phi(0)\bigr),
$$

then $0<q<1$ and there exists $k_0$ such that for every $k\ge k_0$,

$$
\|x_{k+1}-x_k\|\le q^{k-k_0}\|x_{k_0+1}-x_{k_0}\|,
$$

and

$$
\|x_k-x_\infty\|\le \frac{q^{k-k_0}}{1-q}\|x_{k_0+1}-x_{k_0}\|.
$$

Thus the algorithm converges geometrically to $x_\infty$ at an explicit rate $q$. Second, if

$$
\|\nabla f(x_\infty)\|<r,
$$

then there exists a stopping index $k_{\mathrm{Stop}}$ such that for every $k\ge k_{\mathrm{Stop}}$,

$$
x_{k+1}=x_k.
$$

So the algorithm is eventually constant. The bounded-below hypothesis `_hbelow` is part of the statement but is not invoked explicitly in the proof shown.

## Lean proof
```lean
1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))
    (-gradient f xInf ∈ interior (subdifferential phi 0) →
      0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
        ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
        ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
    (‖gradient f xInf‖ < r → ∃ kStop, ∀ k ≥ kStop, alg.x (k + 1) = alg.x k) := by
  dsimp
  rcases hpositive with ⟨hh, hg, hb⟩
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hq := ipahdd_rate_mem_Ioo h gamma beta L hh hg hb hL_nonneg hgamma
  constructor
  · intro hinterior
    refine ⟨hq.1, hq.2, ?_⟩
    let d : ℕ → H := fun k => alg.x (k + 1) - alg.x k
    let v : ℕ → H := fun k => (1 / h) • d k
    have hdv (k : ℕ) : d k = h • v k := by
      dsimp [d, v]
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    have hshift (k : ℕ) :
        ∃ s, s ∈ subdifferential phi (v (k + 1)) ∧
          (v (k + 1) - v k + gamma • d (k + 1) + h • s +
            beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
            h • gradient f (alg.x (k + 1)) = 0) := by
      simpa [d, v, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ipahdd_shifted_recurrence_local f phi hdf.toEReal_mem_gammaZero h gamma beta alg hh hg k
    have hraw (k : ℕ) :
        (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
          (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
          gamma * h * ‖v (k + 1)‖ ^ 2 + h * phi (v (k + 1)) +
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) ≤ 0 := by
      obtain ⟨s, hs, hrec⟩ := hshift k
      have hinner := congrArg (fun z : H => inner ℝ z (v (k + 1))) hrec
      have hinert := inner_sub_self_energy_identity_local (v (k + 1)) (v k)
      have hdamp : inner ℝ (gamma • d (k + 1)) (v (k + 1)) =
          gamma * h * ‖v (k + 1)‖ ^ 2 := by
        rw [hdv (k + 1), inner_smul_left, inner_smul_left,
          real_inner_self_eq_norm_sq]
        simp only [starRingEnd_apply, star_trivial]
        ring
      have hsterm : inner ℝ (h • s) (v (k + 1)) = h * inner ℝ s (v (k + 1)) := by
        rw [inner_smul_left]
        simp only [starRingEnd_apply, star_trivial]
      have hbetaterm :
          inner ℝ (beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) (v (k + 1)) =
            beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
        rw [inner_smul_left]
        simp only [starRingEnd_apply, star_trivial]
      have hgradterm : inner ℝ (h • gradient f (alg.x (k + 1))) (v (k + 1)) =
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
        dsimp [v]
        rw [inner_smul_left, inner_smul_right]
        simp only [starRingEnd_apply, star_trivial]
        field_simp [hh.ne']
      have hscalar :
          (1 / 2 : ℝ) * ‖v (k + 1)‖ ^ 2 - (1 / 2 : ℝ) * ‖v k‖ ^ 2 +
            (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 +
            gamma * h * ‖v (k + 1)‖ ^ 2 + h * inner ℝ s (v (k + 1)) +
            beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) +
            inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) = 0 := by
        simpa only [inner_add_left, inner_sub_left, inner_zero_left, add_zero,
          hinert, hdamp, hsterm, hbetaterm, hgradterm] using hinner
      have hphi : phi (v (k + 1)) ≤ inner ℝ s (v (k + 1)) := by
        have hs0 := hs 0
        change (⟪0 - v (k + 1), s⟫_ℝ : EReal) + (phi (v (k + 1)) : EReal) ≤
          (phi 0 : EReal) at hs0
        norm_cast at hs0
        simp only [zero_sub, inner_neg_left, hdf.value_at_zero, neg_add_le_iff_le_add,
          add_zero] at hs0
        rw [real_inner_comm] at hs0
        linarith
      have hhphi := mul_le_mul_of_nonneg_left hphi hh.le
      linarith
    obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp hinterior)
    let eps : ℝ := rho / 2
    have heps : 0 < eps := by dsimp [eps]; positivity
    have hgradlim : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop
        (nhds (gradient f xInf)) := hC1.tendsto xInf |>.comp hlimit
    have hgradtail : ∀ᶠ k : ℕ in Filter.atTop,
        ‖gradient f (alg.x k) - gradient f xInf‖ < eps := by
      have hzero : Filter.Tendsto (fun k => gradient f (alg.x k) - gradient f xInf)
          Filter.atTop (nhds 0) := by
        simpa using hgradlim.sub (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => gradient f xInf) Filter.atTop (nhds (gradient f xInf)))
      simpa using hzero.norm.eventually
        (eventually_lt_nhds (show ‖(0 : H)‖ < eps by simpa using heps))
    obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hgradtail
    have htranslated (k : ℕ) (hk : k0 ≤ k) (u : H) (hu : ‖u‖ ≤ 1) :
        -gradient f (alg.x (k + 1)) + eps • u ∈ subdifferential phi 0 := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hrewrite :
          (-gradient f (alg.x (k + 1)) + eps • u) - -gradient f xInf =
            -(gradient f (alg.x (k + 1)) - gradient f xInf) + eps • u := by
        abel
      rw [hrewrite]
      calc
        ‖-(gradient f (alg.x (k + 1)) - gradient f xInf) + eps • u‖ ≤
            ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ + ‖eps • u‖ := by
              calc
                _ ≤ ‖-(gradient f (alg.x (k + 1)) - gradient f xInf)‖ + ‖eps • u‖ := norm_add_le _ _
                _ = _ := by rw [norm_neg]
        _ = ‖gradient f (alg.x (k + 1)) - gradient f xInf‖ + eps * ‖u‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos heps]
        _ < eps + eps * ‖u‖ := by
              gcongr
              exact hk0 (k + 1) (by omega)
        _ ≤ eps + eps := by
              gcongr
              simpa using mul_le_mul_of_nonneg_left hu heps.le
        _ = rho := by dsimp [eps]; ring
    have hfricInterior (k : ℕ) (hk : k0 ≤ k) :
        eps * ‖v (k + 1)‖ ≤
          phi (v (k + 1)) + inner ℝ (gradient f (alg.x (k + 1))) (v (k + 1)) := by
      by_cases hv0 : v (k + 1) = 0
      · simp [hv0, hdf.value_at_zero]
      · let u : H := (‖v (k + 1)‖)⁻¹ • v (k + 1)
        have hvpos : 0 < ‖v (k + 1)‖ := norm_pos_iff.mpr hv0
        have hu : ‖u‖ ≤ 1 := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
          field_simp [hvpos.ne']
          norm_num
        have hs := htranslated k hk u hu
        have hsub := hs (v (k + 1))
        have hinner : inner ℝ u (v (k + 1)) = ‖v (k + 1)‖ := by
          dsimp [u]
          rw [inner_smul_left, real_inner_self_eq_norm_sq]
          simp only [map_inv₀, starRingEnd_apply, star_trivial]
          field_simp [hvpos.ne']
        change (⟪v (k + 1) - 0, -gradient f (alg.x (k + 1)) + eps • u⟫_ℝ : EReal) +
            (phi 0 : EReal) ≤ (phi (v (k + 1)) : EReal) at hsub
        norm_cast at hsub
        simp only [sub_zero] at hsub
        rw [hdf.value_at_zero, inner_add_right, inner_neg_right, inner_smul_right] at hsub
        rw [real_inner_comm (gradient f (alg.x (k + 1))) (v (k + 1)),
          real_inner_comm u (v (k + 1)), hinner] at hsub
        linarith
    have hcross_lower (k : ℕ) :
        -(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2)) ≤
          beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
      have hnormv : ‖v (k + 1)‖ = ‖d (k + 1)‖ / h := by
        dsimp [v]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / h)]
        ring
      have hnormgrad :
          ‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ ≤ L * ‖d k‖ := by
        simpa [d] using hL (alg.x (k + 1)) (alg.x k)
      have hprod := mul_le_mul_of_nonneg_right hnormgrad (norm_nonneg (v (k + 1)))
      have hinter :
          -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) ≤
            inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
        calc
          -(L * ‖d k‖ * (‖d (k + 1)‖ / h)) =
              -((L * ‖d k‖) * ‖v (k + 1)‖) := by rw [hnormv]
          _ ≤ -(‖gradient f (alg.x (k + 1)) - gradient f (alg.x k)‖ * ‖v (k + 1)‖) :=
              neg_le_neg hprod
          _ ≤ inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) :=
              neg_le_of_abs_le (abs_real_inner_le_norm _ _)
      have hmul := mul_le_mul_of_nonneg_left hinter hb.le
      have hyoung : 2 * (‖d k‖ * ‖d (k + 1)‖) ≤
          ‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖d k‖ - ‖d (k + 1)‖)]
      have hcoef : 0 ≤ beta * L / h := by positivity
      have hyoung' := mul_le_mul_of_nonneg_left hyoung hcoef
      field_simp [hh.ne'] at hmul hyoung' ⊢
      nlinarith
    have hsq_contract (k : ℕ) (hk : k0 ≤ k) :
        (1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖d (k + 1)‖ ^ 2 ≤
          (1 + beta * h * L) * ‖d k‖ ^ 2 := by
      have hnorm (j : ℕ) : ‖d j‖ = h * ‖v j‖ := by
        rw [hdv j, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
      have hraw' := hraw k
      have hfric := hfricInterior k hk
      have hcross := hcross_lower k
      have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖v (k + 1) - v k‖ ^ 2 := by positivity
      have hrawtwo := mul_le_mul_of_nonneg_left hraw' (show (0 : ℝ) ≤ 2 by norm_num)
      have hfric' := mul_le_mul_of_nonneg_left hfric hh.le
      have hgradscale :
          inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) =
            h * inner ℝ (gradient f (alg.x (k + 1))) (v (k + 1)) := by
        rw [hdv (k + 1), inner_smul_right]
      have hfricscale : h * eps * ‖v (k + 1)‖ ≤
          h * phi (v (k + 1)) + inner ℝ (gradient f (alg.x (k + 1))) (d (k + 1)) := by
        rw [hgradscale]
        nlinarith [hfric']
      have hcrossv :
          -(beta * L * h * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2)) ≤
            2 * beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) (v (k + 1)) := by
        calc
          -(beta * L * h * (‖v k‖ ^ 2 + ‖v (k + 1)‖ ^ 2)) =
              2 * (-(beta * L / (2 * h) * (‖d k‖ ^ 2 + ‖d (k + 1)‖ ^ 2))) := by
                rw [hnorm k, hnorm (k + 1)]
                field_simp [hh.ne']
          _ ≤ 2 * (beta * inner ℝ (gradient f (alg.x (k + 1)) - gradient f (alg.x k))
              (v (k + 1))) := mul_le_mul_of_nonneg_left hcross (by norm_num)
          _ = _ := by ring
      have hvcontract :
          (1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖v (k + 1)‖ ^ 2 ≤
            (1 + beta * h * L) * ‖v k‖ ^ 2 := by
        have hepsnorm : 0 ≤ h * eps * ‖v (k + 1)‖ := by positivity
        nlinarith [hrawtwo, hcrossv, hfricscale]
      rw [hnorm k, hnorm (k + 1)]
      calc
        (1 + beta * h * L + 2 * h * (gamma - beta * L)) * (h * ‖v (k + 1)‖) ^ 2 =
            h ^ 2 * ((1 + beta * h * L + 2 * h * (gamma - beta * L)) * ‖v (k + 1)‖ ^ 2) := by ring
        _ ≤ h ^ 2 * ((1 + beta * h * L) * ‖v k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hvcontract (sq_nonneg h)
        _ = (1 + beta * h * L) * (h * ‖v k‖) ^ 2 := by ring
    have hgap : 0 < gamma - beta * L := by
      rcases hL_nonneg.eq_or_lt with rfl | hLpos
      · simpa using hg
      · have hstrict : beta * L < L * (h / 2 + beta) := by
          nlinarith [mul_pos hLpos hh]
        nlinarith [hgamma, hstrict]
    have hB : 0 < 1 + beta * h * L := by positivity
    have hA : 0 < 1 + beta * h * L + 2 * h * (gamma - beta * L) := by
      nlinarith [mul_pos hh hgap]
    have hq_sq :
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ 2 *
            (1 + beta * h * L + 2 * h * (gamma - beta * L)) =
          1 + beta * h * L := by
      have hratio :
          (1 + beta * h * L + 2 * h * (gamma - beta * L)) / (1 + beta * h * L) =
            1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L) := by
        field_simp [hB.ne']
      have hhelper := ipahdd_q_sq_mul_A_eq_B_local h gamma beta L hh hB hgap
      dsimp only at hhelper
      rw [hratio] at hhelper
      exact hhelper
    have hcontract (k : ℕ) (hk : k0 ≤ k) :
        ‖d (k + 1)‖ ≤
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) * ‖d k‖ := by
      have hsquare : ‖d (k + 1)‖ ^ 2 ≤
          ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) * ‖d k‖) ^ 2 := by
        have hmain := hsq_contract k hk
        have hrewrite : 1 + beta * h * L =
            (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ 2 *
              (1 + beta * h * L + 2 * h * (gamma - beta * L)) := hq_sq.symm
        rw [hrewrite] at hmain
        have hmul := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hA.le)
        field_simp [hA.ne'] at hmul
        nlinarith
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq.1.le (norm_nonneg _))).mp hsquare
    have hgeom (n : ℕ) : ‖d (k0 + n)‖ ≤
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n * ‖d k0‖ := by
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            ‖d (k0 + (n + 1))‖ = ‖d ((k0 + n) + 1)‖ := by congr 2
            _ ≤ (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                (1 + beta * h * L))) * ‖d (k0 + n)‖ :=
              hcontract (k0 + n) (Nat.le_add_right k0 n)
            _ ≤ (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                (1 + beta * h * L))) *
                ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                  (1 + beta * h * L))) ^ n * ‖d k0‖) :=
              mul_le_mul_of_nonneg_left ih hq.1.le
            _ = (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
                (1 + beta * h * L))) ^ (n + 1) * ‖d k0‖ := by
              rw [pow_succ]
              ring
    have hsum (n p : ℕ) :
        (∑ i ∈ Finset.range p,
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ (n + i)) ≤
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ n /
            (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L)))) := by
      exact geometric_range_sum_le_local _ hq.1.le hq.2 n p
    have htel (n p : ℕ) :
        alg.x (k0 + n + p) - alg.x (k0 + n) =
          ∑ i ∈ Finset.range p, d (k0 + n + i) := by
      induction p with
      | zero => simp
      | succ p ih =>
          rw [Finset.sum_range_succ, ← ih]
          dsimp [d]
          convert (show alg.x (k0 + n + p + 1) - alg.x (k0 + n) =
              (alg.x (k0 + n + p) - alg.x (k0 + n)) +
                (alg.x (k0 + n + p + 1) - alg.x (k0 + n + p)) by abel) using 1
    have htail (n p : ℕ) :
        ‖alg.x (k0 + n) - alg.x (k0 + n + p)‖ ≤
          (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
            (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L)))) * ‖d k0‖ := by
      calc
        ‖alg.x (k0 + n) - alg.x (k0 + n + p)‖ =
            ‖-(alg.x (k0 + n) - alg.x (k0 + n + p))‖ := (norm_neg _).symm
        _ = ‖alg.x (k0 + n + p) - alg.x (k0 + n)‖ := by
            congr 1
            abel
        _ = ‖∑ i ∈ Finset.range p, d (k0 + n + i)‖ := by rw [htel]
        _ ≤ ∑ i ∈ Finset.range p, ‖d (k0 + n + i)‖ :=
          norm_sum_le (Finset.range p) (fun i => d (k0 + n + i))
        _ ≤ ∑ i ∈ Finset.range p,
            (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ (n + i) * ‖d k0‖ := by
              apply Finset.sum_le_sum
              intro i hi
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hgeom (n + i)
        _ = (∑ i ∈ Finset.range p,
            (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))) ^ (n + i)) * ‖d k0‖ := by
              rw [Finset.sum_mul]
        _ ≤ ((1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L))) ^ n /
            (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
              (1 + beta * h * L))))) * ‖d k0‖ :=
              mul_le_mul_of_nonneg_right (hsum n p) (norm_nonneg _)
    refine ⟨k0, ?_⟩
    intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hdist : ‖alg.x (k0 + n) - xInf‖ ≤
        (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) / (1 + beta * h * L))) ^ n /
          (1 - (1 / Real.sqrt (1 + 2 * h * (gamma - beta * L) /
            (1 + beta * h * L)))) * ‖d k0‖ := by
      apply le_of_tendsto
        ((tendsto_const_nhds.sub
          (hlimit.comp (Filter.tendsto_add_atTop_nat (k0 + n)))).norm)
      filter_upwards with p
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail n p
    constructor
    · simpa [d] using hgeom n
    · simpa [d] using hdist
  · intro hmargin
    let D : ℝ := 1 + h * gamma
    let lam : ℝ := h / D
    let z : ℕ → H := fun k =>
      (1 / (h * D)) • (alg.x (k + 1) - alg.x k) -
        (beta / D) • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) -
        lam • gradient f (alg.x (k + 1))
    have hD : 0 < D := by
      dsimp [D]
      nlinarith [mul_pos hh hg]
    have hlam : 0 < lam := by
      dsimp [lam]
      exact div_pos hh hD
    have hxshift : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
      simpa using hlimit.comp (Filter.tendsto_add_atTop_nat 1)
    have hinc : Filter.Tendsto (fun k => alg.x (k + 1) - alg.x k)
        Filter.atTop (nhds 0) := by
      simpa using hxshift.sub hlimit
    have hgradlim : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop
        (nhds (gradient f xInf)) := hC1.tendsto xInf |>.comp hlimit
    have hgradshift : Filter.Tendsto (fun k => gradient f (alg.x (k + 1))) Filter.atTop
        (nhds (gradient f xInf)) := by
      simpa using hgradlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hgraddiff : Filter.Tendsto
        (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) := by
      simpa using hgradshift.sub hgradlim
    have hzlim : Filter.Tendsto z Filter.atTop (nhds (lam • (-gradient f xInf))) := by
      dsimp [z]
      simpa using ((hinc.const_smul (1 / (h * D))).sub
        (hgraddiff.const_smul (beta / D))).sub (hgradshift.const_smul lam)
    have hscaled : Filter.Tendsto (fun k => lam⁻¹ • z k) Filter.atTop
        (nhds (-gradient f xInf)) := by
      have := hzlim.const_smul lam⁻¹
      simpa only [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul] using this
    have hsmall : ∀ᶠ k : ℕ in Filter.atTop, ‖lam⁻¹ • z k‖ < r := by
      exact hscaled.norm.eventually (eventually_lt_nhds (by simpa using hmargin))
    rcases Filter.eventually_atTop.1 hsmall with ⟨kStop, hkStop⟩
    have hnext : ∀ j ≥ kStop, alg.x (j + 2) = alg.x (j + 1) := by
      intro j hj
      have hmem : lam⁻¹ • z j ∈ subdifferential phi 0 := hdf.ball_subset (by
        simpa [Metric.mem_ball, dist_eq_norm] using hkStop j hj)
      have hzero : IsProximalPoint phi lam (z j) 0 := by
        refine ⟨hlam, ?_⟩
        simpa [sub_zero] using hmem
      have hp : IsProximalPoint phi lam (z j)
          (ERealFunction.scaledProximityOperator phi.toEReal hdf.toEReal_mem_gammaZero
            ⟨lam, hlam⟩ (z j)) :=
        ⟨hlam, ERealFunction.scaledProximityOperator_residual_mem
          hdf.toEReal_mem_gammaZero ⟨lam, hlam⟩ (z j)⟩
      have hpzero :
          ERealFunction.scaledProximityOperator phi.toEReal hdf.toEReal_mem_gammaZero
            ⟨lam, hlam⟩ (z j) = 0 :=
        proximal_point_eq_zero_of_subgradient_ball phi lam hlam (z j) _ hp hzero
      have hupdate : alg.x (j + 2) = alg.x (j + 1) + h •
          ERealFunction.scaledProximityOperator phi.toEReal hdf.toEReal_mem_gammaZero
            ⟨lam, hlam⟩
            ((1 / (h * (1 + h * gamma))) • (alg.x (j + 1) - alg.x j) -
              (beta / (1 + h * gamma)) • (gradient f (alg.x (j + 1)) - gradient f (alg.x j)) -
              (h / (1 + h * gamma)) • gradient f (alg.x (j + 1))) := by
        simpa [lam, D] using alg.update j
      have hz :
          (1 / (h * (1 + h * gamma))) • (alg.x (j + 1) - alg.x j) -
              (beta / (1 + h * gamma)) • (gradient f (alg.x (j + 1)) - gradient f (alg.x j)) -
              (h / (1 + h * gamma)) • gradient f (alg.x (j + 1)) = z j := by
        rfl
      rw [hz, hpzero] at hupdate
      simpa using hupdate
    refine ⟨kStop + 1, ?_⟩
    intro k hk
    have hkstop : k - 1 ≥ kStop := by omega
    have hsucc := hnext (k - 1) hkstop
    have hindex : k - 1 + 2 = k + 1 := by omega
    have hindex' : k - 1 + 1 = k := by omega
    rw [hindex] at hsucc
    rw [hindex'] at hsucc
    exact hsucc
```

## Proof explanation
The proof starts with `dsimp`, which unfolds the let-binding for $q$, so the goal becomes the two-implication statement with $q$ replaced by

$$
\frac{1}{\sqrt{1+\frac{2h(\gamma-\beta L)}{1+\beta h L}}}.
$$

Then `rcases hpositive with ⟨hh, hg, hb⟩` extracts $h>0$, $\gamma>0$, and $\beta>0$. The line
`have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf`
uses the cited result `continuous_gradient_of_contDiff`: since $f$ is $C^1$, its gradient $\nabla f$ is continuous. This is later used to pass limits through gradients when $x_k\to x_\infty$.

Next,
`have hq := ipahdd_rate_mem_Ioo h gamma beta L hh hg hb hL_nonneg hgamma`
applies the cited rate lemma. Its statement is exactly that, under $h>0$, $\gamma>0$, $\beta>0$, $L\ge0$, and $\gamma\ge L(h/2+\beta)$, the number

$$
\frac{1}{\sqrt{1+\frac{2h(\gamma-\beta L)}{1+\beta h L}}}
$$

satisfies $0<q<1$. This supplies the first two conjuncts of the first implication.

The proof then uses `constructor` to split the conjunction into two goals.

For the first goal, the proof introduces `hinterior`, the hypothesis

$$
-\nabla f(x_\infty)\in\mathrm{interior}\bigl(\partial\phi(0)\bigr),
$$

and refines the goal to $\langle hq.1,hq.2,?\rangle$, leaving only the existence of $k_0$ and the two geometric bounds.

It defines

$$
d_k=x_{k+1}-x_k,\qquad v_k=\frac1h d_k.
$$

Thus $d_k=h v_k$, proved in the local fact `hdv`. The cited recurrence lemma `ipahdd_shifted_recurrence_local` is applied through `hshift`: for every $k$, there exists $s\in\partial\phi(v_{k+1})$ such that

$$
v_{k+1}-v_k+\gamma d_{k+1}+h s
+\beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
+h\nabla f(x_{k+1})=0.
$$

This is the first-order optimality relation for the IPAHDD update, expressed in terms of the velocity variables $v_k$.

The proof then forms `hraw` by taking the inner product of this recurrence with $v_{k+1}$. The cited identity `inner_sub_self_energy_identity_local` says that for all $u,v\in H$,

$$
\langle u-v,u\rangle
=\frac12\|u\|^2-\frac12\|v\|^2+\frac12\|u-v\|^2.
$$

Applied with $u=v_{k+1}$ and $v=v_k$, it expands the first inner product. The proof also computes

$$
\langle \gamma d_{k+1},v_{k+1}\rangle
=\gamma h\|v_{k+1}\|^2,
$$

uses linearity of the inner product for the $h s$, $\beta$-gradient-difference, and $h\nabla f(x_{k+1})$ terms, and replaces $\langle h\nabla f(x_{k+1}),v_{k+1}\rangle$ by $\langle \nabla f(x_{k+1}),d_{k+1}\rangle$. From $s\in\partial\phi(v_{k+1})$, evaluated at $0$, and using the visible consequence $\phi(0)=0$, the proof obtains

$$
\phi(v_{k+1})\le \langle s,v_{k+1}\rangle.
$$

Multiplying by $h>0$ and replacing $h\langle s,v_{k+1}\rangle$ by the smaller quantity $h\phi(v_{k+1})$ in the recurrence identity yields the inequality

$$
\frac12\|v_{k+1}\|^2-\frac12\|v_k\|^2+\frac12\|v_{k+1}-v_k\|^2
+\gamma h\|v_{k+1}\|^2+h\phi(v_{k+1})
+\beta\langle \nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle
+\langle \nabla f(x_{k+1}),d_{k+1}\rangle\le 0.
$$

Next, the interior hypothesis is converted into a ball condition. The proof uses `Metric.mem_nhds_iff.mp` and `mem_interior_iff_mem_nhds.mp` to obtain a radius $\rho>0$ such that the ball around $-\nabla f(x_\infty)$ of radius $\rho$ is contained in $\partial\phi(0)$. It sets

$$
\varepsilon=\frac{\rho}{2}>0.
$$

Because $\nabla f$ is continuous and $x_k\to x_\infty$, the gradients satisfy

$$
\nabla f(x_k)\to \nabla f(x_\infty).
$$

Hence eventually

$$
\|\nabla f(x_k)-\nabla f(x_\infty)\|<\varepsilon.
$$

Let $k_0$ be such an index. For every $k\ge k_0$ and every $u\in H$ with $\|u\|\le1$, the point

$$
-\nabla f(x_{k+1})+\varepsilon u
$$

lies in the ball of radius $\rho$ around $-\nabla f(x_\infty)$, hence in $\partial\phi(0)$. This is the local fact `htranslated`.

The proof then derives the friction lower bound `hfricInterior`:

$$
\varepsilon\|v_{k+1}\|
\le \phi(v_{k+1})+\langle \nabla f(x_{k+1}),v_{k+1}\rangle.
$$

If $v_{k+1}=0$, this is immediate. Otherwise let

$$
u=\frac{1}{\|v_{k+1}\|}v_{k+1}.
$$

Then $\|u\|\le1$, and the subgradient inequality for $-\nabla f(x_{k+1})+\varepsilon u\in\partial\phi(0)$, evaluated at $v_{k+1}$, gives

$$
\langle v_{k+1},-\nabla f(x_{k+1})+\varepsilon u\rangle+\phi(0)
\le \phi(v_{k+1}).
$$

Using $\phi(0)=0$ and $\langle u,v_{k+1}\rangle=\|v_{k+1}\|$, this rearranges to the displayed friction bound.

A separate estimate `hcross_lower` controls the gradient-difference term. From the Lipschitz gradient hypothesis,

$$
\|\nabla f(x_{k+1})-\nabla f(x_k)\|\le L\|d_k\|.
$$

Together with Cauchy–Schwarz and Young’s inequality $2ab\le a^2+b^2$, the proof obtains

$$
-\frac{\beta L}{2h}\bigl(\|d_k\|^2+\|d_{k+1}\|^2\bigr)
\le
\beta\langle \nabla f(x_{k+1})-\nabla f(x_k),v_{k+1}\rangle.
$$

Combining `hraw`, `hfricInterior`, and `hcross_lower` yields the squared contraction inequality `hsq_contract`:

$$
\bigl(1+\beta hL+2h(\gamma-\beta L)\bigr)\|d_{k+1}\|^2
\le
(1+\beta hL)\|d_k\|^2.
$$

The proof then proves $\gamma-\beta L>0$ in `hgap`: if $L=0$, this follows from $\gamma>0$; if $L>0$, the lower bound on $\gamma$ and $h,\beta>0$ force $\beta L<L(h/2+\beta)\le\gamma$. Hence

$$
B=1+\beta hL>0,\qquad
A=1+\beta hL+2h(\gamma-\beta L)>0.
$$

The cited lemma `ipahdd_q_sq_mul_A_eq_B_local` is then applied to give

$$
q^2\bigl(1+\beta hL+2h(\gamma-\beta L)\bigr)=1+\beta hL.
$$

This is `hq_sq`. Using it in the squared contraction inequality gives

$$
\|d_{k+1}\|\le q\|d_k\|.
$$

So the consecutive differences contract geometrically.

By induction, `hgeom` proves

$$
\|d_{k_0+n}\|\le q^n\|d_{k_0}\|.
$$

The cited lemma `geometric_range_sum_le_local` states that for $0\le q<1$,

$$
\sum_{i=0}^{p-1}q^{n+i}\le \frac{q^n}{1-q}.
$$

This is used as `hsum`. The proof then proves the telescoping identity

$$
x_{k_0+n+p}-x_{k_0+n}
=\sum_{i=0}^{p-1}d_{k_0+n+i}
$$

as `htel`. Taking norms, applying the triangle inequality for sums, and using the geometric bound and `hsum`, the proof obtains the tail estimate

$$
\|x_{k_0+n}-x_{k_0+n+p}\|
\le
\frac{q^n}{1-q}\|d_{k_0}\|.
$$

Letting $p\to\infty$ and using $x_k\to x_\infty$ replaces $x_{k_0+n+p}$ by $x_\infty$. Thus

$$
\|x_{k_0+n}-x_\infty\|
\le
\frac{q^n}{1-q}\|d_{k_0}\|.
$$

Reindexing with $k=k_0+n$ gives exactly the two geometric inequalities required in the first implication.

For the second implication, the proof introduces `hmargin`, the hypothesis

$$
\|\nabla f(x_\infty)\|<r.
$$

It defines

$$
D=1+h\gamma,\qquad \lambda=\frac{h}{D},
$$

and

$$
z_k=
\frac{1}{hD}(x_{k+1}-x_k)
-\frac{\beta}{D}\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
-\lambda \nabla f(x_{k+1}).
$$

The proof shows $D>0$ and $\lambda>0$. Since $x_{k+1}\to x_\infty$, the differences $x_{k+1}-x_k\to0$; since $\nabla f$ is continuous, the gradient differences also tend to $0$. Therefore

$$
z_k\to \lambda\bigl(-\nabla f(x_\infty)\bigr),
$$

and hence

$$
\lambda^{-1}z_k\to -\nabla f(x_\infty).
$$

Because $\|\nabla f(x_\infty)\|<r$, eventually

$$
\|\lambda^{-1}z_k\|<r.
$$

Let $k_{\mathrm{Stop}}$ be such an index.

For every $j\ge k_{\mathrm{Stop}}$, the consequence `hdf.ball_subset` of `hdf : DF_r phi r` gives

$$
\lambda^{-1}z_j\in\partial\phi(0).
$$

Since $\lambda>0$, this means that $0$ is a proximal point of $\phi$ at $z_j$ with parameter $\lambda$, i.e.

$$
\mathrm{IsProximalPoint}(\phi,\lambda,z_j,0).
$$

The definition of `IsProximalPoint` is precisely that $0<\lambda$ and $\lambda^{-1}(z_j-0)\in\partial\phi(0)$.

On the other hand, the cited theorem `scaledProximityOperator_residual_mem` says that the true scaled proximal point

$$
p=\mathrm{Prox}_{\lambda\phi}(z_j)
$$

satisfies

$$
\lambda^{-1}\bigl(z_j-p\bigr)\in\partial\phi(p),
$$

so $p$ is also a proximal point of $\phi$ at $z_j$ with parameter $\lambda$. The cited theorem `proximal_point_eq_zero_of_subgradient_ball` then applies: if $p$ and $0$ are both proximal points for the same $\phi,\lambda,z_j$, then $p=0$. Hence

$$
\mathrm{Prox}_{\lambda\phi}(z_j)=0.
$$

Finally, the algorithm update relation `alg.update j` gives

$$
x_{j+2}=x_{j+1}+h\mathrm{Prox}_{\lambda\phi}(z_j).
$$

Since the proximal point is $0$, this reduces to

$$
x_{j+2}=x_{j+1}.
$$

Thus for every $j\ge k_{\mathrm{Stop}}$, the sequence satisfies $x_{j+2}=x_{j+1}$. Reindexing with $k=j+1$ gives

$$
x_{k+1}=x_k
$$

for all $k\ge k_{\mathrm{Stop}}+1$, which is exactly the eventual constancy stated in the second implication.

