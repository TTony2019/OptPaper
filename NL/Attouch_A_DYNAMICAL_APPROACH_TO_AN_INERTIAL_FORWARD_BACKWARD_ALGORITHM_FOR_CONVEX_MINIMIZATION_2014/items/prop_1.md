## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_1.lean`

## Lean statement
```lean
theorem proposition2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (Ψ : H → ℝ) (gradPsi : H → H) (a b lam L : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis Φ Θ Ψ gradPsi a b lam L) (hIFB : IsIFBTrajectory Φ Ψ gradPsi a b lam u y) :
    (∀ k : ℕ,
      mechanicalEnergy Θ u (gamma a b lam) (k + 2) (by omega) ≤
        mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega)) ∧
    Summable (fun k : ℕ ↦ ‖u (k + 1) - u k‖ ^ 2) ∧
    ∃ e : EReal,
      Filter.Tendsto
        (fun k : ℕ ↦ mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega))
        Filter.atTop (nhds e) ∧
      Filter.Tendsto (fun k : ℕ ↦ Θ (u (k + 1))) Filter.atTop (nhds e)
```

## Statement explanation
The declaration `proposition2` is a convergence and descent theorem for an inertial forward-backward trajectory. The ambient space is a real inner product space $H$, equipped with its norm and additive group structure. The data are two extended-real-valued functions $\Phi,\Theta:H\to \mathrm{EReal}$, a real-valued function $\Psi:H\to \mathbb R$, a map $\operatorname{grad}\Psi:H\to H$, real parameters $a,b,\lambda,L$, and two sequences $u,y:\mathbb N\to H$, representing the trajectory and an auxiliary variable. The hypothesis `hH` is an `IFBHypothesis`; the proof uses from it that $b>0$, that the step size $\lambda$ is positive/nonzero, that $\Psi$ is differentiable, that its Fréchet derivative is represented by $\operatorname{grad}\Psi$,

$$
\operatorname{fderiv}_{\mathbb R}\Psi(x)(h)=\langle \operatorname{grad}\Psi(x),h\rangle,
$$

that $\operatorname{grad}\Psi$ is $L$-Lipschitz,

$$
\|\operatorname{grad}\Psi(x)-\operatorname{grad}\Psi(y)\|\le L\|x-y\|,
$$

that $\Theta=\Phi+\Psi$ as extended-real functions, and that $\Theta$ is bounded below by a real constant. The hypothesis `hIFB` supplies the forward-backward update equations. In the form used in the proof, for every $k$ there exists $g\in\partial\Phi(u_{k+2})$ such that

$$
\frac1\lambda(u_{k+2}-u_{k+1})+g+a u_{k+1}-b y_{k+1}=0,
$$

and also

$$
\frac1\lambda(y_{k+1}-y_k)+\operatorname{grad}\Psi(u_{k+1})-a u_{k+1}+b y_{k+1}=0.
$$

The subdifferential is the standard one,

$$
\partial\Phi(x)=\{g\mid \forall z,\ \langle z-x,g\rangle+\Phi(x)\le \Phi(z)\},
$$

with the inequality taken in $\mathrm{EReal}$.

The constant

$$
\gamma(a,b,\lambda)=\frac{1-a\lambda}{2b\lambda^2}
$$

is used to form the mechanical energy

$$
\mathcal E_n=\Theta(u_n)+\gamma(a,b,\lambda)\|u_n-u_{n-1}\|^2,\qquad n\ge 1.
$$

The conclusion has three parts. First, the mechanical energies are nonincreasing along the trajectory:

$$
\forall k\in\mathbb N,\qquad \mathcal E_{k+2}\le \mathcal E_{k+1}.
$$

Second, the squared consecutive differences are summable:

$$
\sum_{k=0}^{\infty}\|u_{k+1}-u_k\|^2<\infty.
$$

Third, there exists an extended-real number $e\in \mathrm{EReal}$ such that both the mechanical energy sequence and the potential sequence converge to $e$:

$$
\mathcal E_{k+1}\longrightarrow e,\qquad \Theta(u_{k+1})\longrightarrow e
$$

as $k\to\infty$. In ordinary language, under the inertial forward-backward hypotheses and trajectory assumptions, the energy decreases, the discrete velocities are square-summable, and the energy and the $\Theta$-term have the same extended-real limit.

## Lean proof
```lean
by
  have hbeta : 0 < 1 / lam - L / 2 + 1 / (b * lam ^ 2) - 2 * gamma a b lam :=
    proposition2_beta_pos Φ Θ Ψ gradPsi a b lam L hH
  have hgamma : 0 < gamma a b lam := gamma_pos Φ Θ Ψ gradPsi a b lam L hH
  have hfirst (k : ℕ) :
      ∃ g ∈ subdifferential Φ (u (k + 2)),
        (1 / lam) • (u (k + 2) - u (k + 1)) + g + a • u (k + 1) - b • y (k + 1) = 0 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIFB.first_update (k + 1)
  have hsecond (k : ℕ) :
      (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) - a • u (k + 1) +
          b • y (k + 1) = 0 :=
    hIFB.second_update k
  have hfinite (n : ℕ) :
      Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥ ∧ Θ (u (n + 1)) ≠ ⊤ ∧
        Θ (u (n + 1)) ≠ ⊥ :=
    trajectory_phi_theta_finite Φ Θ Ψ gradPsi a b lam L u y hH hIFB n
  have hsub (k : ℕ) :
      ∃ g, g ∈ subdifferential Φ (u (k + 2)) ∧
        (1 / lam) • (u (k + 2) - u (k + 1)) + g + a • u (k + 1) -
            b • y (k + 1) = 0 := by
    obtain ⟨g, hg, hu⟩ := hfirst k
    exact ⟨g, hg, hu⟩
  have h35 (k : ℕ) :
      (Φ (u (k + 2))).toReal - (Φ (u (k + 1))).toReal +
          (1 / lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 +
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1)) ≤ 0 := by
    obtain ⟨g, hg, hu⟩ := hsub k
    have hs : Φ (u (k + 2)) + (inner ℝ g (u (k + 1) - u (k + 2)) : EReal) ≤
        Φ (u (k + 1)) := by
      simpa [real_inner_comm, add_comm] using hg (u (k + 1))
    have hleftbot : Φ (u (k + 2)) +
        (inner ℝ g (u (k + 1) - u (k + 2)) : ℝ) ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨(hfinite (k + 1)).2.1, EReal.coe_ne_bot _⟩
    have hsr := EReal.toReal_le_toReal hs hleftbot (hfinite k).1
    rw [EReal.toReal_add (hfinite (k + 1)).1 (hfinite (k + 1)).2.1
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hsr
    have hg_eq : g = - ((1 / lam) • (u (k + 2) - u (k + 1)) +
        a • u (k + 1) - b • y (k + 1)) := by
      apply eq_neg_of_add_eq_zero_left
      calc
        g + ((1 / lam) • (u (k + 2) - u (k + 1)) + a • u (k + 1) -
            b • y (k + 1)) =
            (1 / lam) • (u (k + 2) - u (k + 1)) + g + a • u (k + 1) -
              b • y (k + 1) := by abel
        _ = 0 := hu
    rw [hg_eq] at hsr
    have hinner : inner ℝ (- ((1 / lam) • (u (k + 2) - u (k + 1)) +
        a • u (k + 1) - b • y (k + 1))) (u (k + 1) - u (k + 2)) =
        (1 / lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 +
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1)) := by
      rw [show u (k + 1) - u (k + 2) = -(u (k + 2) - u (k + 1)) by abel]
      simp only [inner_neg_left, inner_neg_right, neg_neg]
      rw [inner_sub_left, inner_add_left, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      rw [add_sub_assoc, ← inner_sub_left]
    rw [hinner] at hsr
    norm_num at hsr
    have hsr' : (Φ (u (k + 2))).toReal +
        ((1 / lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 +
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1))) ≤ (Φ (u (k + 1))).toReal := by
      simpa [Nat.add_assoc] using hsr
    linarith
  have h36 (k : ℕ) :
      Ψ (u (k + 2)) - Ψ (u (k + 1)) - (L / 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
          inner ℝ (a • u (k + 1) - b • y (k + 1))
            (u (k + 2) - u (k + 1)) ≤
        -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) := by
    have hd := descent_lemma Ψ gradPsi L hH.psi_differentiable hH.psi_gradient
      hH.psi_lipschitz (u (k + 1)) (u (k + 2))
    have hg : gradPsi (u (k + 1)) = a • u (k + 1) - b • y (k + 1) -
        (1 / lam) • (y (k + 1) - y k) := by
      have hz : gradPsi (u (k + 1)) +
          ((1 / lam) • (y (k + 1) - y k) - a • u (k + 1) + b • y (k + 1)) = 0 := by
        calc
          gradPsi (u (k + 1)) +
              ((1 / lam) • (y (k + 1) - y k) - a • u (k + 1) + b • y (k + 1)) =
              (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) -
                a • u (k + 1) + b • y (k + 1) := by abel
          _ = 0 := hsecond k
      calc
        gradPsi (u (k + 1)) = - ((1 / lam) • (y (k + 1) - y k) -
            a • u (k + 1) + b • y (k + 1)) := eq_neg_of_add_eq_zero_left hz
        _ = a • u (k + 1) - b • y (k + 1) -
            (1 / lam) • (y (k + 1) - y k) := by abel
    rw [hg] at hd
    simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial] at hd
    have hr : inner ℝ (a • u (k + 1) - b • y (k + 1))
        (u (k + 2) - u (k + 1)) =
        a * inner ℝ (u (k + 1)) (u (k + 2) - u (k + 1)) -
          b * inner ℝ (y (k + 1)) (u (k + 2) - u (k + 1)) := by
      simp only [inner_sub_left, inner_smul_left, starRingEnd_apply, star_trivial]
    have hz : inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) =
        inner ℝ (y (k + 1)) (u (k + 2) - u (k + 1)) -
          inner ℝ (y k) (u (k + 2) - u (k + 1)) := by rw [inner_sub_left]
    rw [hr, hz]
    linarith [hd]
  have h37 (k : ℕ) :
      (Θ (u (k + 2))).toReal - (Θ (u (k + 1))).toReal +
          (1 / lam - L / 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 ≤
        -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) := by
    have ht2 : (Θ (u (k + 2))).toReal = (Φ (u (k + 2))).toReal + Ψ (u (k + 2)) := by
      rw [hH.theta_eq, EReal.toReal_add (hfinite (k + 1)).1 (hfinite (k + 1)).2.1
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    have ht1 : (Θ (u (k + 1))).toReal = (Φ (u (k + 1))).toReal + Ψ (u (k + 1)) := by
      rw [hH.theta_eq, EReal.toReal_add (hfinite k).1 (hfinite k).2.1
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      simp
    rw [ht2, ht1]
    linarith [h35 k, h36 k]
  have h38 (k : ℕ) :
      -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) +
          1 / (b * lam ^ 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
            2 * gamma a b lam * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) ≤ 0 := by
    obtain ⟨g0, hg0, hu0⟩ := hIFB.first_update k
    obtain ⟨g1, hg1, hu1⟩ := hfirst k
    have hs0 : Φ (u (k + 1)) + (inner ℝ g0 (u (k + 2) - u (k + 1)) : EReal) ≤
        Φ (u (k + 2)) := by
      simpa [real_inner_comm, add_comm] using hg0 (u (k + 2))
    have hs1 : Φ (u (k + 2)) + (inner ℝ g1 (u (k + 1) - u (k + 2)) : EReal) ≤
        Φ (u (k + 1)) := by
      simpa [real_inner_comm, add_comm] using hg1 (u (k + 1))
    have hr0 := EReal.toReal_le_toReal hs0
      (EReal.add_ne_bot_iff.mpr ⟨(hfinite k).2.1, EReal.coe_ne_bot _⟩)
      (hfinite (k + 1)).1
    have hr1 := EReal.toReal_le_toReal hs1
      (EReal.add_ne_bot_iff.mpr ⟨(hfinite (k + 1)).2.1, EReal.coe_ne_bot _⟩)
      (hfinite k).1
    rw [EReal.toReal_add (hfinite k).1 (hfinite k).2.1
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hr0
    rw [EReal.toReal_add (hfinite (k + 1)).1 (hfinite (k + 1)).2.1
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hr1
    have hmono : inner ℝ (g0 - g1) (u (k + 2) - u (k + 1)) ≤ 0 := by
      norm_num at hr0 hr1
      rw [show u (k + 1) - u (k + 2) =
        -(u (k + 2) - u (k + 1)) by abel, inner_neg_right] at hr1
      rw [inner_sub_left]
      linarith
    have hg0 : g0 = - ((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) := by
      apply eq_neg_of_add_eq_zero_left
      calc
        g0 + ((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) =
            (1 / lam) • (u (k + 1) - u k) + g0 + a • u k - b • y k := by abel
        _ = 0 := hu0
    have hg1 : g1 = - ((1 / lam) • (u (k + 2) - u (k + 1)) +
        a • u (k + 1) - b • y (k + 1)) := by
      apply eq_neg_of_add_eq_zero_left
      calc
        g1 + ((1 / lam) • (u (k + 2) - u (k + 1)) +
            a • u (k + 1) - b • y (k + 1)) =
            (1 / lam) • (u (k + 2) - u (k + 1)) + g1 +
              a • u (k + 1) - b • y (k + 1) := by abel
        _ = 0 := hu1
    rw [hg0, hg1] at hmono
    have hvec : -((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) -
        -((1 / lam) • (u (k + 2) - u (k + 1)) + a • u (k + 1) - b • y (k + 1)) =
        (1 / lam) • (u (k + 2) - u (k + 1)) -
          (1 / lam) • (u (k + 1) - u k) + a • (u (k + 1) - u k) -
            b • (y (k + 1) - y k) := by
      module
    rw [hvec] at hmono
    let v0 : H := u (k + 1) - u k
    let v1 : H := u (k + 2) - u (k + 1)
    let z : H := y (k + 1) - y k
    change inner ℝ ((1 / lam) • v1 - (1 / lam) • v0 + a • v0 - b • z) v1 ≤ 0 at hmono
    have hinner : inner ℝ ((1 / lam) • v1 - (1 / lam) • v0 + a • v0 - b • z) v1 =
        (1 / lam) * (‖v1‖ ^ 2 - inner ℝ v0 v1) + a * inner ℝ v0 v1 -
          b * inner ℝ z v1 := by
      rw [inner_sub_left, inner_add_left, inner_sub_left, inner_smul_left,
        inner_smul_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      ring
    rw [hinner] at hmono
    have hscalar :
        (1 / lam) * (‖u (k + 2) - u (k + 1)‖ ^ 2 -
          inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1))) +
          a * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) -
            b * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) ≤ 0 := by
      change (1 / lam) * (‖v1‖ ^ 2 - inner ℝ v0 v1) + a * inner ℝ v0 v1 -
        b * inner ℝ z v1 ≤ 0
      exact hmono
    have hcoef :
        -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) +
            1 / (b * lam ^ 2) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
              2 * gamma a b lam * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) =
          (1 / (b * lam)) *
            ((1 / lam) * (‖u (k + 2) - u (k + 1)‖ ^ 2 -
              inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1))) +
              a * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) -
                b * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1))) := by
      rw [gamma]
      field_simp [hH.b_pos.ne', hH.step_pos.ne']
      ring
    rw [hcoef]
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (one_div_pos.mpr (mul_pos hH.b_pos hH.step_pos))) hscalar
  have h39 (k : ℕ) :
      -(1 / lam) * inner ℝ (y (k + 1) - y k) (u (k + 2) - u (k + 1)) +
          (1 / (b * lam ^ 2) - gamma a b lam) * ‖u (k + 2) - u (k + 1)‖ ^ 2 -
            gamma a b lam * ‖u (k + 1) - u k‖ ^ 2 ≤ 0 := by
    have hsq : 0 ≤ ‖(u (k + 2) - u (k + 1)) - (u (k + 1) - u k)‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at hsq
    have hcross : 2 * inner ℝ (u (k + 1) - u k) (u (k + 2) - u (k + 1)) ≤
        ‖u (k + 1) - u k‖ ^ 2 + ‖u (k + 2) - u (k + 1)‖ ^ 2 := by
      rw [real_inner_comm] at hsq
      nlinarith [hsq]
    have hcross' := mul_le_mul_of_nonneg_left hcross (le_of_lt hgamma)
    linarith [h38 k]
  let E : ℕ → ℝ := fun n =>
    (mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega)).toReal
  let q : ℕ → ℝ := fun n =>
    (1 / lam - L / 2 + 1 / (b * lam ^ 2) - 2 * gamma a b lam) *
      ‖u (n + 2) - u (n + 1)‖ ^ 2
  have hq : ∀ n, 0 ≤ q n := by
    intro n
    dsimp [q]
    exact mul_nonneg (le_of_lt hbeta) (sq_nonneg _)
  have hdesc : ∀ n, E (n + 1) + q n ≤ E n := by
    intro n
    have hs := add_le_add (h37 n) (h39 n)
    dsimp [E, q, mechanicalEnergy, velocity]
    rw [← EReal.coe_mul, ← EReal.coe_mul]
    rw [EReal.toReal_add (hfinite (n + 1)).2.2.1 (hfinite (n + 1)).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    rw [EReal.toReal_add (hfinite n).2.2.1 (hfinite n).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp only [EReal.toReal_coe]
    norm_num
    ring_nf at hs ⊢
    linarith
  obtain ⟨m, hm⟩ := hH.theta_bounded_below
  have hbelow : BddBelow (Set.range E) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp [E, mechanicalEnergy, velocity]
    rw [← EReal.coe_mul]
    rw [EReal.toReal_add (hfinite n).2.2.1 (hfinite n).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp only [EReal.toReal_coe]
    have htm := EReal.toReal_le_toReal (hm (u (n + 1)))
      (EReal.coe_ne_bot _) (hfinite n).2.2.1
    norm_num at htm
    have hcorr : 0 ≤ gamma a b lam * ‖u (n + 1) - u n‖ ^ 2 :=
      mul_nonneg (le_of_lt hgamma) (sq_nonneg _)
    linarith
  obtain ⟨hanti, ⟨l, hlim⟩, hsumq⟩ := descent_summable_real E q hq hbelow hdesc
  have hsumshift : Summable (fun n : ℕ => ‖u (n + 2) - u (n + 1)‖ ^ 2) := by
    apply (summable_mul_left_iff hbeta.ne').mp
    convert hsumq using 1
  have hsum : Summable (fun k : ℕ => ‖u (k + 1) - u k‖ ^ 2) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.add_assoc] using hsumshift
  have hEfinite (n : ℕ) :
      mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega) ≠ ⊤ ∧
        mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega) ≠ ⊥ := by
    unfold mechanicalEnergy
    constructor
    · exact EReal.add_ne_top (hfinite n).2.2.1 (EReal.coe_ne_top _)
    · exact EReal.add_ne_bot_iff.mpr ⟨(hfinite n).2.2.2, EReal.coe_ne_bot _⟩
  have hEeq (n : ℕ) : mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega) =
      (E n : EReal) := by
    dsimp [E]
    exact (EReal.coe_toReal (hEfinite n).1 (hEfinite n).2).symm
  have hmonoEnergy : ∀ k : ℕ,
      mechanicalEnergy Θ u (gamma a b lam) (k + 2) (by omega) ≤
        mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega) := by
    intro k
    rw [hEeq (k + 1), hEeq k]
    exact_mod_cast hanti (Nat.le_succ k)
  have hElim : Filter.Tendsto (fun n : ℕ => (E n : EReal)) Filter.atTop (nhds (l : EReal)) :=
    (continuous_coe_real_ereal.tendsto l).comp hlim
  have henergy_lim : Filter.Tendsto
      (fun n : ℕ => mechanicalEnergy Θ u (gamma a b lam) (n + 1) (by omega))
        Filter.atTop (nhds (l : EReal)) := by
    simpa only [hEeq] using hElim
  refine ⟨hmonoEnergy, hsum, (l : EReal), henergy_lim, ?_⟩
  have hcorr_lim : Filter.Tendsto
      (fun n : ℕ => gamma a b lam * ‖u (n + 1) - u n‖ ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (Summable.tendsto_atTop_zero hsum))
  have hEform (n : ℕ) : E n = (Θ (u (n + 1))).toReal +
      gamma a b lam * ‖u (n + 1) - u n‖ ^ 2 := by
    dsimp [E, mechanicalEnergy, velocity]
    rw [← EReal.coe_mul]
    rw [EReal.toReal_add (hfinite n).2.2.1 (hfinite n).2.2.2
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp only [EReal.toReal_coe]
  have hsub_lim : Filter.Tendsto
      (fun n : ℕ => E n - gamma a b lam * ‖u (n + 1) - u n‖ ^ 2)
        Filter.atTop (nhds (l - 0)) := hlim.sub hcorr_lim
  have hthetaR : Filter.Tendsto (fun n : ℕ => (Θ (u (n + 1))).toReal)
      Filter.atTop (nhds l) := by
    rw [sub_zero] at hsub_lim
    apply hsub_lim.congr'
    filter_upwards [] with n
    rw [hEform n]
    ring
  have hthetaEL : Filter.Tendsto (fun n : ℕ => ((Θ (u (n + 1))).toReal : EReal))
      Filter.atTop (nhds (l : EReal)) :=
    (continuous_coe_real_ereal.tendsto l).comp hthetaR
  apply hthetaEL.congr'
  filter_upwards [] with n
  exact EReal.coe_toReal (hfinite n).2.2.1 (hfinite n).2.2.2
```

## Proof explanation
The proof first records two positivity facts. The result `proposition2_beta_pos` applied to the current hypothesis `hH` gives

$$
\beta:=\frac1\lambda-\frac L2+\frac1{b\lambda^2}-2\gamma(a,b,\lambda)>0.
$$

The result `gamma_pos` gives

$$
\gamma(a,b,\lambda)>0.
$$

These two constants later control the descent inequality and the summability argument.

Next the proof extracts the two update equations. From `hIFB.first_update (k+1)`, after harmless reindexing of natural numbers, it obtains for each $k$ some

$$
g\in\partial\Phi(u_{k+2})
$$

with

$$
\frac1\lambda(u_{k+2}-u_{k+1})+g+a u_{k+1}-b y_{k+1}=0.
$$

From `hIFB.second_update k` it obtains

$$
\frac1\lambda(y_{k+1}-y_k)+\operatorname{grad}\Psi(u_{k+1})-a u_{k+1}+b y_{k+1}=0.
$$

It also invokes `trajectory_phi_theta_finite`, which says that for every $n$, both $\Phi(u_{n+1})$ and $\Theta(u_{n+1})$ are neither $\top$ nor $\bot$. This finiteness is what allows all subsequent extended-real inequalities to be converted to ordinary real inequalities via $\operatorname{toReal}$, and later to be coerced back.

The first main inequality, called `h35` in the proof, comes from the subgradient inequality for $\Phi$. Since $g\in\partial\Phi(u_{k+2})$, applying the definition with $z=u_{k+1}$ gives

$$
\Phi(u_{k+2})+\langle g,u_{k+1}-u_{k+2}\rangle\le \Phi(u_{k+1}).
$$

The update equation says

$$
g=-\left(\frac1\lambda(u_{k+2}-u_{k+1})+a u_{k+1}-b y_{k+1}\right).
$$

Substituting this into the inner product and expanding, using $u_{k+1}-u_{k+2}=-(u_{k+2}-u_{k+1})$, yields

$$
\langle g,u_{k+1}-u_{k+2}\rangle
=
\frac1\lambda\|u_{k+2}-u_{k+1}\|^2
+
\left\langle a u_{k+1}-b y_{k+1},\,u_{k+2}-u_{k+1}\right\rangle.
$$

After taking real parts and rearranging, the proof obtains

$$
(\Phi(u_{k+2}))^{\operatorname{toReal}}-(\Phi(u_{k+1}))^{\operatorname{toReal}}
+\frac1\lambda\|u_{k+2}-u_{k+1}\|^2
+\left\langle a u_{k+1}-b y_{k+1},\,u_{k+2}-u_{k+1}\right\rangle\le 0.
$$

The second main inequality, `h36`, uses the descent lemma. The result `descent_lemma` states that for a differentiable $\Psi$ whose gradient $\operatorname{grad}\Psi$ has the given derivative representation and is $L$-Lipschitz, one has

$$
\Psi(v)\le \Psi(x)+\langle \operatorname{grad}\Psi(x),v-x\rangle+\frac L2\|v-x\|^2.
$$

Taking $x=u_{k+1}$ and $v=u_{k+2}$, this gives

$$
\Psi(u_{k+2})\le
\Psi(u_{k+1})+
\langle \operatorname{grad}\Psi(u_{k+1}),u_{k+2}-u_{k+1}\rangle
+\frac L2\|u_{k+2}-u_{k+1}\|^2.
$$

The second update equation rearranges to

$$
\operatorname{grad}\Psi(u_{k+1})
=
a u_{k+1}-b y_{k+1}
-\frac1\lambda(y_{k+1}-y_k).
$$

Substituting this and expanding the inner product gives

$$
\Psi(u_{k+2})-\Psi(u_{k+1})
-\frac L2\|u_{k+2}-u_{k+1}\|^2
-
\left\langle a u_{k+1}-b y_{k+1},\,u_{k+2}-u_{k+1}\right\rangle
\le
-\frac1\lambda\left\langle y_{k+1}-y_k,\,u_{k+2}-u_{k+1}\right\rangle.
$$

The proof then combines the two previous inequalities. Since $\Theta=\Phi+\Psi$, and the values are finite, one has

$$
(\Theta(u_{k+2}))^{\operatorname{toReal}}
=
(\Phi(u_{k+2}))^{\operatorname{toReal}}+\Psi(u_{k+2}),
$$

and similarly at $u_{k+1}$. Adding the $\Phi$-inequality and the $\Psi$-inequality cancels the common inner product term and gives the key energy inequality

$$
(\Theta(u_{k+2}))^{\operatorname{toReal}}-(\Theta(u_{k+1}))^{\operatorname{toReal}}
+\left(\frac1\lambda-\frac L2\right)\|u_{k+2}-u_{k+1}\|^2
\le
-\frac1\lambda\left\langle y_{k+1}-y_k,\,u_{k+2}-u_{k+1}\right\rangle.
$$

The next inequality, `h38`, uses monotonicity of the subdifferential. The proof obtains two subgradients: $g_0\in\partial\Phi(u_{k+1})$ from the first update at index $k$, and $g_1\in\partial\Phi(u_{k+2})$ from the first update at index $k+1$. Applying the subgradient inequalities at $u_{k+2}$ and $u_{k+1}$, respectively, gives

$$
\Phi(u_{k+1})+\langle g_0,u_{k+2}-u_{k+1}\rangle\le \Phi(u_{k+2}),
$$

$$
\Phi(u_{k+2})+\langle g_1,u_{k+1}-u_{k+2}\rangle\le \Phi(u_{k+1}).
$$

After taking real parts and adding, this yields the monotonicity inequality

$$
\langle g_0-g_1,u_{k+2}-u_{k+1}\rangle\le 0.
$$

The update equations express $g_0$ and $g_1$ as negatives of the corresponding forward-backward residuals. Their difference is

$$
g_0-g_1
=
\frac1\lambda(u_{k+2}-u_{k+1})
-\frac1\lambda(u_{k+1}-u_k)
+a(u_{k+1}-u_k)
-b(y_{k+1}-y_k).
$$

Writing

$$
v_0=u_{k+1}-u_k,\qquad v_1=u_{k+2}-u_{k+1},\qquad z=y_{k+1}-y_k,
$$

the monotonicity inequality becomes

$$
\left\langle
\frac1\lambda v_1-\frac1\lambda v_0+a v_0-bz,\ v_1
\right\rangle\le 0.
$$

Expanding the inner product,

$$
\frac1\lambda(\|v_1\|^2-\langle v_0,v_1\rangle)
+a\langle v_0,v_1\rangle
-b\langle z,v_1\rangle\le 0.
$$

Multiplying by the positive number $1/(b\lambda)$ and using the definition of $\gamma$ gives

$$
-\frac1\lambda\langle z,v_1\rangle
+\frac1{b\lambda^2}\|v_1\|^2
-2\gamma(a,b,\lambda)\langle v_0,v_1\rangle\le 0.
$$

The following inequality, `h39`, is obtained from the elementary fact

$$
0\le \|v_1-v_0\|^2
=
\|v_0\|^2+\|v_1\|^2-2\langle v_0,v_1\rangle,
$$

hence

$$
2\langle v_0,v_1\rangle\le \|v_0\|^2+\|v_1\|^2.
$$

Multiplying by $\gamma>0$, and combining with the preceding inequality, yields

$$
-\frac1\lambda\langle z,v_1\rangle
+\left(\frac1{b\lambda^2}-\gamma\right)\|v_1\|^2
-\gamma\|v_0\|^2\le 0.
$$

At this point the proof defines the real sequence

$$
E_n=\operatorname{toReal}\bigl(\mathcal E_{n+1}\bigr)
=
(\Theta(u_{n+1}))^{\operatorname{toReal}}
+\gamma\|u_{n+1}-u_n\|^2,
$$

and

$$
q_n=
\beta\|u_{n+2}-u_{n+1}\|^2,
$$

where

$$
\beta=\frac1\lambda-\frac L2+\frac1{b\lambda^2}-2\gamma.
$$

Since $\beta>0$, each $q_n\ge0$. Adding the two inequalities above, cancelling the common $-(1/\lambda)\langle z,v_1\rangle$ term, and rearranging gives

$$
E_{n+1}+q_n\le E_n.
$$

The proof also shows that $E$ is bounded below. Indeed, the hypothesis `hH.theta_bounded_below` gives a real constant $m$ such that $m\le \Theta(x)$ for all $x$. Since $\Theta(u_{n+1})$ is finite, this implies

$$
m\le (\Theta(u_{n+1}))^{\operatorname{toReal}},
$$

and the added term $\gamma\|u_{n+1}-u_n\|^2$ is nonnegative. Hence $E_n\ge m$ for every $n$, so the range of $E$ is bounded below.

Now the proof applies `descent_summable_real` to the real sequences $E$ and $q$. That result says that if $q_n\ge0$, $E$ is bounded below, and

$$
E_{n+1}+q_n\le E_n
$$

for all $n$, then $E$ is antitone, $E$ converges to some real limit $l$, and $q$ is summable. Thus the proof obtains

$$
E_{n+1}\le E_n,\qquad E_n\to l,\qquad \sum q_n<\infty.
$$

Since $q_n=\beta\|u_{n+2}-u_{n+1}\|^2$ and $\beta\neq0$, summability of $q$ is equivalent to summability of

$$
\|u_{n+2}-u_{n+1}\|^2.
$$

Shifting the index by one gives

$$
\sum_{k=0}^{\infty}\|u_{k+1}-u_k\|^2<\infty,
$$

which is the second conclusion of the theorem.

To recover the energy monotonicity, the proof uses that the mechanical energy values are finite. Therefore

$$
\mathcal E_{n+1}=(E_n:\mathrm{EReal}).
$$

Since $E_{k+1}\le E_k$, coercing this real inequality into $\mathrm{EReal}$ gives

$$
\mathcal E_{k+2}\le \mathcal E_{k+1}.
$$

This proves the first conclusion.

Finally, the proof identifies the common limit. From $E_n\to l$ and continuity of the coercion $\mathbb R\to\mathrm{EReal}$, one gets

$$
(E_n:\mathrm{EReal})\to(l:\mathrm{EReal}).
$$

Since $\mathcal E_{n+1}=(E_n:\mathrm{EReal})$, this gives convergence of the mechanical energies to $(l:\mathrm{EReal})$. To handle the $\Theta$-term, the proof notes that summability of $\|u_{n+1}-u_n\|^2$ implies

$$
\|u_{n+1}-u_n\|^2\to 0.
$$

Multiplying by the constant $\gamma$ gives

$$
\gamma\|u_{n+1}-u_n\|^2\to 0.
$$

But

$$
E_n=(\Theta(u_{n+1}))^{\operatorname{toReal}}
+\gamma\|u_{n+1}-u_n\|^2,
$$

so subtracting the vanishing correction term yields

$$
(\Theta(u_{n+1}))^{\operatorname{toReal}}\to l.
$$

Coercing back to $\mathrm{EReal}$, and using that $\Theta(u_{n+1})$ is finite so that

$$
\bigl((\Theta(u_{n+1}))^{\operatorname{toReal}}:\mathrm{EReal}\bigr)=\Theta(u_{n+1}),
$$

gives

$$
\Theta(u_{n+1})\to (l:\mathrm{EReal}).
$$

Thus the common extended-real limit $e=(l:\mathrm{EReal})$ satisfies both required convergence statements, completing the proof.

