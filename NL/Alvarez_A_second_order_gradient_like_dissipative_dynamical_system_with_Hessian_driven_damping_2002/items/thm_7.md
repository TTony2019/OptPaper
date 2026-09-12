## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_7.lean`

## Lean statement
```lean
theorem constrained_din_global_properties_part_iii {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (Φ : H → ℝ)
  (hC : ConstrainedHypothesis C Φ)
  (β a b : ℝ) (hβ : 0 < β) (ha : a ≠ 0) (hb : 0 < b) (hab : 0 < b + a)
  (x₀ y₀ : H) (x y : ℝ → H)
  (hxy : IsConstrainedDINTrajectory C Φ hC β a b x₀ y₀ x y)
  (hreg : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0)) :
    Bornology.IsBounded (x '' Set.Ici 0) →
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici 0) ∧
      Bornology.IsBounded (y '' Set.Ici 0) ∧
      Bornology.IsBounded ((deriv x) '' Set.Ici 0) ∧
      Tendsto (deriv x) atTop (nhds 0)
```

## Statement explanation
The theorem `constrained_din_global_properties_part_iii` is stated in a complete real inner product space $H$. The fixed data are a set $C\subseteq H$, a function $\Phi:H\to\mathbb R$, and a hypothesis `hC` of type `ConstrainedHypothesis C Φ`. The proof uses that this hypothesis supplies, in particular, that $C$ is nonempty, closed, and convex, that $\Phi$ is bounded below on $C$, and that $\nabla\Phi$ is Lipschitz on bounded subsets of $C$. The real parameters are $\beta,a,b$, subject to $0<\beta$, $a\neq 0$, $0<b$, and $0<b+a$.

The initial points are $x_0,y_0\in H$, and $x,y:\mathbb R\to H$ are trajectories. The hypothesis `hxy` says that $(x,y)$ is a constrained DIN trajectory for these data. From the proof, the parts of this hypothesis that are used are the initial condition $x(0)=x_0$, the membership $x_0\in C$, and, for every $t\ge 0$, the ODE relations

$$
\dot x(t)+x(t)-P\bigl(x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t)\bigr)=0,
$$

$$
\dot y(t)+a x(t)+b y(t)=0,
$$

where $P$ denotes the constrained DIN projection onto $C$. The regularity hypothesis `hreg` says that $x$ is $C^1$ on $[0,\infty)$ and $y$ is $C^2$ on $[0,\infty)$.

The conclusion is an implication. If the image $x([0,\infty))$ is bounded, then four statements hold:

- the image of $t\mapsto \nabla\Phi(x(t))$ is bounded;
- the image $y([0,\infty))$ is bounded;
- the image of $t\mapsto \dot x(t)$ is bounded;
- the derivative $\dot x(t)$ tends to $0$ as $t\to\infty$.

In ordinary mathematical language, the theorem says that for this constrained dissipative second-order system, once the position trajectory $x$ stays bounded on the nonnegative time axis, the auxiliary variable $y$, the gradient of the potential along $x$, and the velocity $\dot x$ are all bounded, and moreover the velocity decays to zero at infinity.

## Lean proof
```lean
by
  intro hxbounded
  obtain ⟨X, Y, hXY, hXreg, hYreg, hXC, hunique⟩ :=
    constrained_din_global_properties_part_i C Φ hC β a b hβ ha hb hab x₀ y₀
      hxy.2.2.2.2.2.1
  have hsame := hunique x y hxy hreg
  have hxC (t : ℝ) (ht : 0 ≤ t) : x t ∈ C := by
    rw [hsame.1 (Set.mem_Ici.mpr ht)]
    exact hXC t ht
  have heq (t : ℝ) (ht : 0 ≤ t) :
      deriv x t + x t - constrainedDINProjection C Φ hC
          (x t - β • gradient Φ (x t) - a • x t - b • y t) = 0 ∧
        deriv y t + a • x t + b • y t = 0 := by
    simpa [constrainedDINProjection] using hxy.2.2.2.2.2.2.2 t ht
  have hii := constrained_din_global_properties_part_ii C Φ hC β a b hβ ha hb hab
    x₀ y₀ x y hxy hreg
  rcases isBounded_iff_forall_norm_le.mp hxbounded with ⟨R, hR⟩
  have hxzero : x 0 = x₀ := hxy.2.2.2.2.1
  have hRnonneg : 0 ≤ R := by
    exact (norm_nonneg x₀).trans (hR x₀ ⟨0, Set.mem_Ici.mpr le_rfl, hxzero⟩)
  obtain ⟨L, hL, hgrad⟩ := hC.gradient_lipschitz_on_bounded R
  let G : ℝ := L * (2 * R) + ‖gradient Φ x₀‖
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hgradbound (t : ℝ) (ht : 0 ≤ t) : ‖gradient Φ (x t)‖ ≤ G := by
    have hxt := hR (x t) ⟨t, Set.mem_Ici.mpr ht, rfl⟩
    have hx0 := hR x₀ ⟨0, Set.mem_Ici.mpr le_rfl, hxzero⟩
    have hdiff := hgrad (x t) (hxC t ht) x₀ hxy.2.2.2.2.2.1 hxt hx0
    calc
      ‖gradient Φ (x t)‖ ≤
          ‖gradient Φ (x t) - gradient Φ x₀‖ + ‖gradient Φ x₀‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ L * ‖x t - x₀‖ + ‖gradient Φ x₀‖ := add_le_add hdiff le_rfl
      _ ≤ L * (2 * R) + ‖gradient Φ x₀‖ := by
        gcongr
        calc
          ‖x t - x₀‖ ≤ ‖x t‖ + ‖x₀‖ := norm_sub_le _ _
          _ ≤ 2 * R := by nlinarith
      _ = G := rfl
  have hgradbounded :
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici 0) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨G, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hgradbound t ht
  let lam : ℝ := β * (a + 2 * b)
  have hlam : 0 < lam := by dsimp [lam]; exact mul_pos hβ (by linarith)
  have hsb : (Real.sqrt b) ^ 2 = b := by simpa using Real.sq_sqrt hb.le
  have hsab : (Real.sqrt (b + a)) ^ 2 = b + a := by
    simpa using Real.sq_sqrt hab.le
  have hmidLow : β * (Real.sqrt b - Real.sqrt (b + a)) ^ 2 ≤ lam := by
    dsimp [lam]
    have hroot : 0 ≤ Real.sqrt b * Real.sqrt (b + a) := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hβ.le]
  have hmidHigh : lam ≤ β * (Real.sqrt b + Real.sqrt (b + a)) ^ 2 := by
    dsimp [lam]
    have hroot : 0 ≤ Real.sqrt b * Real.sqrt (b + a) := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [hβ.le]
  obtain ⟨lE, hEanti, hEbelow, hElim⟩ := hii.1 lam hmidLow hmidHigh
  obtain ⟨m, hm⟩ := hC.bounded_below
  let q : ℝ → H := fun t => a • x t + b • y t
  let E : ℝ → ℝ := fun t => constrainedEnergy Φ a b lam (x t) (y t)
  have hEzeroLower : lam * m ≤ E 0 := by
    have hp := mul_le_mul_of_nonneg_left (hm (x 0) (hxC 0 le_rfl)) hlam.le
    dsimp [E, constrainedEnergy, q]
    nlinarith [sq_nonneg ‖a • x 0 + b • y 0‖]
  let Q : ℝ := 2 * (E 0 - lam * m) + 1
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hqbound (t : ℝ) (ht : 0 ≤ t) : ‖q t‖ ≤ Q := by
    have hanti := hEanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    have hphi := hm (x t) (hxC t ht)
    have hphis := mul_le_mul_of_nonneg_left hphi hlam.le
    have hsq : ‖q t‖ ^ 2 ≤ 2 * (E 0 - lam * m) := by
      dsimp [E, constrainedEnergy, q] at hanti ⊢
      nlinarith
    dsimp [Q]
    nlinarith [sq_nonneg (‖q t‖ - 1 / 2), norm_nonneg (q t)]
  let Ry : ℝ := |b|⁻¹ * (Q + |a| * R)
  have hRy : 0 ≤ Ry := by dsimp [Ry]; positivity
  have hybound (t : ℝ) (ht : 0 ≤ t) : ‖y t‖ ≤ Ry := by
    have hby : b • y t = q t - a • x t := by dsimp [q]; module
    calc
      ‖y t‖ = |b|⁻¹ * ‖b • y t‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        field_simp [abs_ne_zero.mpr hb.ne']
      _ = |b|⁻¹ * ‖q t - a • x t‖ := by rw [hby]
      _ ≤ |b|⁻¹ * (‖q t‖ + |a| * ‖x t‖) := by
        gcongr
        simpa [norm_smul, Real.norm_eq_abs] using norm_sub_le (q t) (a • x t)
      _ ≤ |b|⁻¹ * (Q + |a| * R) := by
        gcongr
        · exact hqbound t ht
        · exact hR (x t) ⟨t, Set.mem_Ici.mpr ht, rfl⟩
      _ = Ry := rfl
  have hybounded : Bornology.IsBounded (y '' Set.Ici 0) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Ry, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hybound t ht
  let V : ℝ := |β| * G + Q
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hdxbound (t : ℝ) (ht : 0 ≤ t) : ‖deriv x t‖ ≤ V := by
    let P := constrainedDINProjection C Φ hC
    let z : H := x t - β • gradient Φ (x t) - a • x t - b • y t
    have hPx : P (x t) = x t := constrainedDINProjection_eq_self C Φ hC (hxC t ht)
    have hform : deriv x t = P z - x t := by
      have hp : P z = deriv x t + x t := (sub_eq_zero.mp (heq t ht).1).symm
      rw [hp]
      module
    rw [hform, ← hPx]
    calc
      ‖P z - P (x t)‖ ≤ ‖z - x t‖ := by
        simpa using (constrainedDINProjection_lipschitz C Φ hC).norm_sub_le z (x t)
      _ = ‖-β • gradient Φ (x t) - q t‖ := by
        congr 1
        dsimp [z, q]
        module
      _ ≤ ‖-β • gradient Φ (x t)‖ + ‖q t‖ := norm_sub_le _ _
      _ ≤ |β| * G + Q := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        gcongr
        · exact hgradbound t ht
        · exact hqbound t ht
      _ = V := rfl
  have hdxbounded : Bornology.IsBounded ((deriv x) '' Set.Ici 0) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨V, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hdxbound t ht
  have hdybound (t : ℝ) (ht : 0 ≤ t) : ‖deriv y t‖ ≤ Q := by
    have hneg : deriv y t = -q t := by
      dsimp [q]
      exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using (heq t ht).2)
    rw [hneg, norm_neg]
    exact hqbound t ht
  let F := constrainedDINPhaseField C Φ hC β a b
  let Z : ℝ → H × H := fun t => (x t, y t)
  have hfield (t : ℝ) (ht : 0 ≤ t) : F (Z t) = (deriv x t, deriv y t) := by
    apply Prod.ext
    · dsimp [F, Z, constrainedDINPhaseField]
      rw [constrainedDINProjection_eq_self C Φ hC (hxC t ht)]
      symm
      apply eq_sub_of_add_eq
      exact sub_eq_zero.mp (heq t ht).1
    · dsimp [F, Z, constrainedDINPhaseField]
      have hneg : deriv y t = -(a • x t + b • y t) :=
        eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using (heq t ht).2)
      rw [hneg]
      module
  have hxd (t : ℝ) (ht : 0 < t) : HasDerivAt x (deriv x t) t :=
    (hreg.1.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hyd (t : ℝ) (ht : 0 < t) : HasDerivAt y (deriv y t) t :=
    (hreg.2.differentiableOn (by norm_num) t ht.le).differentiableAt
      (Ici_mem_nhds ht) |>.hasDerivAt
  have hZode (t : ℝ) (ht : 0 < t) : HasDerivAt Z (F (Z t)) t := by
    have hp := (hxd t ht).prodMk (hyd t ht)
    convert hp using 1
    exact hfield t ht.le
  have hZC1 : ContDiffOn ℝ 1 Z (Set.Ici 0) :=
    hreg.1.prodMk (hreg.2.of_le (by norm_num))
  have hFcont : Continuous F :=
    (constrainedDINPhaseField_locallyLipschitz C Φ hC β a b).continuous
  have hFZcont : ContinuousOn (fun t => F (Z t)) (Set.Ici 0) :=
    hFcont.comp_continuousOn hZC1.continuousOn
  have hZzero : HasDerivWithinAt Z (F (Z 0)) (Set.Ici 0) 0 :=
    constrainedDIN_hasDerivWithinAt_zero_of_contDiffOn_one hZC1 hFZcont hZode
  have hxwithin (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt x (deriv x t) (Set.Ici 0) t := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
    · have hz := hZzero.hasFDerivWithinAt.fst.hasDerivWithinAt
      simpa [Z, hfield 0 le_rfl] using hz
    · exact (hxd t ht).hasDerivWithinAt
  have hywithin (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
      HasDerivWithinAt y (deriv y t) (Set.Ici 0) t := by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp ht) with rfl | ht
    · have hz := hZzero.hasFDerivWithinAt.snd.hasDerivWithinAt
      simpa [Z, hfield 0 le_rfl] using hz
    · exact (hyd t ht).hasDerivWithinAt
  let KV : NNReal := ⟨V, hV⟩
  let KQ : NNReal := ⟨Q, hQ.le⟩
  have hxLip : LipschitzOnWith KV x (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hxwithin
    intro t ht
    apply NNReal.coe_le_coe.mpr
    simpa [KV] using hdxbound t ht
  have hyLip : LipschitzOnWith KQ y (Set.Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hywithin
    intro t ht
    apply NNReal.coe_le_coe.mpr
    simpa [KQ] using hdybound t ht
  let arg : ℝ → H := fun t =>
    x t - β • gradient Φ (x t) - a • x t - b • y t
  have hvel (t : ℝ) (ht : 0 ≤ t) :
      deriv x t = constrainedDINProjection C Φ hC (arg t) - x t := by
    have hp : constrainedDINProjection C Φ hC (arg t) = deriv x t + x t := by
      exact (sub_eq_zero.mp (heq t ht).1).symm
    rw [hp]
    module
  let Kvel : ℝ := (1 + |β| * L + |a|) * V + |b| * Q + V
  have hKvel : 0 ≤ Kvel := by dsimp [Kvel]; positivity
  have hvelLip : LipschitzOnWith (Real.toNNReal Kvel) (deriv x) (Set.Ici 0) := by
    apply LipschitzOnWith.of_dist_le'
    intro s hs t ht
    have hxs : ‖x s‖ ≤ R := hR (x s) ⟨s, hs, rfl⟩
    have hxt : ‖x t‖ ≤ R := hR (x t) ⟨t, ht, rfl⟩
    have hxdiff : ‖x s - x t‖ ≤ V * ‖s - t‖ := by
      simpa [dist_eq_norm, KV] using hxLip.dist_le_mul s hs t ht
    have hxdiff' : ‖x s - x t‖ ≤ ‖s - t‖ * V := by
      simpa [mul_comm] using hxdiff
    have hydiff : ‖y s - y t‖ ≤ Q * ‖s - t‖ := by
      simpa [dist_eq_norm, KQ] using hyLip.dist_le_mul s hs t ht
    have hydiff' : ‖y s - y t‖ ≤ ‖s - t‖ * Q := by
      simpa [mul_comm] using hydiff
    have hgdiff : ‖gradient Φ (x s) - gradient Φ (x t)‖ ≤
        L * (V * ‖s - t‖) :=
      (hgrad (x s) (hxC s hs) (x t) (hxC t ht) hxs hxt).trans
        (mul_le_mul_of_nonneg_left hxdiff hL)
    have hargdiff : ‖arg s - arg t‖ ≤
        ((1 + |β| * L + |a|) * V + |b| * Q) * ‖s - t‖ := by
      calc
        ‖arg s - arg t‖ = ‖(x s - x t) -
            β • (gradient Φ (x s) - gradient Φ (x t)) -
            a • (x s - x t) - b • (y s - y t)‖ := by
          congr 1
          dsimp [arg]
          module
        _ ≤ ‖x s - x t‖ + |β| * ‖gradient Φ (x s) - gradient Φ (x t)‖ +
            |a| * ‖x s - x t‖ + |b| * ‖y s - y t‖ := by
          calc
            _ ≤ ‖(x s - x t) - β • (gradient Φ (x s) - gradient Φ (x t)) -
                a • (x s - x t)‖ + ‖b • (y s - y t)‖ := norm_sub_le _ _
            _ ≤ (‖(x s - x t) - β • (gradient Φ (x s) - gradient Φ (x t))‖ +
                ‖a • (x s - x t)‖) + ‖b • (y s - y t)‖ := by gcongr; apply norm_sub_le
            _ ≤ ((‖x s - x t‖ + ‖β • (gradient Φ (x s) - gradient Φ (x t))‖) +
                ‖a • (x s - x t)‖) + ‖b • (y s - y t)‖ := by gcongr; apply norm_sub_le
            _ = _ := by simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖s - t‖ * V + |β| * (L * (V * ‖s - t‖)) +
            |a| * (V * ‖s - t‖) + |b| * (Q * ‖s - t‖) := by
          gcongr
        _ = ((1 + |β| * L + |a|) * V + |b| * Q) * ‖s - t‖ := by ring
    rw [dist_eq_norm, hvel s hs, hvel t ht]
    calc
      ‖(constrainedDINProjection C Φ hC (arg s) - x s) -
          (constrainedDINProjection C Φ hC (arg t) - x t)‖ ≤
          ‖constrainedDINProjection C Φ hC (arg s) -
            constrainedDINProjection C Φ hC (arg t)‖ + ‖x s - x t‖ := by
        rw [show
          (constrainedDINProjection C Φ hC (arg s) - x s) -
              (constrainedDINProjection C Φ hC (arg t) - x t) =
            (constrainedDINProjection C Φ hC (arg s) -
              constrainedDINProjection C Φ hC (arg t)) - (x s - x t) by
          module]
        exact norm_sub_le _ _
      _ ≤ ‖arg s - arg t‖ + ‖x s - x t‖ := by
        gcongr
        simpa using
          (constrainedDINProjection_lipschitz C Φ hC).norm_sub_le (arg s) (arg t)
      _ ≤ (((1 + |β| * L + |a|) * V + |b| * Q) * ‖s - t‖) +
          V * ‖s - t‖ := add_le_add hargdiff hxdiff
      _ = Kvel * dist s t := by
        dsimp [Kvel]
        rw [dist_eq_norm, Real.norm_eq_abs]
        ring
  have hdxuc : UniformContinuousOn (deriv x) (Set.Ici 0) := hvelLip.uniformContinuousOn
  have hdxintIoi : MeasureTheory.IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ioi 0) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hii.2.1.aestronglyMeasurable).mp hii.2.1
  have hdxintIci : MeasureTheory.IntegrableOn (fun t => ‖deriv x t‖ ^ 2) (Set.Ici 0) := by
    rwa [integrableOn_Ici_iff_integrableOn_Ioi]
  have hdxzero : Tendsto (deriv x) atTop (nhds 0) :=
    constrainedDIN_uniformContinuousOn_sq_integrable_tendsto_zero _ hdxuc hdxintIci
  exact ⟨hgradbounded, hybounded, hdxbounded, hdxzero⟩
```

## Proof explanation
The proof starts with `intro hxbounded`, which introduces the assumption that the image $x([0,\infty))$ is bounded. The boundedness is then converted, using `isBounded_iff_forall_norm_le.mp`, into the existence of a real number $R$ such that every element of $x([0,\infty))$ has norm at most $R$. Thus, for every $t\ge 0$,

$$
\|x(t)\|\le R.
$$

The proof also records that $0\le R$, because $\|x_0\|\ge 0$ and $x_0=x(0)$ lies in the image.

Next, the proof applies `constrained_din_global_properties_part_i` to the given data, using as its last hypothesis the fact $x_0\in C$ extracted from `hxy`. That theorem provides trajectories $X,Y$ which satisfy the constrained trajectory equations, are $C^1$ and $C^2$ respectively on $[0,\infty)$, satisfy $X(t)\in C$ for all $t\ge 0$, and are unique among trajectories with the same regularity. Since the given pair $(x,y)$ also satisfies the trajectory and regularity assumptions, the uniqueness clause gives

$$
x(t)=X(t),\qquad y(t)=Y(t)
$$

for all $t\ge 0$. Consequently $x(t)\in C$ for every $t\ge 0$. This membership is used repeatedly later, in particular so that the projection fixes $x(t)$ and so that the gradient-Lipschitz estimate on $C$ can be applied to points $x(t)$.

The proof then extracts the ODE identities. For every $t\ge 0$, after unfolding the definition of `constrainedDINProjection`, it gets

$$
\dot x(t)+x(t)-P\bigl(x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t)\bigr)=0,
$$

$$
\dot y(t)+a x(t)+b y(t)=0.
$$

These equations are the source of the later representations of $\dot x$ and $\dot y$.

The main quantitative input is `constrained_din_global_properties_part_ii`. The proof chooses

$$
\lambda=\beta(a+2b).
$$

Because $0<\beta$ and $0<b+a$, one has $a+2b=(a+b)+b>0$, hence $\lambda>0$. The proof then verifies that $\lambda$ lies in the interval required by part ii:

$$
\beta(\sqrt b-\sqrt{b+a})^2\le \lambda\le \beta(\sqrt b+\sqrt{b+a})^2.
$$

Indeed, $(\sqrt b)^2=b$ and $(\sqrt{b+a})^2=b+a$, and the cross term $\sqrt b\sqrt{b+a}$ is nonnegative, so the inequalities reduce to simple algebraic comparisons involving $a+2b$. Applying part ii at this $\lambda$ gives that the constrained energy

$$
E(t)=\lambda \Phi(x(t))+\frac12\|a x(t)+b y(t)\|^2
$$

is antitone on $[0,\infty)$, bounded below, and convergent. It also gives that $\dot x$ is square-integrable on $(0,\infty)$. The proof uses the antitonicity and the square-integrability of $\dot x$; the other clauses of part ii are not needed for the final conclusion.

To bound $y$, the proof first bounds

$$
q(t)=a x(t)+b y(t).
$$

From `hC.bounded_below`, there is a real number $m$ such that $m\le \Phi(z)$ for all $z\in C$. Since $x(t)\in C$, this gives $m\le \Phi(x(t))$. The energy satisfies

$$
E(t)=\lambda\Phi(x(t))+\frac12\|q(t)\|^2.
$$

Because $E$ is antitone and $t\ge 0$, one has $E(t)\le E(0)$. Since $\lambda\ge 0$, the lower bound $\Phi(x(t))\ge m$ yields

$$
\lambda m+\frac12\|q(t)\|^2\le E(0).
$$

Thus

$$
\|q(t)\|^2\le 2(E(0)-\lambda m).
$$

The proof defines

$$
Q=2(E(0)-\lambda m)+1>0.
$$

The displayed inequality implies $\|q(t)\|\le Q$ for all $t\ge 0$. The use of `nlinarith` here is to turn the quadratic estimate on $\|q(t)\|^2$ into a linear bound on $\|q(t)\|$.

Once $q$ is bounded, $y$ is bounded as follows. Since

$$
b y(t)=q(t)-a x(t),
$$

and $b\neq 0$, one has

$$
\|y(t)\|=\frac1{|b|}\|b y(t)\|
=\frac1{|b|}\|q(t)-a x(t)\|
\le \frac1{|b|}\bigl(\|q(t)\|+|a|\|x(t)\|\bigr).
$$

Using $\|q(t)\|\le Q$ and $\|x(t)\|\le R$, the proof obtains

$$
\|y(t)\|\le |b|^{-1}(Q+|a|R).
$$

This proves boundedness of $y([0,\infty))$.

The proof next bounds $\nabla\Phi(x(t))$. From `hC.gradient_lipschitz_on_bounded R`, there is a constant $L$ such that for all $u,v\in C$ with $\|u\|,\|v\|\le R$,

$$
\|\nabla\Phi(u)-\nabla\Phi(v)\|\le L\|u-v\|.
$$

For $t\ge 0$, both $x(t)$ and $x_0$ lie in $C$, and both have norm at most $R$. Therefore

$$
\|\nabla\Phi(x(t))-\nabla\Phi(x_0)\|
\le L\|x(t)-x_0\|.
$$

Using the triangle inequality,

$$
\|x(t)-x_0\|\le \|x(t)\|+\|x_0\|\le 2R.
$$

Hence

$$
\|\nabla\Phi(x(t))\|
\le \|\nabla\Phi(x(t))-\nabla\Phi(x_0)\|+\|\nabla\Phi(x_0)\|
\le L(2R)+\|\nabla\Phi(x_0)\|.
$$

The proof defines this last quantity as $G$, so $\|\nabla\Phi(x(t))\|\le G$. This gives boundedness of the gradient image.

The velocity $\dot x$ is bounded by combining the projection and the ODE. Let

$$
z(t)=x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t).
$$

From the first ODE identity,

$$
P(z(t))=\dot x(t)+x(t),
$$

so

$$
\dot x(t)=P(z(t))-x(t).
$$

Since $x(t)\in C$, the projection fixes $x(t)$: $P(x(t))=x(t)$. Therefore

$$
\dot x(t)=P(z(t))-P(x(t)).
$$

The projection is $1$-Lipschitz, so

$$
\|\dot x(t)\|\le \|z(t)-x(t)\|.
$$

But

$$
z(t)-x(t)=-\beta\nabla\Phi(x(t))-q(t).
$$

Thus

$$
\|\dot x(t)\|
\le \|-\beta\nabla\Phi(x(t))\|+\|q(t)\|
\le |\beta|G+Q.
$$

The proof defines $V=|\beta|G+Q$, so $\|\dot x(t)\|\le V$ for all $t\ge 0$. This proves boundedness of $(\dot x)([0,\infty))$. Similarly, the second ODE identity gives

$$
\dot y(t)=-q(t),
$$

so $\|\dot y(t)\|\le Q$.

The proof then prepares to apply the uniform-continuity-and-square-integrability lemma to $\dot x$. It defines the phase-field map

$$
F(u,v)=\bigl(P(u-\beta\nabla\Phi(Pu)-a u-b v)-u,\,-a u-b v\bigr)
$$

through `constrainedDINPhaseField`, and the curve

$$
Z(t)=(x(t),y(t)).
$$

For $t\ge 0$, the ODE identities imply

$$
F(Z(t))=(\dot x(t),\dot y(t)).
$$

The theorem `constrainedDINPhaseField_locallyLipschitz` says that $F$ is locally Lipschitz, hence continuous. Since $x$ is $C^1$ and $y$ is $C^2$, the curve $Z$ is $C^1$ on $[0,\infty)$. For $t>0$, the ordinary derivatives of $x$ and $y$ give

$$
Z'(t)=F(Z(t)).
$$

The auxiliary lemma `constrainedDIN_hasDerivWithinAt_zero_of_contDiffOn_one` is then applied to the curve $Z$, whose derivative at positive times is the continuous function $t\mapsto F(Z(t))$. It yields that $Z$ has right derivative $F(Z(0))$ at $0$ within $[0,\infty)$. Taking components gives right derivatives for $x$ and $y$ at every $t\ge 0$.

Using these right derivatives and the bounds $\|\dot x(t)\|\le V$ and $\|\dot y(t)\|\le Q$, the proof applies the standard fact that a function with derivative bounded by a constant on a convex set is Lipschitz with that constant. Hence

$$
x\text{ is }V\text{-Lipschitz on } [0,\infty),\qquad
y\text{ is }Q\text{-Lipschitz on } [0,\infty).
$$

Concretely,

$$
\|x(s)-x(t)\|\le V|s-t|,\qquad
\|y(s)-y(t)\|\le Q|s-t|.
$$

The proof then shows that $\dot x$ itself is Lipschitz on $[0,\infty)$. Define

$$
\arg(t)=x(t)-\beta\nabla\Phi(x(t))-a x(t)-b y(t).
$$

Then

$$
\dot x(t)=P(\arg(t))-x(t).
$$

For $s,t\ge 0$, the Lipschitz bounds for $x$ and $y$, together with the gradient-Lipschitz estimate, give

$$
\|\nabla\Phi(x(s))-\nabla\Phi(x(t))\|\le L V|s-t|.
$$

Expanding the difference of $\arg(s)$ and $\arg(t)$ and using the triangle inequality yields

$$
\|\arg(s)-\arg(t)\|
\le \bigl((1+|\beta|L+|a|)V+|b|Q\bigr)|s-t|.
$$

Since $P$ is $1$-Lipschitz,

$$
\|\dot x(s)-\dot x(t)\|
\le \|\arg(s)-\arg(t)\|+\|x(s)-x(t)\|.
$$

Therefore

$$
\|\dot x(s)-\dot x(t)\|\le K_{\mathrm{vel}}|s-t|,
$$

where

$$
K_{\mathrm{vel}}=(1+|\beta|L+|a|)V+|b|Q+V.
$$

Thus $\dot x$ is Lipschitz on $[0,\infty)$, hence uniformly continuous there.

Finally, part ii supplied that $\dot x$ is square-integrable on $(0,\infty)$, i.e.

$$
\int_0^\infty \|\dot x(t)\|^2\,dt<\infty.
$$

In Lean this is expressed as

$$
\mathrm{MemLp}(\dot x,2,\text{volume restricted to }(0,\infty)).
$$

The equivalence `memLp_two_iff_integrable_sq_norm` converts this into integrability of $t\mapsto\|\dot x(t)\|^2$ on $(0,\infty)$. Since the single point $0$ has measure zero, `integrableOn_Ici_iff_integrableOn_Ioi` upgrades this to integrability on $[0,\infty)$. The lemma `constrainedDIN_uniformContinuousOn_sq_integrable_tendsto_zero` then applies: a function that is uniformly continuous on $[0,\infty)$ and whose squared norm is integrable on $[0,\infty)$ must tend to $0$ at infinity. Hence

$$
\dot x(t)\to 0\qquad (t\to\infty).
$$

Combining the boundedness of the gradient image, the boundedness of $y$, the boundedness of $\dot x$, and the decay $\dot x(t)\to 0$ gives exactly the four conjuncts in the theorem’s conclusion.

