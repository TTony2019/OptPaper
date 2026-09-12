## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_5.lean`

## Lean statement
```lean
theorem gdin_bounded_asymptotics
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (β a b : ℝ)
    (hΦ : ContDiff ℝ 1 Φ)
    (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x)
    (hloclip : LipschitzOnBoundedSets (gradient Φ))
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < a + b)
    (x₀ y₀ : H) (x y : ℝ → H)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y)
    (hxbounded : BoundedOnNonnegative x) :
    BoundedOnNonnegative (deriv x) ∧
      BoundedOnNonnegative (fun t => gradient Φ (x t)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0)
```

## Statement explanation
The theorem `gdin_bounded_asymptotics` is stated for a complete real inner product space $H$. It involves a function $\Phi:H\to\mathbb R$, real parameters $\beta,a,b$, initial vectors $x_0,y_0\in H$, and curves $x,y:\mathbb R\to H$. The main hypotheses are:

$$
\Phi \text{ is } C^1,\qquad
\Phi \text{ is bounded below},
$$

$$
\nabla\Phi \text{ is Lipschitz on every bounded subset of } H,
$$

and

$$
\beta>0,\qquad b>0,\qquad a+b>0.
$$

The curves satisfy that $x$ is $C^1$ on $[0,\infty)$, that $y$ is $C^2$ on $[0,\infty)$, and that the pair $(x,y)$ is a solution of the `gDIN` system with parameters $\Phi,\beta,a,b$ and initial data $x_0,y_0$. The proof uses the solution predicate through the following two consequences at each $t\ge 0$:

$$
\operatorname{deriv}x(t)+\beta\,\nabla\Phi(x(t))+a x(t)+b y(t)=0,
$$

and

$$
\operatorname{deriv}y(t)+a x(t)+b y(t)=0.
$$

Finally, the hypothesis `hxbounded` says that $x$ is bounded on $[0,\infty)$, meaning that the image $x([0,\infty))$ is a bounded subset of $H$.

The conclusion is a four-part conjunction:

$$
\operatorname{deriv}x \text{ is bounded on } [0,\infty),
$$

$$
t\mapsto \nabla\Phi(x(t)) \text{ is bounded on } [0,\infty),
$$

$$
\operatorname{deriv}x(t)\to 0 \quad \text{as } t\to\infty,
$$

and

$$
\nabla\Phi(x(t))\to 0 \quad \text{as } t\to\infty.
$$

Here boundedness on $[0,\infty)$ is expressed by `BoundedOnNonnegative`, which means that the image of $[0,\infty)$ under the given function is bounded in the norm of $H$. Thus the theorem says that both the velocity $\operatorname{deriv}x$ and the gradient term $\nabla\Phi(x(t))$ are bounded and asymptotically vanish.

## Lean proof
```lean
by
  let q : ℝ → H := fun t => a • x t + b • y t
  let v : ℝ → H := fun t => deriv x t
  let g : ℝ → H := fun t => gradient Φ (x t)
  let ell : ℝ := β * (a + 2 * b)
  have hmidlow : β * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 ≤ ell := by
    have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hp : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [ell]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    nlinarith
  have hmidhigh : ell ≤ β * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
    have hs : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt hab.le
    have hb' : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
    have hp : 0 ≤ Real.sqrt (a + b) * Real.sqrt b :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    dsimp [ell]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    nlinarith
  have hell : 0 < ell := by
    dsimp [ell]
    exact mul_pos hβ (by linarith)
  rcases (gdin_lyapunov_energy_properties Φ β a b hΦ hbounded hβ hb hab
    x₀ y₀ x y hxy hsol ell hmidlow hmidhigh).1 with hEanti
  obtain ⟨mΦ, hmΦ⟩ := hbounded
  rcases isBounded_iff_forall_norm_le.mp hxbounded with ⟨Cx, hCx⟩
  have hxnorm : ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ Cx := by
    intro t ht
    exact hCx _ ⟨t, ht, rfl⟩
  rcases hloclip (x '' Set.Ici (0 : ℝ)) hxbounded with ⟨K, hK⟩
  have hgrad_bound : ∀ t : ℝ, 0 ≤ t →
      ‖g t‖ ≤ (K : ℝ) * (Cx + ‖x 0‖) + ‖g 0‖ := by
    intro t ht
    have hKt := hK.norm_sub_le ⟨t, ht, rfl⟩ ⟨0, by simp, rfl⟩
    dsimp [g] at hKt ⊢
    calc
      ‖gradient Φ (x t)‖ = ‖gradient Φ (x t) - gradient Φ (x 0) + gradient Φ (x 0)‖ := by
        congr 1; abel
      _ ≤ ‖gradient Φ (x t) - gradient Φ (x 0)‖ + ‖gradient Φ (x 0)‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖x t - x 0‖ + ‖gradient Φ (x 0)‖ := by gcongr
      _ ≤ (K : ℝ) * (Cx + ‖x 0‖) + ‖gradient Φ (x 0)‖ := by
        gcongr
        calc ‖x t - x 0‖ ≤ ‖x t‖ + ‖x 0‖ := norm_sub_le _ _
          _ ≤ Cx + ‖x 0‖ := by
            simpa [add_comm] using add_le_add_right (hxnorm t ht) ‖x 0‖
  let Cg : ℝ := (K : ℝ) * (Cx + ‖x 0‖) + ‖g 0‖
  have hgbdd : BoundedOnNonnegative g := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max Cg 0, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact (hgrad_bound t ht).trans (le_max_left _ _)
  have hE0 : ∀ t : ℝ, 0 ≤ t →
      LyapunovEnergy Φ a b ell (x t) (y t) ≤ LyapunovEnergy Φ a b ell (x 0) (y 0) := by
    intro t ht
    exact hEanti (by simp) ht ht
  have hq_bound : ∀ t : ℝ, 0 ≤ t → ‖q t‖ ^ 2 ≤
      2 * (LyapunovEnergy Φ a b ell (x 0) (y 0) - ell * mΦ) := by
    intro t ht
    have hpot : ell * mΦ ≤ ell * Φ (x t) :=
      mul_le_mul_of_nonneg_left (hmΦ (x t)) hell.le
    have hEt := hE0 t ht
    have hkin0 : 0 ≤ (1 / 2 : ℝ) * ‖a • x 0 + b • y 0‖ ^ 2 := by positivity
    dsimp [q] at hEt ⊢
    dsimp [LyapunovEnergy] at hEt ⊢
    nlinarith
  let Cq : ℝ := max (2 * (LyapunovEnergy Φ a b ell (x 0) (y 0) - ell * mΦ)) 0
  have hqbdd : BoundedOnNonnegative q := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨Real.sqrt Cq, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hCq : 0 ≤ Cq := le_max_right _ _
    have hsq : ‖q t‖ ^ 2 ≤ Cq := (hq_bound t ht).trans (le_max_left _ _)
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hCq]
    exact hsq
  have hybdd : BoundedOnNonnegative y := by
    rcases isBounded_iff_forall_norm_le.mp hqbdd with ⟨Cq', hqC⟩
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨(1 / b) * (Cq' + |a| * Cx), ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hbne : b ≠ 0 := ne_of_gt hb
    have hy_eq : y t = (1 / b) • (q t - a • x t) := by
      dsimp [q]
      field_simp [hbne]
      simp [hbne]
    rw [hy_eq, norm_smul]
    have hqnorm := hqC _ ⟨t, ht, rfl⟩
    have hax : ‖a • x t‖ ≤ |a| * Cx := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact hxnorm t ht
    have hqsub : ‖q t - a • x t‖ ≤ Cq' + |a| * Cx := by
      calc ‖q t - a • x t‖ ≤ ‖q t‖ + ‖a • x t‖ := norm_sub_le _ _
        _ ≤ Cq' + |a| * Cx := add_le_add hqnorm hax
    have hbinv : 0 ≤ (1 / b : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hbinv]
    exact mul_le_mul_of_nonneg_left hqsub hbinv
  have hvbdd : BoundedOnNonnegative v := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨β * max Cg 0 + Real.sqrt Cq, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    have hres : v t = -(β • g t + q t) := by
      dsimp [v, g, q]
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht
    rw [hres, norm_neg]
    calc
      ‖β • g t + q t‖ ≤ ‖β • g t‖ + ‖q t‖ := norm_add_le _ _
      _ = β * ‖g t‖ + ‖q t‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      _ ≤ β * max Cg 0 + Real.sqrt Cq := by
        have hgn : ‖g t‖ ≤ max Cg 0 := (hgrad_bound t ht).trans (le_max_left _ _)
        have hqn : ‖q t‖ ≤ Real.sqrt Cq := by
          have hCq : 0 ≤ Cq := le_max_right _ _
          have hsq : ‖q t‖ ^ 2 ≤ Cq := (hq_bound t ht).trans (le_max_left _ _)
          apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
          rw [Real.sq_sqrt hCq]
          exact hsq
        exact add_le_add (mul_le_mul_of_nonneg_left hgn (le_of_lt hβ)) hqn
  rcases isBounded_iff_forall_norm_le.mp hvbdd with ⟨Cv, hCv⟩
  rcases isBounded_iff_forall_norm_le.mp hqbdd with ⟨Cq', hCq'⟩
  have hqcont : ContinuousOn q (Set.Ici (0 : ℝ)) := by
    exact (hxy.1.continuousOn.const_smul a).add (hxy.2.continuousOn.const_smul b)
  have hgcont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    exact (gdin_grad_continuous Φ hΦ).continuousOn.comp hxy.1.continuousOn
      (fun _ _ => Set.mem_univ _)
  have hv_eq (t : ℝ) (ht : 0 ≤ t) : v t = -(β • g t + q t) := by
    dsimp [v, g, q]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc, add_left_comm, add_comm] using hsol.1 t ht
  have hvcont : ContinuousOn v (Set.Ici (0 : ℝ)) := by
    apply ContinuousOn.congr ((hgcont.const_smul β).add hqcont |>.neg)
    intro t ht
    simp [hv_eq t (Set.mem_Ici.mp ht)]
  let Cvn : NNReal := ⟨max Cv 0, le_max_right _ _⟩
  have hLipx : LipschitzOnWith Cvn x (Set.Ioi (0 : ℝ)) := by
    apply (convex_Ioi 0).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (hxy.1.differentiableOn (by norm_num) t
        (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)).differentiableAt
        (Ici_mem_nhds ht)
    · intro t ht
      apply (NNReal.coe_le_coe).mp
      change ‖deriv x t‖ ≤ max Cv 0
      exact (hCv _ ⟨t, Set.mem_Ici.mpr ht.le, rfl⟩).trans (le_max_left _ _)
  let Kq : NNReal := ⟨max (|a| * max Cv 0 + b * max Cq' 0) 0,
    le_max_right _ _⟩
  have hLipq : LipschitzOnWith Kq q (Set.Ioi (0 : ℝ)) := by
    apply (convex_Ioi 0).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      have hqC1 : ContDiffOn ℝ 1 q (Set.Ici (0 : ℝ)) := by
        exact (hxy.1.const_smul a).add
          ((hxy.2.of_le (by norm_num)).const_smul b)
      exact (hqC1.differentiableOn (by norm_num) t
        (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)).differentiableAt
          (Ici_mem_nhds ht)
    · intro t ht
      have hxAt : HasDerivAt x (v t) t := by
        have hd := hxy.1.differentiableOn (by norm_num) t
          (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)
        convert (hd.differentiableAt (Ici_mem_nhds ht)).hasDerivAt using 1
      have hyAt : HasDerivAt y (deriv y t) t := by
        have hd := hxy.2.differentiableOn (by norm_num) t
          (show t ∈ Set.Ici (0 : ℝ) from Set.mem_Ici.mpr ht.le)
        exact (hd.differentiableAt (Ici_mem_nhds ht)).hasDerivAt
      have hyval : deriv y t = -q t := by
        have h : deriv y t = -(a • x t + b • y t) :=
          eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using hsol.2.1 t ht.le)
        simpa [q] using h
      have hqAt : HasDerivAt q (a • v t - b • q t) t := by
        have hraw := (hxAt.const_smul a).add (hyAt.const_smul b)
        convert hraw using 1
        rw [hyval]
        module
      rw [hqAt.deriv]
      have hvn : ‖v t‖ ≤ max Cv 0 :=
        (hCv _ ⟨t, Set.mem_Ici.mpr ht.le, rfl⟩).trans (le_max_left _ _)
      have hqn : ‖q t‖ ≤ max Cq' 0 :=
        (hCq' _ ⟨t, Set.mem_Ici.mpr ht.le, rfl⟩).trans (le_max_left _ _)
      apply (NNReal.coe_le_coe).mp
      change ‖a • v t - b • q t‖ ≤
        max (|a| * max Cv 0 + b * max Cq' 0) 0
      have hreal : ‖a • v t - b • q t‖ ≤
          max (|a| * max Cv 0 + b * max Cq' 0) 0 := by
        calc
          ‖a • v t - b • q t‖ ≤ ‖a • v t‖ + ‖b • q t‖ := norm_sub_le _ _
          _ = |a| * ‖v t‖ + |b| * ‖q t‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ |a| * max Cv 0 + b * max Cq' 0 := by
            have hbabs : |b| = b := abs_of_pos hb
            rw [hbabs]
            gcongr
          _ ≤ max (|a| * max Cv 0 + b * max Cq' 0) 0 := le_max_left _ _
      exact hreal
  have hLipg : LipschitzOnWith
      (K * ⟨max Cv 0, le_max_right _ _⟩) g (Set.Ioi (0 : ℝ)) := by
    have hc := hK.comp hLipx (fun t ht =>
      ⟨t, Set.mem_Ici.mpr (Set.mem_Ioi.mp ht).le, rfl⟩)
    simpa [Function.comp_def, g] using hc
  obtain ⟨Kβ, hLipv⟩ : ∃ Kβ : NNReal, LipschitzOnWith Kβ v (Set.Ioi (0 : ℝ)) := by
    let Lβ : H →L[ℝ] H := β • ContinuousLinearMap.id ℝ H
    have hβg : LipschitzOnWith (‖Lβ‖₊ * (K * Cvn))
        (fun t : ℝ => β • g t) (Set.Ioi (0 : ℝ)) := by
      simpa [Lβ, Function.comp_def] using
        Lβ.lipschitz.comp_lipschitzOnWith hLipg
    have hsum := hβg.add hLipq
    have hneg := hsum.neg
    refine ⟨‖Lβ‖₊ * (K * Cvn) + Kq, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have h := hneg.dist_le_mul s hs t ht
    simpa [v, hv_eq s hs.le, hv_eq t ht.le, dist_eq_norm] using h
  have hucg : UniformContinuousOn g (Set.Ici (0 : ℝ)) :=
    gdin_uniformContinuousOn_Ici_of_lipschitzOn_Ioi g hLipg hgcont
  have hucv : UniformContinuousOn v (Set.Ici (0 : ℝ)) :=
    gdin_uniformContinuousOn_Ici_of_lipschitzOn_Ioi v hLipv hvcont
  have hvL2 := gdin_x_derivative_memL2 Φ β a b hΦ ⟨mΦ, hmΦ⟩ hβ hb hab
    x₀ y₀ x y hxy hsol
  have hgL2 := gdin_gradient_memL2 Φ β a b hΦ ⟨mΦ, hmΦ⟩ hβ hb hab
    x₀ y₀ x y hxy hsol
  have hvSq : IntegrableOn (fun t => ‖v t‖ ^ 2) (Set.Ici (0 : ℝ)) := by
    exact hvL2.integrable_norm_pow (by norm_num)
  have hgSq : IntegrableOn (fun t => ‖g t‖ ^ 2) (Set.Ici (0 : ℝ)) := by
    exact hgL2.integrable_norm_pow (by norm_num)
  have hvzero : Tendsto v atTop (nhds 0) :=
    gdin_uniformContinuousOn_sq_integrable_tendsto_zero v hucv hvSq
  have hgzero : Tendsto g atTop (nhds 0) := by
    have hres := gdin_residual_limit Φ β a b hΦ ⟨mΦ, hmΦ⟩ hβ hb hab
      x₀ y₀ x y hxy hsol
    have hbg : Tendsto (fun t => β • g t) atTop (nhds 0) := by
      have hsub := hres.sub hvzero
      simpa [v, g, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hinv := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (β⁻¹ : ℝ)) atTop (nhds β⁻¹)).smul hbg
    simpa [smul_smul, ne_of_gt hβ] using hinv
  refine ⟨hvbdd, hgbdd, ?_, ?_⟩
  · simpa [v] using hvzero
  · simpa [g] using hgzero
```

## Proof explanation
The proof begins by introducing abbreviations:

$$
q(t)=a x(t)+b y(t),\qquad
v(t)=\operatorname{deriv}x(t),\qquad
g(t)=\nabla\Phi(x(t)),
$$

and the Lyapunov weight

$$
\ell=\beta(a+2b).
$$

It first checks that this $\ell$ lies in the admissible interval required by the Lyapunov energy theorem. The identities

$$
(\sqrt{a+b}\pm \sqrt b)^2
= a+2b \pm 2\sqrt{a+b}\sqrt b
$$

are used after rewriting $\sqrt{a+b}^2=a+b$ and $\sqrt b^2=b$, which is legitimate because $a+b>0$ and $b>0$. Since $\sqrt{a+b}\sqrt b\ge 0$, the quantity $a+2b$ lies between the two squared-root expressions. Multiplying by $\beta>0$ gives

$$
\beta(\sqrt{a+b}-\sqrt b)^2\le \beta(a+2b)\le \beta(\sqrt{a+b}+\sqrt b)^2.
$$

The tactic `nlinarith` closes these inequalities. Also, $\ell>0$ because $\beta>0$ and $a+2b=(a+b)+b>0$, the latter proved by `linarith`.

Next the proof applies `gdin_lyapunov_energy_properties`. Specialized to this situation, that theorem says that for every real $\ell$ satisfying

$$
\beta(\sqrt{a+b}-\sqrt b)^2\le \ell\le \beta(\sqrt{a+b}+\sqrt b)^2,
$$

the Lyapunov energy

$$
E(t)=\ell\,\Phi(x(t))+\frac12\|q(t)\|^2
=
\ell\,\Phi(x(t))+\frac12\|a x(t)+b y(t)\|^2
$$

is antitone on $[0,\infty)$, bounded below, and has a finite limit as $t\to\infty$. The proof uses only the antitone part, obtaining that for every $t\ge 0$,

$$
E(t)\le E(0).
$$

Since $\Phi$ is bounded below, there is $m_\Phi$ with $m_\Phi\le \Phi(z)$ for all $z\in H$. From the bound on $x$, using the characterization of bounded sets in a normed group, the proof obtains a constant $C_x$ such that

$$
\|x(t)\|\le C_x
$$

for all $t\ge 0$. The hypothesis `hloclip` is then applied to the bounded set $x([0,\infty))$. This gives a nonnegative Lipschitz constant $K$ for $\nabla\Phi$ on that set, so for $t\ge 0$,

$$
\|\nabla\Phi(x(t))-\nabla\Phi(x(0))\|\le K\|x(t)-x(0)\|.
$$

Using the triangle inequality,

$$
\|g(t)\|
\le \|g(t)-g(0)\|+\|g(0)\|
\le K\|x(t)-x(0)\|+\|g(0)\|
\le K(C_x+\|x(0)\|)+\|g(0)\|.
$$

Thus $g$ is bounded on $[0,\infty)$. The tactics `gcongr` and `calc` carry out the chain of norm inequalities.

The energy inequality is then used to bound $q$. Because $\ell>0$ and $m_\Phi\le \Phi(x(t))$,

$$
\ell m_\Phi+\frac12\|q(t)\|^2
\le E(t)
\le E(0).
$$

Hence

$$
\|q(t)\|^2\le 2\bigl(E(0)-\ell m_\Phi\bigr).
$$

Taking

$$
C_q=\max\bigl(2(E(0)-\ell m_\Phi),0\bigr),
$$

we get $\|q(t)\|^2\le C_q$ and therefore $\|q(t)\|\le \sqrt{C_q}$. So $q$ is bounded on $[0,\infty)$. This uses the lemma that for nonnegative real numbers $u,v$, $u^2\le v^2$ implies $u\le v$, together with $\sqrt{C_q}^2=C_q$.

From $q(t)=a x(t)+b y(t)$, the proof also derives

$$
y(t)=\frac1b\bigl(q(t)-a x(t)\bigr).
$$

The tactic `field_simp` verifies this algebraic identity using $b\ne 0$, which follows from $b>0$. Therefore,

$$
\|y(t)\|
\le \frac1b\bigl(\|q(t)\|+\|a x(t)\|\bigr)
\le \frac1b\bigl(C_q'+|a|C_x\bigr),
$$

where $C_q'$ is a norm bound for $q$. This proves $y$ is bounded on $[0,\infty)$, though the later limit argument mainly uses the bounds on $q$ and $v$.

Next the proof bounds $v$. The first solution relation gives

$$
v(t)+\beta g(t)+q(t)=0,
$$

so

$$
v(t)=-(\beta g(t)+q(t)).
$$

Therefore,

$$
\|v(t)\|
\le \beta\|g(t)\|+\|q(t)\|
\le \beta\max(C_g,0)+\sqrt{C_q}.
$$

This proves $v$ is bounded on $[0,\infty)$, which is the first component of the desired conclusion.

The proof then establishes continuity on $[0,\infty)$. Since $x$ and $y$ are continuous, the linear combination $q=a x+b y$ is continuous. The lemma `gdin_grad_continuous` says that because $\Phi$ is $C^1$, the gradient $\nabla\Phi$ is continuous; composing it with the continuous curve $x$ shows that $g(t)=\nabla\Phi(x(t))$ is continuous on $[0,\infty)$. Finally, since

$$
v=-(\beta g+q),
$$

and $\beta g+q$ is continuous, $v$ is continuous on $[0,\infty)$.

The proof now wants to apply a uniform-continuity lemma, which requires Lipschitz continuity on $(0,\infty)$. It first shows that $x$ is Lipschitz on $(0,\infty)$. The derivative of $x$ is $v$, and $\|v(t)\|\le C_v$ for all $t\ge 0$. Using the fact that a differentiable function on the convex interval $(0,\infty)$ whose derivative has norm at most $C$ is $C$-Lipschitz, the proof obtains a Lipschitz constant for $x$ on $(0,\infty)$.

It similarly shows that $q$ is Lipschitz on $(0,\infty)$. Differentiating $q=a x+b y$, and using $\operatorname{deriv}y(t)=-q(t)$, gives

$$
\operatorname{deriv}q(t)=a v(t)-b q(t).
$$

Hence

$$
\|\operatorname{deriv}q(t)\|
\le |a|\|v(t)\|+b\|q(t)\|
\le |a|\max(C_v,0)+b\max(C_q',0).
$$

The same derivative-to-Lipschitz lemma gives a Lipschitz constant $K_q$ for $q$ on $(0,\infty)$.

For $g=\nabla\Phi\circ x$, the proof composes the Lipschitz bound for $\nabla\Phi$ on $x([0,\infty))$ with the Lipschitz bound for $x$ on $(0,\infty)$. This gives that $g$ is Lipschitz on $(0,\infty)$. For $v$, the proof uses

$$
v=-(\beta g+q).
$$

The map $h\mapsto \beta h$ is continuous linear, so $t\mapsto \beta g(t)$ is Lipschitz; adding the Lipschitz map $q$ and taking negatives preserves Lipschitzness. Thus $v$ is Lipschitz on $(0,\infty)$ as well.

At this point the proof applies `gdin_uniformContinuousOn_Ici_of_lipschitzOn_Ioi`. This lemma says that if a function is Lipschitz on $(0,\infty)$ and continuous on $[0,\infty)$, then it is uniformly continuous on $[0,\infty)$. Applying it to $g$ and to $v$ gives uniform continuity of both on $[0,\infty)$.

The proof next uses the square-integrability results. The theorem `gdin_x_derivative_memL2` says, under the standing hypotheses, that

$$
t\mapsto \operatorname{deriv}x(t)
$$

is in $L^2$ on $[0,\infty)$. The theorem `gdin_gradient_memL2` says similarly that

$$
t\mapsto \nabla\Phi(x(t))
$$

is in $L^2$ on $[0,\infty)$. From these membership statements the proof extracts integrability of

$$
t\mapsto \|v(t)\|^2
$$

and of

$$
t\mapsto \|g(t)\|^2
$$

on $[0,\infty)$.

Now the limit conclusion is obtained. The lemma `gdin_uniformContinuousOn_sq_integrable_tendsto_zero` says that if a function on $[0,\infty)$ is uniformly continuous and its squared norm is integrable on $[0,\infty)$, then the function tends to $0$ at infinity. Applied to $v$, this gives

$$
\operatorname{deriv}x(t)\to 0 \quad \text{as } t\to\infty.
$$

For $g$, the proof uses `gdin_residual_limit`, which states that

$$
\operatorname{deriv}x(t)+\beta\,\nabla\Phi(x(t))\to 0
$$

as $t\to\infty$. Since $\operatorname{deriv}x(t)\to 0$, subtracting gives

$$
\beta\,\nabla\Phi(x(t))\to 0.
$$

Multiplying by the constant $\beta^{-1}$, which is valid because $\beta>0$, yields

$$
\nabla\Phi(x(t))\to 0
$$

as $t\to\infty$.

Finally, the four established facts — boundedness of $v=\operatorname{deriv}x$, boundedness of $g=\nabla\Phi(x(\cdot))$, convergence of $v$ to $0$, and convergence of $g$ to $0$ — are assembled into the required conjunction. The final `simpa` steps unfold the abbreviations $v$ and $g$, returning exactly the statement of `gdin_bounded_asymptotics`.

