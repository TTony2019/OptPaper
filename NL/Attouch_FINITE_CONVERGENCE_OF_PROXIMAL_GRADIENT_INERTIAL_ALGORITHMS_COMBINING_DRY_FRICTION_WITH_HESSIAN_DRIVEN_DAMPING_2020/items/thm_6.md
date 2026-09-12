## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/thm_6.lean`

## Lean statement
```lean
theorem IPAHDDNonsmooth_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (F : H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H))
    (fLam : H → ℝ) (phi : H → ℝ) (h gamma beta lam r : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDNonsmooth F hF phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta lam)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta) (hlam : 0 < lam)
    (hgamma : gamma ≥ (h / 2 + beta) / lam)
    (hfLam_def : fLam = moreauEnvelopeReal F ⟨lam, hlam⟩)
    (hbelow : ∃ c : ℝ, ∀ x, (c : EReal) ≤ (F x : EReal)) :
    ∃ xInf pInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        fLam (alg.x 1) - sInf (Set.range fLam) ∧
      HasFiniteLength alg.x ∧ Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦ ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * (1 / lam) / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} ↦
        ‖alg.x (k.1 + 1) - 2 • alg.x k.1 + alg.x (k.1 - 1)‖ ^ 2) ≤
        2 * h ^ 2 * (E1 + beta * (1 / lam) / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      IsDryFrictionCritical phi fLam xInf ∧
      HasFiniteLength (fun k ↦ ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ (alg.x k)) ∧
      Tendsto (fun k ↦ ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ (alg.x k))
        Filter.atTop (𝓝 pInf) ∧
      pInf = ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩ xInf ∧
      ((1 / lam) • (xInf - pInf) ∈ subdifferential F pInf) ∧
      (-gradient fLam xInf ∈ interior (subdifferential phi 0) →
        let q := 1 / Real.sqrt (1 + 2 * h * (gamma * lam - beta) / (lam + beta * h))
        0 < q ∧ q < 1 ∧ ∃ k0, ∀ k ≥ k0,
          ‖alg.x (k + 1) - alg.x k‖ ≤ q ^ (k - k0) * ‖alg.x (k0 + 1) - alg.x k0‖ ∧
          ‖alg.x k - xInf‖ ≤ q ^ (k - k0) / (1 - q) * ‖alg.x (k0 + 1) - alg.x k0‖) ∧
      (‖gradient fLam xInf‖ < r →
        Metric.ball (0 : H) r ⊆ subdifferential phi 0 → IsFinitelyConvergent alg.x)
```

## Statement explanation
The declaration `IPAHDDNonsmooth_finiteLength` is a convergence theorem for a nonsmooth inertial proximal-gradient algorithm with dry friction and Hessian-driven damping. Let $H$ be a real Hilbert space. The theorem concerns:

- a function $F:H\to(-\infty,+\infty]$ which is proper, convex, and lower semicontinuous, encoded by $F\in\Gamma_0(H)$;
- a real-valued dry-friction function $\phi:H\to\mathbb R$, together with a dry-friction hypothesis `DF_r phi r`;
- real parameters $h,\gamma,\beta,\lambda,r$, with $h>0$, $\gamma>0$, $\beta>0$, $\lambda>0$, and

  $$
  \gamma \ge \frac{h/2+\beta}{\lambda};
  $$

- the real-valued Moreau envelope

  $$
  f_\lambda = \operatorname{moreauEnvelopeReal} F \langle \lambda,h_\lambda\rangle,
  $$

  where $h_\lambda$ is the proof that $\lambda>0$;
- a nonsmooth IPAHDD trajectory `alg` for $F$, $\phi$, and parameters $h,\gamma,\beta,\lambda$, whose iterates are denoted by $x_k=\text{alg.x }k$;
- a lower bound on $F$: there exists $c\in\mathbb R$ such that $c\le F(x)$ for every $x$.

The theorem asserts the existence of $x_\infty$, $p_\infty$, and an initial energy $E_1$ such that:

$$
E_1=\frac12\left\|\frac1h(x_1-x_0)\right\|^2
+f_\lambda(x_1)-\inf_{y\in H} f_\lambda(y).
$$

The sequence $x_k$ has finite length, meaning

$$
\sum_{k=0}^\infty \|x_{k+1}-x_k\|<\infty,
$$

and it converges to $x_\infty$. Moreover,

$$
\sum_{k\ge 1}\|x_{k+1}-x_k\|
\le
\frac1r\left(E_1+\frac{\beta}{2h\lambda}\|x_1-x_0\|^2\right),
$$

and the squared acceleration terms satisfy

$$
\sum_{k\ge 1}\|x_{k+1}-2x_k+x_{k-1}\|^2
\le
2h^2\left(E_1+\frac{\beta}{2h\lambda}\|x_1-x_0\|^2\right).
$$

At the limit, the dry-friction criticality condition holds:

$$
-\nabla f_\lambda(x_\infty)\in \partial\phi(0).
$$

If $P=\operatorname{Prox}_{\lambda F}$, then the proximal sequence $P(x_k)$ also has finite length and converges to some $p_\infty$, with

$$
p_\infty=P(x_\infty).
$$

The limit satisfies the proximal optimality inclusion

$$
\frac1\lambda(x_\infty-p_\infty)\in \partial F(p_\infty).
$$

Finally, the theorem gives two conditional convergence refinements. If

$$
-\nabla f_\lambda(x_\infty)\in \operatorname{int}\partial\phi(0),
$$

then with

$$
q=\left(1+\frac{2h(\gamma\lambda-\beta)}{\lambda+\beta h}\right)^{-1/2},
$$

one has $0<q<1$ and, for some $k_0$, for all $k\ge k_0$,

$$
\|x_{k+1}-x_k\|\le q^{k-k_0}\|x_{k_0+1}-x_{k_0}\|,
$$

and

$$
\|x_k-x_\infty\|\le \frac{q^{k-k_0}}{1-q}\|x_{k_0+1}-x_{k_0}\|.
$$

If instead

$$
\|\nabla f_\lambda(x_\infty)\|<r
\quad\text{and}\quad
B_H(0,r)\subseteq \partial\phi(0),
$$

then the sequence $x_k$ is finitely convergent, meaning it becomes eventually constant.

In ordinary language, the theorem says that the nonsmooth IPAHDD algorithm applied to $F$ with dry friction $\phi$ behaves like the smooth IPAHDD algorithm applied to the Moreau envelope $f_\lambda$ of $F$. It inherits finite-length convergence, stationarity, a proximal-limit relation, and conditional linear and finite convergence.

## Lean proof
```lean
by
  let P : H → H := ERealFunction.scaledProximityOperator F hF ⟨lam, hlam⟩
  have hP_firm : FirmlyNonexpansive P := by
    have hfirm := ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
      (f := (⟨lam, hlam⟩ : PosReal) • F)
      (ERealFunction.smul_mem_gammaZero F hF ⟨lam, hlam⟩)
    simpa [P, ERealFunction.scaledProximityOperator] using hfirm
  have hnonexp : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖ := fun x y => by
    simpa [dist_eq_norm] using (lipschitzWith_one_of_firmlyNonexpansive hP_firm).dist_le_mul x y
  have hderiv : ∀ x, HasFDerivAt fLam (innerSL ℝ ((1 / lam) • (x - P x))) x := by
    intro x
    have h := hasFDerivAt_moreauEnvelopeReal (F := F) hF ⟨lam, hlam⟩ x
    simpa [hfLam_def, P, one_div] using h
  have hlipgrad : LipschitzWith (Real.toNNReal ((⟨lam, hlam⟩ : PosReal) : ℝ)⁻¹)
      (gradient fLam) := by
    have h := lipschitzWith_gradient_moreauEnvelopeReal (F := F) hF ⟨lam, hlam⟩
    simpa [hfLam_def] using h
  have hLip : HasLipschitzGradient (gradient fLam) (1 / lam) := by
    intro x y
    have h := hlipgrad.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at h
    simpa [Real.coe_toNNReal _ (inv_nonneg.mpr hlam.le), one_div] using h
  have hfLam : ContDiff ℝ 1 fLam := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hfd_eq : fderiv ℝ fLam = fun x => InnerProductSpace.toDual ℝ H (gradient fLam x) := by
      funext x
      rw [gradient]
      exact (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ H)
        (fderiv ℝ fLam x)).symm
    rw [hfd_eq]
    exact (InnerProductSpace.toDual ℝ H).continuous.comp hlipgrad.continuous
  let moreauGrad : H → H := fun x ↦ (1 / lam) • (x - P x)
  have hgrad_eq : gradient fLam = moreauGrad := by
    funext x
    rw [gradient, (hderiv x).fderiv]
    have h1 : InnerProductSpace.toDual ℝ H (moreauGrad x) = innerSL ℝ (moreauGrad x) := by
      ext y
      simp
    rw [← h1, LinearIsometryEquiv.symm_apply_apply]
  have hLnonneg : 0 ≤ (1 / lam : ℝ) := (one_div_pos.mpr hlam).le
  have hgamma' : gamma ≥ (1 / lam : ℝ) * (h / 2 + beta) := by
    calc gamma ≥ (h / 2 + beta) / lam := hgamma
         _ = (1 / lam : ℝ) * (h / 2 + beta) := by ring
  -- The Moreau envelope is `C¹` with gradient `(1/λ)(x - Prox_{λF} x)`, so the splitting
  -- iteration `alg` is literally the IPAHDD trajectory of `fLam`.
  have hz : ∀ k, gradient fLam (alg.x k) = (1 / lam) • (alg.x k - P (alg.x k)) := by
    intro k
    simpa [moreauGrad] using congrFun hgrad_eq (alg.x k)
  have hsmooth : ∃ smooth : IPAHDD fLam phi.toEReal hdf.toEReal_mem_gammaZero h gamma beta,
      smooth.x = alg.x := by
    refine ⟨{ h_pos := alg.h_pos
              gamma_pos := alg.gamma_pos
              x := alg.x
              initial0 := alg.x 0
              initial1 := alg.x 1
              init0 := rfl
              init1 := rfl
              update := ?_ }, rfl⟩
    intro k
    have harg : (1 / (h * (1 + h * gamma))) • (alg.x (k + 1) - alg.x k) -
        (beta / (1 + h * gamma)) •
          (gradient fLam (alg.x (k + 1)) - gradient fLam (alg.x k)) -
        (h / (1 + h * gamma)) • gradient fLam (alg.x (k + 1)) = alg.y k := by
      rw [alg.aux k, hz (k + 1), hz k]
      apply ext_inner_left ℝ
      intro w
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
      have hh : h ≠ 0 := ne_of_gt alg.h_pos
      have hl : lam ≠ 0 := ne_of_gt alg.lam_pos
      have hg : 1 + h * gamma ≠ 0 := by
        have hpos : 0 < h * gamma := mul_pos alg.h_pos hpositive.2.1
        exact ne_of_gt (by linarith)
      field_simp
      ring
    rw [alg.update k, harg]
  obtain ⟨smooth, hsmooth⟩ := hsmooth
  -- The Moreau envelope preserves the infimum, so a lower bound on `F` bounds the envelope.
  have hPdom : ∀ y, (F (P y) : EReal) ≠ ⊤ := by
    intro y
    have hmem := ERealFunction.scaledProximityOperator_residual_mem hF ⟨lam, hlam⟩ y
    have hsub : SubdifferentiableAt F (P y) :=
      (SetValuedOperator.mem_dom_iff (∂ F) (P y)).mpr ⟨_, by simpa [P] using hmem⟩
    exact ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp
      (SubdifferentiableAt.mem_effectiveDomain (isProper_of_mem_gammaZero hF).2 hsub))
  have hbelowLam : ∃ c : ℝ, ∀ x, c ≤ fLam x := by
    obtain ⟨c, hc⟩ := hbelow
    refine ⟨c, fun x => ?_⟩
    rw [hfLam_def, moreauEnvelopeReal,
      ERealFunction.moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
        (f := F) (γ := ⟨lam, hlam⟩) hF x]
    rw [EReal.toReal_add (hPdom x) (ne_of_gt (F (P x)).2) (EReal.coe_ne_top _)
        (EReal.coe_ne_bot _),
      EReal.toReal_coe]
    have h1 : c ≤ ((F (P x) : EReal)).toReal :=
      EReal.toReal_le_toReal (hc (P x)) (EReal.coe_ne_bot _) (hPdom x)
    have h2 : 0 ≤ (‖x - P x‖ ^ 2) / (2 * (⟨lam, hlam⟩ : PosReal) : ℝ) := by positivity
    linarith
  have hfinite := IPAHDD_finiteLength_and_critical fLam phi h gamma beta
    (1 / lam) r hdf smooth hfLam hLip
    hLnonneg hbelowLam hpositive hgamma'
  rcases hfinite with ⟨xInf, E1, hE1, hlength, hlim, hcritical, hlenbound, haccelbound⟩
  have hlengthAlg : HasFiniteLength alg.x := by simpa [hsmooth] using hlength
  have hlimAlg : Tendsto alg.x Filter.atTop (𝓝 xInf) := by simpa [hsmooth] using hlim
  have hproxLength : HasFiniteLength (fun k ↦ P (alg.x k)) := by
    unfold HasFiniteLength at hlengthAlg ⊢
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => hnonexp _ _) hlengthAlg
  have hproxCont : Continuous P := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    calc dist (P y) (P x) = ‖P y - P x‖ := dist_eq_norm _ _
         _ ≤ ‖y - x‖ := hnonexp _ _
         _ = dist y x := (dist_eq_norm _ _).symm
         _ < ε := hy
  have hproxLim : Tendsto (fun k ↦ P (alg.x k)) Filter.atTop
      (𝓝 (P xInf)) := hproxCont.continuousAt.tendsto.comp hlimAlg
  have hsubgrad : moreauGrad xInf ∈ subdifferential F (P xInf) := by
    have h := ERealFunction.scaledProximityOperator_residual_mem hF ⟨lam, hlam⟩ xInf
    simpa [P, moreauGrad, one_div, subdifferential] using h
  have hgeo := IPAHDD_geometric_and_finite fLam phi h gamma beta (1 / lam) r
    hdf smooth xInf hfLam hLip hLnonneg hbelowLam hpositive hgamma' hlim
  have hrate :
      1 / Real.sqrt (1 + 2 * h * (gamma - beta * (1 / lam)) /
        (1 + beta * h * (1 / lam))) =
      1 / Real.sqrt (1 + 2 * h * (gamma * lam - beta) / (lam + beta * h)) := by
    congr 2
    field_simp [hlam.ne']
  refine ⟨xInf, P xInf, E1, ?_, hlengthAlg, hlimAlg, ?_, ?_, ?_, hproxLength,
    hproxLim, rfl, ?_, ?_, ?_⟩
  · simpa [hsmooth] using hE1
  · simpa [hsmooth, moreauGrad] using hlenbound
  · simpa [hsmooth, moreauGrad] using haccelbound
  · simpa [IsDryFrictionCritical] using hcritical
  · simpa [moreauGrad] using hsubgrad
  · intro hinterior
    simpa only [hrate, hsmooth] using
      hgeo.1 (by simpa [hfLam_def, moreauGrad, hgrad_eq] using hinterior)
  · intro hnorm hball
    obtain ⟨kStop, hkStop⟩ := hgeo.2 (by simpa [hfLam_def, moreauGrad, hgrad_eq] using hnorm)
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa only [hsmooth] using hkStop)
```

## Proof explanation
The proof first identifies the Moreau envelope $f_\lambda$ with a smooth function whose gradient is the scaled proximal residual, and then transfers the known smooth IPAHDD theory to the nonsmooth trajectory `alg`.

The proof defines

$$
P=\operatorname{scaledProximityOperator} F h_F \langle \lambda,h_\lambda\rangle,
$$

so $P$ is the scaled proximity operator $\operatorname{Prox}_{\lambda F}$. It then proves that $P$ is firmly nonexpansive. For this, it applies `proximityOperator_firmlyNonexpansive_of_mem_gammaZero` to the function $\lambda F$. The cited result says that if a function belongs to $\Gamma_0(H)$, then its proximity operator is firmly nonexpansive. The hypothesis $\lambda F\in\Gamma_0(H)$ is supplied by `smul_mem_gammaZero`, which states that a positive scalar multiple of a $\Gamma_0(H)$ function remains in $\Gamma_0(H)$. Since firm nonexpansiveness implies $1$-Lipschitz continuity by `lipschitzWith_one_of_firmlyNonexpansive`, the proof obtains

$$
\|P x-P y\|\le \|x-y\|
$$

for all $x,y$.

Next, the proof uses `hasFDerivAt_moreauEnvelopeReal`. This theorem says that for $F\in\Gamma_0(H)$ and $\gamma>0$, the Moreau envelope $x\mapsto \operatorname{moreauEnvelopeReal} F \gamma(x)$ is Fréchet differentiable at $x$, with derivative equal to the continuous linear functional

$$
v\mapsto \left\langle \gamma^{-1}\bigl(x-\operatorname{Prox}_{\gamma F}(x)\bigr),v\right\rangle.
$$

With $\gamma=\lambda$, this gives

$$
D f_\lambda(x)
=
\left\langle \frac1\lambda(x-Px),\,\cdot\,\right\rangle.
$$

Thus the Riesz gradient is

$$
\nabla f_\lambda(x)=\frac1\lambda(x-Px).
$$

The proof records this by defining `moreauGrad` and proving `gradient fLam = moreauGrad`.

It also applies `lipschitzWith_gradient_moreauEnvelopeReal`, which states that the gradient of the Moreau envelope is Lipschitz with constant $\gamma^{-1}$. For $\gamma=\lambda$, this gives that $\nabla f_\lambda$ is Lipschitz with constant $1/\lambda$. After converting the nonnegative real constant from `NNReal` to `ℝ`, the proof obtains

$$
\|\nabla f_\lambda(x)-\nabla f_\lambda(y)\|
\le \frac1\lambda\|x-y\|,
$$

i.e. `HasLipschitzGradient (gradient fLam) (1/lam)`.

The proof then shows that $f_\lambda$ is $C^1$. Using `contDiff_one_iff_fderiv`, it is enough to prove that $f_\lambda$ is differentiable everywhere and that its Fréchet derivative is continuous. Differentiability follows from `hderiv`. The derivative is the Riesz dual of the gradient, so continuity of the derivative follows from continuity of the gradient, which follows from its Lipschitz property. Hence `hfLam : ContDiff ℝ 1 fLam`.

The key structural step is `hsmooth`. The nonsmooth algorithm `alg` for $F$ is shown to be exactly a smooth IPAHDD trajectory for the Moreau envelope $f_\lambda$. The proof constructs a smooth trajectory with the same iterates `alg.x`. For each $k$, it proves that the auxiliary vector `alg.y k` satisfies

$$
\frac{1}{h(1+h\gamma)}(x_{k+1}-x_k)
-\frac{\beta}{1+h\gamma}\bigl(\nabla f_\lambda(x_{k+1})-\nabla f_\lambda(x_k)\bigr)
-\frac{h}{1+h\gamma}\nabla f_\lambda(x_{k+1})
=
\text{alg.y }k.
$$

This is done by rewriting with `alg.aux k`, substituting

$$
\nabla f_\lambda(x_k)=\frac1\lambda(x_k-Px_k)
$$

from `hz`, and then reducing the vector equality to inner-product equalities with an arbitrary test vector via `ext_inner_left ℝ`. The scalar algebra is closed by `field_simp` and `ring`. Therefore the smooth algorithm's update equation is satisfied, so the nonsmooth iterates coincide with the smooth iterates for $f_\lambda$.

Before applying the smooth convergence theorem, the proof must show that $f_\lambda$ is bounded below. For this, it first proves that $F(P y)$ is finite for every $y$. It invokes `scaledProximityOperator_residual_mem`, which states that

$$
\frac1\lambda(y-Py)\in \partial F(Py).
$$

Hence $Py$ lies in the domain of the subdifferential of $F$. By `SetValuedOperator.mem_dom_iff`, this means $(\partial F)(Py)$ is nonempty, so $F$ is subdifferentiable at $Py$. Since $F$ is proper by `isProper_of_mem_gammaZero`, subdifferentiability implies that $Py$ belongs to the effective domain, i.e. $F(Py)<+\infty$. Because $F$ already never takes $-\infty$, this means $F(Py)$ is finite.

Then the proof uses `moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero`, which gives the extended-real identity

$$
({}^\lambda F)(x)
=
F(Px)+\frac{\|x-Px\|^2}{2\lambda}.
$$

Since $F(Px)$ is finite and $F$ is bounded below by $c$, one has

$$
c\le F(Px).
$$

The squared-distance term is nonnegative. Converting the extended-real identity to real numbers gives

$$
f_\lambda(x)
=
F(Px)_{\mathrm{toReal}}+\frac{\|x-Px\|^2}{2\lambda}.
$$

Therefore $c\le f_\lambda(x)$ for all $x$, proving that $f_\lambda$ is bounded below.

The proof then applies `IPAHDD_finiteLength_and_critical` to $f_\lambda$, $\phi$, and $L=1/\lambda$. The hypotheses of that theorem are satisfied: $f_\lambda$ is $C^1$, its gradient is Lipschitz with constant $1/\lambda$, $f_\lambda$ is bounded below, $h,\gamma,\beta>0$, and

$$
\gamma\ge \frac{h/2+\beta}{\lambda}
=
\frac1\lambda\left(\frac h2+\beta\right).
$$

The smooth theorem yields $x_\infty$, $E_1$, finite length of the smooth iterates, convergence to $x_\infty$, dry-friction criticality, and the two summability bounds. Since the smooth iterates are exactly `alg.x`, these conclusions transfer to the nonsmooth sequence.

Next, the proof shows that the proximal sequence $P(x_k)$ has finite length. Since $P$ is $1$-Lipschitz,

$$
\|P(x_{k+1})-P(x_k)\|\le \|x_{k+1}-x_k\|.
$$

The comparison test for nonnegative series, invoked by `Summable.of_nonneg_of_le`, then gives

$$
\sum_{k=0}^\infty \|P(x_{k+1})-P(x_k)\|<\infty.
$$

The proof also proves that $P$ is continuous using the same $1$-Lipschitz estimate, and then uses continuity to pass limits: because $x_k\to x_\infty$, it follows that

$$
P(x_k)\to P(x_\infty).
$$

Thus one may choose $p_\infty=P(x_\infty)$, giving both the convergence of the proximal sequence and the equality $p_\infty=P(x_\infty)$.

The subgradient inclusion at the limit follows again from `scaledProximityOperator_residual_mem`. Applied at $x_\infty$, it gives

$$
\frac1\lambda(x_\infty-Px_\infty)\in \partial F(Px_\infty).
$$

Since $p_\infty=Px_\infty$, this is exactly

$$
\frac1\lambda(x_\infty-p_\infty)\in \partial F(p_\infty).
$$

For the geometric rate, the proof applies `IPAHDD_geometric_and_finite` to $f_\lambda$, $\phi$, the same parameters, $L=1/\lambda$, and the already established limit $x_\infty$. The provided statement of that theorem is truncated after `let q`, but the proof uses two consequences. The first, `hgeo.1`, gives the geometric implication: if

$$
-\nabla f_\lambda(x_\infty)\in \operatorname{int}\partial\phi(0),
$$

then the explicit factor lies in $(0,1)$ and the geometric decay estimates hold. The proof then rewrites the factor from the smooth form

$$
\frac{1}{\sqrt{1+2h(\gamma-\beta/\lambda)/(1+\beta h/\lambda)}}
$$

to the stated form

$$
\frac{1}{\sqrt{1+2h(\gamma\lambda-\beta)/(\lambda+\beta h)}}.
$$

This algebraic identity is proved by `congr 2` followed by `field_simp`. Since the smooth iterates equal `alg.x`, the geometric estimates transfer to the nonsmooth trajectory.

For finite convergence, the proof uses the second consequence `hgeo.2` of `IPAHDD_geometric_and_finite`. Given

$$
\|\nabla f_\lambda(x_\infty)\|<r,
$$

it obtains some $k_0$ such that the smooth iterates satisfy

$$
x_{k+1}=x_k
$$

for every $k\ge k_0$. The explicit hypothesis

$$
B_H(0,r)\subseteq \partial\phi(0)
$$

is introduced but not separately consumed in this branch; the dry-friction hypothesis `hdf` is already passed into `IPAHDD_geometric_and_finite`. Finally, the proof applies `eventually_constant_of_eventual_successor_eq`, which states that if a sequence satisfies $x_{k+1}=x_k$ for all sufficiently large $k$, then it is finitely convergent. This gives `IsFinitelyConvergent alg.x`, completing the theorem.

