## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/thm_7.lean`

## Lean statement
```lean
theorem IPAHDDLasso_finiteLength {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi fLam : H → ℝ) (G : H → Set.Ioi (⊥ : EReal)) (hG : G ∈ Γ₀(H))
    (A : H →L[ℝ] H) (M : H →L[ℝ] H) (b : H)
    (h gamma beta lam r L : ℝ) (hdf : DF_r phi r)
    (alg : IPAHDDLasso phi.toEReal hdf.toEReal_mem_gammaZero G hG A M b lam h gamma beta)
    (hphi : ∀ x, phi x = r * ‖x‖)
    (hfLam : ContDiff ℝ 1 fLam)
    (hLip : HasLipschitzGradient (gradient fLam) L) (hL_nonneg : 0 ≤ L)
    (hbelow : ∃ c : ℝ, ∀ x, (c : EReal) ≤ lassoObjectiveE G A b x)
    (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (hgamma : gamma ≥ L * (h / 2 + beta))
    (hfLam_def : fLam = lassoEnvelope G hG A M b ⟨lam, alg.lam_pos⟩) :
    ∃ xInf E1, E1 = (1 / 2) * ‖(1 / h) • (alg.x 1 - alg.x 0)‖ ^ 2 +
        fLam (alg.x 1) - sInf (Set.range fLam) ∧
      HasFiniteLength alg.x ∧ Filter.Tendsto alg.x Filter.atTop (𝓝 xInf) ∧
      tsum (fun k : {k : ℕ // 1 ≤ k} => ‖alg.x (k.1 + 1) - alg.x k.1‖) ≤
        (1 / r) * (E1 + beta * L / (2 * h) * ‖alg.x 1 - alg.x 0‖ ^ 2) ∧
      (∃ u, u ∈ subdifferential G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) ∧
        ‖A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) - b) + u‖ ≤ r) ∧
      (‖gradient fLam xInf‖ < r -> IsFinitelyConvergent alg.x)
```

## Statement explanation
The declaration `IPAHDDLasso_finiteLength` is a convergence and finite-length theorem for the Lasso version of an inertial proximal-gradient algorithm with Hessian-driven damping and dry friction. Let $H$ be a real Hilbert space. The regularizer is an extended-real-valued function $G:H\to(-\infty,+\infty]$, and the hypothesis $G\in\Gamma_0(H)$ means, as used in the proof, that $G$ is convex, lower semicontinuous, and proper. The linear map $A:H\to H$ is the Lasso operator, $b\in H$ is the data vector, and $M:H\to H$ is the variable metric. The scalars are $h,\gamma,\beta,\lambda,r,L\in\mathbb R$. The real function $\phi$ is the dry-friction potential, and the hypothesis `hdf : DF_r phi r` supplies the dry-friction datum with radius $r$; the theorem also assumes explicitly that

$$
\phi(x)=r\|x\|
$$

for every $x\in H$. The other real function $f_\lambda$ is the smooth envelope function. It is assumed to be $C^1$, to have $L$-Lipschitz gradient, with $L\ge 0$. The extended-valued Lasso objective

$$
z\mapsto G(z)+\frac12\|Az-b\|^2
$$

is assumed bounded below in the sense that there is a real $c$ with $c\le G(x)+\frac12\|Ax-b\|^2$ for every $x$, interpreted in the extended real line.

The algorithm object `alg` is an `IPAHDDLasso` trajectory. It carries a sequence $x_k$, auxiliary variables $z_k$, the positivity of $\lambda$, the metric identity

$$
M=I-\lambda A^*A,
$$

and the stability condition $\lambda\|A\|^2<1$. The step-size hypotheses are $h>0$, $\gamma>0$, $\beta>0$, and

$$
\gamma\ge L\left(\frac h2+\beta\right).
$$

Finally, the hypothesis `hfLam_def` identifies $f_\lambda$ with the variable-metric Moreau envelope of the Lasso objective. Concretely, with the Lasso proximal map

$$
p_\lambda(x)=\mathrm{Prox}_{\lambda G}\bigl(x-\lambda A^*(Ax-b)\bigr),
$$

the envelope is

$$
F_\lambda(x)=\frac12\|A p_\lambda(x)-b\|^2
+\mathrm{toReal}\bigl(G(p_\lambda(x))\bigr)
+\frac{\langle M(x-p_\lambda(x)),x-p_\lambda(x)\rangle}{2\lambda},
$$

and the hypothesis says $f_\lambda=F_\lambda$.

The conclusion asserts that there exist $x_\infty\in H$ and $E_1\in\mathbb R$ such that

$$
E_1=\frac12\left\|\frac1h(x_1-x_0)\right\|^2
+f_\lambda(x_1)-\inf f_\lambda,
$$

the trajectory $x_k$ has finite length and converges to $x_\infty$, and its total variation satisfies

$$
\sum_{k=1}^{\infty}\|x_{k+1}-x_k\|
\le
\frac1r\left(E_1+\frac{\beta L}{2h}\|x_1-x_0\|^2\right).
$$

At the limit, there is a subgradient $u\in\partial G(p_\lambda(x_\infty))$ such that

$$
\left\|A^*\bigl(Ap_\lambda(x_\infty)-b\bigr)+u\right\|\le r.
$$

Finally, if the envelope gradient at the limit is strictly below the dry-friction radius,

$$
\|\nabla f_\lambda(x_\infty)\|<r,
$$

then the sequence $x_k$ is finitely convergent, i.e. eventually constant. Thus the theorem says that the Lasso algorithm has finite length, converges, satisfies a limiting Lasso stationarity condition with dry-friction error $r$, and stabilizes in finite time when the limiting gradient is strictly below the dry-friction threshold.

## Lean proof
```lean
by
  -- The Lasso potential `fLam` is the variable-metric Moreau envelope, so its gradient is
  -- formula (5.7) rather than an extra hypothesis.
  have hsymm : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y) :=
    lassoMetric_symm A M lam alg.metric
  have hnorm_le : lam * ‖A‖ ^ 2 ≤ 1 := le_of_lt alg.lam_norm_sq.2
  have hnonneg : ∀ x, 0 ≤ metricNormSq M x :=
    lassoMetric_nonneg A M lam alg.metric alg.lam_pos.le hnorm_le
  have hgrad : ∀ x, gradient fLam x =
      (1 / lam) • M (x - lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x) := by
    intro x
    rw [hfLam_def]
    exact congrFun (gradient_lassoEnvelope G hG A M b lam alg.lam_pos alg.metric hsymm hnonneg) x
  -- The variable-metric Moreau envelope preserves the infimum, so a lower bound on the Lasso
  -- objective bounds the envelope.
  have hGtop : ∀ y, (G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ y) : EReal) ≠ ⊤ := by
    intro y
    have hmem := ERealFunction.scaledProximityOperator_residual_mem hG ⟨lam, alg.lam_pos⟩
      (y - lam • A.adjoint (A y - b))
    have hsub : SubdifferentiableAt G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ y) :=
      (SetValuedOperator.mem_dom_iff (∂ G) (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ y)).mpr
        ⟨_, by simpa [lassoProx] using hmem⟩
    exact ne_of_lt (ERealFunction.mem_effectiveDomain_iff.mp
      (SubdifferentiableAt.mem_effectiveDomain (isProper_of_mem_gammaZero hG).2 hsub))
  have hbelowLam : ∃ c : ℝ, ∀ x, c ≤ fLam x := by
    obtain ⟨c, hc⟩ := hbelow
    refine ⟨c, fun x => ?_⟩
    set p : H := lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x with hp
    have hobj : (lassoObjectiveE G A b p).toReal = lassoObjectiveReal G A b p := by
      simp only [lassoObjectiveE, lassoObjectiveReal]
      rw [EReal.toReal_add (hGtop x) (ne_of_gt (G p).2) (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
        EReal.toReal_coe]
      ring
    have h1 : c ≤ (lassoObjectiveE G A b p).toReal :=
      EReal.toReal_le_toReal (hc p) (EReal.coe_ne_bot _)
        (EReal.add_ne_top (hGtop x) (EReal.coe_ne_top _))
    have hEnv : lassoEnvelope G hG A M b ⟨lam, alg.lam_pos⟩ x =
        lassoObjectiveReal G A b p + metricNormSq M (x - p) / (2 * lam) := by
      simp only [lassoEnvelope, ← hp]
    have h2 : 0 ≤ metricNormSq M (x - p) / (2 * lam) := by
      apply div_nonneg (hnonneg _)
      linarith [alg.lam_pos]
    rw [hfLam_def, hEnv, ← hobj]
    linarith
  -- Splitting (5.6)+(5.7) identifies the Lasso surrogate `z k` with `∇f_λ(x k)`, hence the
  -- Lasso iteration `alg` is literally the IPAHDD trajectory of the envelope `fLam`.
  have hz : ∀ k, alg.z k = gradient fLam (alg.x k) := by
    intro k
    rw [alg.z_def k, hgrad (alg.x k)]
    simp [lassoProx]
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
    rw [alg.update k]
    congr 1
    rw [alg.aux k, hz (k + 1), hz k]
  obtain ⟨smooth, hsmooth⟩ := hsmooth
  -- Paper (5.6) and (5.7) give `∇f_λ^M(x) = Aᵀ(A p x - b) + u` with `u ∈ ∂g(p x)`, where
  -- `p x = prox_{λg}(x - λ Aᵀ(Ax - b))` is the variable-metric proximal point.
  have hcomposite : ∀ x, ∃ u,
      u ∈ subdifferential G (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x) ∧
        gradient fLam x =
          A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x) - b) + u := by
    intro x
    set p : H := lassoProx G hG A b ⟨lam, alg.lam_pos⟩ x with hp
    have hM : M (x - p) = (x - p) - lam • A.adjoint (A (x - p)) := by
      rw [alg.metric]
      simp
    have hgrad' : gradient fLam x = (1 / lam) • M (x - p) := by
      rw [hgrad x, hp]
    have hmem : (lam)⁻¹ • ((x - lam • A.adjoint (A x - b)) - p) ∈ subdifferential G p := by
      have hres := ERealFunction.scaledProximityOperator_residual_mem hG ⟨lam, alg.lam_pos⟩
        (x - lam • A.adjoint (A x - b))
      simpa [p, lassoProx] using hres
    refine ⟨(lam)⁻¹ • ((x - lam • A.adjoint (A x - b)) - p), hmem, ?_⟩
    rw [hgrad', hM, one_div]
    have hAdj : A.adjoint (A (x - p)) = A.adjoint (A x - b) - A.adjoint (A p - b) := by
      simp only [map_sub]
      abel
    rw [hAdj]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ alg.lam_pos.ne', one_smul]
    abel
  obtain ⟨xInf, Ebase, hEbase, hfinite, hlim, hcritical, hlen, _⟩ :=
    IPAHDD_finiteLength_and_critical fLam phi h gamma beta L r hdf smooth
      hfLam hLip hL_nonneg hbelowLam hpositive hgamma
  obtain ⟨u, hu, hgrad_eq⟩ := hcomposite xInf
  have hnormgrad : ‖gradient fLam xInf‖ ≤ r := by
    have hsub : -gradient fLam xInf ∈ subdifferential phi 0 := hcritical
    simpa only [norm_neg] using
      linear_dry_friction_subgradient_norm_le phi r hphi hdf.radius_pos hsub
  have hstationary :
      ‖A.adjoint (A (lassoProx G hG A b ⟨lam, alg.lam_pos⟩ xInf) - b) + u‖ ≤ r := by
    rw [← hgrad_eq]
    exact hnormgrad
  refine ⟨xInf, Ebase, ?_, ?_, ?_, ?_, ⟨u, hu, hstationary⟩, ?_⟩
  · simpa [hsmooth] using hEbase
  · simpa [hsmooth] using hfinite
  · simpa [hsmooth] using hlim
  · simpa [hsmooth] using hlen
  · intro hgradstrict
    obtain ⟨kStop, hkStop⟩ := IPAHDD_geometric_and_finite fLam phi
      h gamma beta L r hdf smooth xInf hfLam hLip hL_nonneg hbelowLam hpositive
      hgamma hlim |>.2 hgradstrict
    exact eventually_constant_of_eventual_successor_eq alg.x kStop (by
      simpa [hsmooth] using hkStop)
```

## Proof explanation
The proof begins by extracting the metric properties needed for the envelope formula. From the equality $M=I-\lambda A^*A$ carried by `alg`, the lemma `lassoMetric_symm` gives

$$
\langle Mx,y\rangle=\langle x,My\rangle
$$

for all $x,y\in H$. This is the symmetry of the metric $M$. The proof stores this as `hsymm`. Next, from the algorithm condition $\lambda\|A\|^2<1$, the proof weakens it to $\lambda\|A\|^2\le 1$ using `le_of_lt`, and then applies `lassoMetric_nonneg`. That lemma states that when $M=I-\lambda A^*A$, $\lambda\ge0$, and $\lambda\|A\|^2\le1$, one has

$$
\langle Mx,x\rangle\ge0
$$

for every $x$. The proof records this as `hnonneg`. These two facts are exactly the hypotheses needed to apply the envelope-gradient formula.

The pointwise gradient formula is then established as `hgrad`. For every $x$, the proof rewrites $f_\lambda$ using `hfLam_def`, so that $f_\lambda$ is replaced by the Lasso envelope. It then applies `gradient_lassoEnvelope`. That theorem says that under the assumptions $G\in\Gamma_0(H)$, $\lambda>0$, symmetry of $M$, and nonnegativity of the quadratic form $x\mapsto\langle Mx,x\rangle$, the gradient of the Lasso envelope is

$$
\nabla f_\lambda(x)
=
\frac1\lambda M\bigl(x-p_\lambda(x)\bigr).
$$

The proof obtains the function equality from `gradient_lassoEnvelope` and applies it pointwise using `congrFun`, giving

$$
\forall x,\qquad
\nabla f_\lambda(x)
=
\frac1\lambda M\bigl(x-p_\lambda(x)\bigr).
$$

This is the key identity that later identifies the Lasso auxiliary variable $z_k$ with the gradient of $f_\lambda$.

Next the proof shows that the regularizer $G$ is finite at every proximal point $p_\lambda(y)$. The claim is

$$
G(p_\lambda(y))\ne\top
$$

for every $y$. To prove this, the proof uses the proximal residual lemma `scaledProximityOperator_residual_mem`. Specialized here, it says that if $G\in\Gamma_0(H)$, $\lambda>0$, and

$$
p_\lambda(y)=\mathrm{Prox}_{\lambda G}\bigl(y-\lambda A^*(Ay-b)\bigr),
$$

then

$$
\frac1\lambda\Bigl(\bigl(y-\lambda A^*(Ay-b)\bigr)-p_\lambda(y)\Bigr)
\in
\partial G(p_\lambda(y)).
$$

Thus the subdifferential of $G$ at $p_\lambda(y)$ is nonempty. Using `SetValuedOperator.mem_dom_iff`, nonemptiness of $\partial G(p_\lambda(y))$ means that $p_\lambda(y)$ lies in the domain of the subdifferential, i.e. $p_\lambda(y)$ is subdifferentiable. Since $G\in\Gamma_0(H)$, the theorem `isProper_of_mem_gammaZero` gives that the underlying extended-real function is proper. A proper function that is subdifferentiable at a point must have that point in its effective domain; equivalently, $G(p_\lambda(y))<\top$. The proof therefore concludes $G(p_\lambda(y))\ne\top$. This step matters because it permits the later passage between extended-real values and real values of the Lasso objective at the proximal point.

Using that finiteness, the proof derives a real lower bound for the envelope $f_\lambda$ from the assumed lower bound on the extended Lasso objective. The hypothesis `hbelow` gives a real $c$ such that

$$
c\le \mathrm{lassoObjectiveE}(G,A,b,p)
$$

for every $p$. For an arbitrary $x$, the proof sets $p=p_\lambda(x)$. Because $G(p)$ is finite, the real part of the extended Lasso objective equals the real-valued Lasso objective:

$$
\mathrm{toReal}\bigl(\mathrm{lassoObjectiveE}(G,A,b,p)\bigr)
=
\mathrm{lassoObjectiveReal}(G,A,b,p).
$$

The proof uses the facts `EReal.toReal_add`, `EReal.toReal_coe`, and finite/non-bottom/non-top side conditions to justify this passage. It then applies monotonicity of taking real parts in the extended real line, `EReal.toReal_le_toReal`, to obtain

$$
c\le \mathrm{toReal}\bigl(\mathrm{lassoObjectiveE}(G,A,b,p)\bigr).
$$

On the other hand, the definition of `lassoEnvelope` gives

$$
f_\lambda(x)
=
\mathrm{lassoObjectiveReal}(G,A,b,p)
+
\frac{\langle M(x-p),x-p\rangle}{2\lambda}.
$$

The quadratic metric term is nonnegative by `hnonneg`, and the denominator is nonnegative because $\lambda>0$; the proof uses `div_nonneg` and `linarith` to verify this. Combining these inequalities with `linarith` yields a global real lower bound for $f_\lambda$. This produces `hbelowLam`, which is needed because the abstract IPAHDD theorem is stated for real-valued functions bounded below.

The proof next identifies the Lasso auxiliary variables with the gradient of the envelope. The Lasso algorithm defines $z_k$ through the Lasso surrogate, and the proof rewrites `alg.z_def` together with the already established `hgrad` and the definition of `lassoProx`. The result is

$$
z_k=\nabla f_\lambda(x_k)
$$

for every $k$. This is the mathematical bridge between the Lasso iteration and the general IPAHDD iteration for the smooth function $f_\lambda$: the Lasso update is exactly the IPAHDD update for $f_\lambda$ once the surrogate $z_k$ is recognized as $\nabla f_\lambda(x_k)$.

This bridge is formalized by constructing a new `IPAHDD` trajectory named `smooth` whose $x$-sequence is the same as `alg.x`. The proof fills the fields of the IPAHDD structure using the corresponding fields of `alg`, including positivity of $h$, positivity of $\gamma$, the same $x$, the same initial points $x_0,x_1$, and the same update rule. The update field is verified by rewriting the Lasso update with `alg.update`, then using `congr 1` to reduce the equality to equality of the arguments involving $z$, and finally rewriting with `alg.aux k` and the previously proved `hz` to replace the Lasso auxiliary variables by the gradient values. Thus the constructed `smooth` is a genuine IPAHDD trajectory for the envelope $f_\lambda$, and its $x$-sequence equals `alg.x`.

The proof now establishes the composite subgradient representation of the envelope gradient. For every $x$, with $p=p_\lambda(x)$, it shows there exists $u\in\partial G(p)$ such that

$$
\nabla f_\lambda(x)
=
A^*\bigl(Ap-b\bigr)+u.
$$

First, using the metric identity $M=I-\lambda A^*A$, it obtains

$$
M(x-p)=(x-p)-\lambda A^*A(x-p).
$$

Together with the gradient formula this gives

$$
\nabla f_\lambda(x)
=
\frac1\lambda M(x-p).
$$

Next, `scaledProximityOperator_residual_mem` applied to the proximal point $p=p_\lambda(x)$ gives

$$
u:=\frac1\lambda\Bigl(x-\lambda A^*(Ax-b)-p\Bigr)
\in
\partial G(p).
$$

The proof then rewrites

$$
A^*A(x-p)
=
A^*(Ax-b)-A^*(Ap-b),
$$

using additivity of the adjoint and elementary additive regrouping. Substituting this into the expression for $\frac1\lambda M(x-p)$ gives exactly

$$
A^*(Ap-b)+u.
$$

Thus `hcomposite` says that the envelope gradient splits into the smooth Lasso gradient $A^*(Ap-b)$ plus a subgradient $u$ of the regularizer $G$ at the proximal point $p$. This is the concrete mathematical content behind formulas (5.6) and (5.7).

The proof then applies the abstract theorem `IPAHDD_finiteLength_and_critical` to the function $f_\lambda$, the dry-friction function $\phi$, the constructed trajectory `smooth`, and the parameters $h,\gamma,\beta,L,r$. All hypotheses have already been assembled: $f_\lambda$ is $C^1$, its gradient is $L$-Lipschitz, $L\ge0$, $f_\lambda$ is bounded below, and the positivity and step-size conditions hold. The theorem returns an $x_\infty$ and an $E_{\text{base}}$ satisfying

$$
E_{\text{base}}
=
\frac12\left\|\frac1h(\text{smooth}.x_1-\text{smooth}.x_0)\right\|^2
+
f_\lambda(\text{smooth}.x_1)
-
\inf f_\lambda,
$$

together with finite length of the trajectory, convergence of the trajectory to $x_\infty$, the dry-friction criticality condition, and the finite total-variation estimate. The proof keeps the first four conclusions and the length estimate; the additional second-order acceleration estimate returned by that theorem is not used and is discarded with `_`.

The proof then specializes `hcomposite` to $x_\infty$. It obtains a $u$ such that

$$
u\in\partial G(p_\lambda(x_\infty))
$$

and

$$
\nabla f_\lambda(x_\infty)
=
A^*\bigl(Ap_\lambda(x_\infty)-b\bigr)+u.
$$

The next step is to bound the gradient of the envelope at the limit by the dry-friction radius. The criticality conclusion from `IPAHDD_finiteLength_and_critical` is used as the subgradient membership

$$
-\nabla f_\lambda(x_\infty)\in\partial\phi(0).
$$

Since the theorem assumes $\phi(y)=r\|y\|$ and the dry-friction datum gives $r>0$, the lemma `linear_dry_friction_subgradient_norm_le` applies. That lemma states that if $\phi(y)=r\|y\|$, $r>0$, and $q\in\partial\phi(0)$, then $\|q\|\le r$. Taking $q=-\nabla f_\lambda(x_\infty)$, the proof obtains

$$
\|-\nabla f_\lambda(x_\infty)\|\le r,
$$

and since $\|-\nabla f_\lambda(x_\infty)\|=\|\nabla f_\lambda(x_\infty)\|$, it gets

$$
\|\nabla f_\lambda(x_\infty)\|\le r.
$$

Using the composite representation of the gradient at $x_\infty$, this immediately gives the stationarity estimate

$$
\left\|A^*\bigl(Ap_\lambda(x_\infty)-b\bigr)+u\right\|\le r.
$$

This is the limiting Lasso optimality condition with dry-friction error $r$.

Finally, the proof assembles the required existential statement. It chooses $x_\infty$ and $E_{\text{base}}$ as the witnesses. The energy formula, finite length, convergence, and total-variation bound are transported from the `smooth` trajectory to `alg.x` by `simpa` using the equality `smooth.x = alg.x`. The subgradient condition is supplied directly by the $u$, its membership in $\partial G(p_\lambda(x_\infty))$, and the stationarity estimate just proved.

For the last clause, assume

$$
\|\nabla f_\lambda(x_\infty)\|<r.
$$

The proof applies the second part of `IPAHDD_geometric_and_finite`. The provided source truncates the full statement of that theorem, but in this proof the exact consequence used is: under the same IPAHDD hypotheses and convergence of the trajectory to $x_\infty$, if the strict gradient inequality above holds, then there exists an index $kStop$ such that for all $k\ge kStop$,

$$
\text{smooth}.x(k+1)=\text{smooth}.x(k).
$$

Since `smooth.x = alg.x`, `simpa` transfers this to the Lasso trajectory `alg.x`. The theorem `eventually_constant_of_eventual_successor_eq` then applies: if a sequence satisfies $x(k+1)=x(k)$ for all sufficiently large $k$, then it is finitely convergent. Therefore the proof concludes `IsFinitelyConvergent alg.x`. Mathematically, the Lasso trajectory stabilizes in finite time whenever the limiting envelope gradient is strictly smaller than the dry-friction radius.

