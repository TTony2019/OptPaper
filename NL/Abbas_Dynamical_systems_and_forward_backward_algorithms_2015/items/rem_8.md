## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_8.lean`

## Lean statement
```lean
theorem restrictive_parameter_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B T : H → H) (S : Set H) (x : ℝ → H) (mu beta : ℝ)
    (hmu : 0 < mu ∧ mu < 2 * beta) (hS : S.Nonempty)
    (_hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (_hB_maximal_monotone : Maximal SetValuedOperator.IsMonotone B.toSetValuedOperator)
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (hT : ∀ q, T q = ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, hmu.1⟩
      (q - mu • B q))
    (hcontraction : LipschitzWith (1 / 2 : NNReal) T)
    (hclassical : ∀ t : ℝ, HasDerivAt x (T (x t) - x t) t)
    (_hdynamics : ∀ t, deriv x t = T (x t) - x t) :
    ∃ z ∈ S, Filter.Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) Filter.atTop
      (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The theorem is a convergence result for a forward-backward dynamical system in a real Hilbert space $H$. The ambient assumptions on $H$ make it a complete real inner product space.

The data and hypotheses are as follows. The function

$$
\Phi : H \to (-\infty,\infty]
$$

has values in extended real numbers strictly larger than $-\infty$, and it is assumed that

$$
\Phi \in \Gamma_0(H).
$$

By the meaning of $\Gamma_0(H)$, this says that $\Phi$ is lower semicontinuous when viewed as an extended-real-valued function and convex on its effective domain.

There are maps

$$
B,T : H \to H,
$$

a set $S \subseteq H$, a trajectory

$$
x : \mathbb R \to H,
$$

and real parameters $\mu,\beta$. The parameter hypothesis is

$$
0 < \mu \quad\text{and}\quad \mu < 2\beta.
$$

The set $S$ is assumed nonempty. The hypothesis on $B$ says that $B$, as a single-valued map on all of $H$, is $\beta$-cocoercive on the whole space. The hypothesis on the associated set-valued operator says that $B$'s set-valued operator is maximal monotone. The set $S$ is characterized by

$$
z \in S \quad\Longleftrightarrow\quad -Bz \in \partial \Phi(z)
$$

for every $z \in H$. Thus $S$ is the solution set of the inclusion $0 \in Bz + \partial \Phi(z)$.

The map $T$ is the forward-backward/proximal-gradient operator associated with $\Phi$ and $B$ with step size $\mu$:

$$
T(q) = \mathrm{Prox}_{\mu \Phi}\bigl(q - \mu B(q)\bigr)
$$

for every $q \in H$. More precisely, in the Lean statement this is written using `scaledProximityOperator`, and the proof unfolds it as the proximity operator of the scaled function $\mu \Phi$. The map $T$ is assumed to be Lipschitz with constant $1/2$:

$$
\|T(u)-T(v)\| \le \frac12 \|u-v\|.
$$

Finally, the trajectory $x$ is assumed to be differentiable at every real $t$, with derivative

$$
x'(t) = T(x(t)) - x(t),
$$

so $x$ solves the dynamical system $\dot x(t) = T(x(t)) - x(t)$. The equivalent `deriv` formulation is also included as a hypothesis, but it is not used in the displayed proof.

The conclusion is that there exists $z \in S$ such that, as $t \to +\infty$,

$$
\mathrm{toWeakSpace}(x(t)) \to \mathrm{toWeakSpace}(z)
$$

in the weak space associated with $H$. In ordinary mathematical language, the trajectory $x(t)$ converges weakly to some solution $z \in S$.

## Lean proof
```lean
by
  obtain ⟨z, hzS⟩ := hS
  have hzsub : -B z ∈ ERealFunction.subdifferential Phi z := (hsolution z).mp hzS
  have hfix : T z = z := by
    rw [hT z]
    let gamma : ERealFunction.PosReal := ⟨mu, hmu.1⟩
    have hg : gamma • Phi ∈ ERealFunction.gammaZero H :=
      ERealFunction.smul_mem_gammaZero Phi hPhi gamma
    have hsub : (z - mu • B z) - z ∈ ERealFunction.subdifferential (gamma • Phi) z := by
      rw [ERealFunction.subdifferential_posReal_smul_eq_smul]
      refine Set.mem_smul_set.2 ⟨-B z, hzsub, ?_⟩
      simp [gamma]
    change ERealFunction.proximityOperator (gamma • Phi) _ (z - mu • B z) = z
    exact (ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential hg
      (z - mu • B z) z).mpr hsub |>.symm
  have henergy : ∀ t : ℝ,
      2 * inner ℝ (x t - z) (T (x t) - x t) ≤ -‖x t - z‖ ^ 2 := by
    intro t
    have hLip : ‖T (x t) - T z‖ ≤ (1 / 2 : ℝ) * ‖x t - z‖ := by
      simpa using hcontraction.norm_sub_le (x t) z
    have hinner : inner ℝ (x t - z) (T (x t) - T z) ≤
        (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 := by
      calc
        inner ℝ (x t - z) (T (x t) - T z) ≤
            ‖x t - z‖ * ‖T (x t) - T z‖ := real_inner_le_norm _ _
        _ ≤ ‖x t - z‖ * ((1 / 2 : ℝ) * ‖x t - z‖) :=
            mul_le_mul_of_nonneg_left hLip (norm_nonneg _)
        _ = (1 / 2 : ℝ) * ‖x t - z‖ ^ 2 := by ring
    rw [show T (x t) - x t = (T (x t) - T z) - (x t - z) by rw [hfix]; abel]
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    nlinarith
  let p : ℝ → ℝ := fun t ↦ Real.exp t * ‖x t - z‖ ^ 2
  have hp : ∀ t : ℝ, HasDerivAt p
      (Real.exp t * ‖x t - z‖ ^ 2 +
        Real.exp t * (2 * inner ℝ (x t - z) (T (x t) - x t))) t := by
    intro t
    simpa [p] using
      (Real.hasDerivAt_exp t).mul ((hclassical t).sub_const z).norm_sq
  have hp_nonpos : ∀ t : ℝ, deriv p t ≤ 0 := by
    intro t
    rw [(hp t).deriv]
    have hscaled := mul_le_mul_of_nonneg_left (henergy t) (Real.exp_pos t).le
    nlinarith
  have hp_diff : Differentiable ℝ p := fun t ↦ (hp t).differentiableAt
  have hp_anti : Antitone p := antitone_of_deriv_nonpos hp_diff hp_nonpos
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖x t - z‖ ^ 2 ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
    intro t ht
    have hle := hp_anti ht
    have hscaled := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-t)).le
    have hexp : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc
      ‖x t - z‖ ^ 2 = Real.exp (-t) * (Real.exp t * ‖x t - z‖ ^ 2) := by
        rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
        simpa [p] using hscaled
  let q : ℝ → ℝ := fun t ↦ if 0 ≤ t then ‖x t - z‖ ^ 2 else 0
  have hq_nonneg : ∀ t : ℝ, 0 ≤ q t := by
    intro t
    by_cases ht : 0 ≤ t <;> simp [q, ht]
  have hq_le : ∀ t : ℝ, q t ≤ Real.exp (-t) * ‖x 0 - z‖ ^ 2 := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa [q, ht] using hbound t ht
    · rw [show q t = 0 by simp [q, ht]]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hexp_zero : Filter.Tendsto
      (fun t : ℝ ↦ Real.exp (-t) * ‖x 0 - z‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul tendsto_const_nhds
  have hq_zero : Filter.Tendsto q Filter.atTop (nhds 0) :=
    squeeze_zero hq_nonneg hq_le hexp_zero
  have hsq_zero : Filter.Tendsto (fun t : ℝ ↦ ‖x t - z‖ ^ 2) Filter.atTop (nhds 0) := by
    apply hq_zero.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simp [q, ht]
  have hsqrt_zero :
      Filter.Tendsto (fun t : ℝ ↦ √(‖x t - z‖ ^ 2)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq_zero
  have hnorm_zero : Filter.Tendsto (fun t : ℝ ↦ ‖x t - z‖) Filter.atTop (nhds 0) := by
    convert hsqrt_zero using 1
    funext t
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hstrong : Filter.Tendsto x Filter.atTop (nhds z) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm_zero
  exact ⟨z, hzS, by simpa using ((toWeakSpaceCLM ℝ H).continuous.tendsto z).comp hstrong⟩
```

## Proof explanation
The proof first extracts a solution from the nonempty set $S$. The command `obtain ⟨z, hzS⟩ := hS` uses the hypothesis that $S$ is nonempty to choose some $z$ with $z \in S$. Then, from the characterization of $S$,

$$
z \in S \quad\Longleftrightarrow\quad -Bz \in \partial \Phi(z),
$$

the proof applies the forward direction to obtain

$$
-Bz \in \partial \Phi(z).
$$

This is recorded as `hzsub`.

Next the proof shows that the chosen solution $z$ is a fixed point of $T$, namely $T(z)=z$. It rewrites $T(z)$ using the hypothesis

$$
T(q)=\mathrm{Prox}_{\mu \Phi}\bigl(q-\mu B(q)\bigr),
$$

so the goal becomes to prove that the proximity operator applied to $z-\mu Bz$ returns $z$.

The proof introduces the positive real number $\gamma=\mu$, using `hmu.1`, which is the assumption $0<\mu$. The cited result `smul_mem_gammaZero` says that if $f \in \Gamma_0(H)$ and $\gamma>0$, then the scaled function $\gamma f$ again belongs to $\Gamma_0(H)$. Applied with $f=\Phi$, it gives

$$
\gamma \Phi \in \Gamma_0(H).
$$

This is needed because the proximal/subdifferential characterization used below requires membership in $\Gamma_0(H)$.

The proof next shows

$$
(z-\mu Bz)-z \in \partial(\gamma \Phi)(z).
$$

The left-hand side is exactly $-\mu Bz$. The cited result `subdifferential_posReal_smul_eq_smul` says that for a positive real scalar $\gamma$,

$$
\partial(\gamma f) = \gamma \cdot \partial f
$$

as set-valued operators. Applied at the point $z$, this means

$$
\partial(\gamma \Phi)(z) = \gamma \cdot \partial \Phi(z).
$$

Since $-Bz \in \partial \Phi(z)$, scalar multiplication by $\gamma=\mu$ gives

$$
-\mu Bz \in \partial(\gamma \Phi)(z).
$$

This is precisely the membership needed. In the Lean proof, `rw [ERealFunction.subdifferential_posReal_smul_eq_smul]` performs this replacement, `Set.mem_smul_set.2` constructs the membership in the scalar multiple of the set by exhibiting the witness $-Bz$, and `simp [gamma]` verifies that the scalar multiple is $-\mu Bz$.

The proof then invokes the cited equivalence `eq_proximityOperator_iff_sub_mem_subdifferential`. For $f \in \Gamma_0(H)$, this equivalence states

$$
p = \mathrm{Prox}_f(x) \quad\Longleftrightarrow\quad x-p \in \partial f(p).
$$

It is applied with

$$
f = \gamma \Phi,\qquad x = z-\mu Bz,\qquad p = z.
$$

The membership just established is exactly

$$
(z-\mu Bz)-z \in \partial(\gamma \Phi)(z),
$$

so the equivalence gives

$$
z = \mathrm{Prox}_{\gamma \Phi}(z-\mu Bz).
$$

Since $\gamma=\mu$, this is

$$
z = \mathrm{Prox}_{\mu \Phi}(z-\mu Bz).
$$

Combining this with the defining property of $T$ gives $T(z)=z$. The Lean proof uses `change` to expose the proximity operator form, applies the equivalence with `.mpr`, and uses `.symm` to orient the equality from the proximity operator back to $z$.

The proof now establishes an energy inequality. For every real $t$, it wants to show

$$
2 \left\langle x(t)-z,\ T(x(t))-x(t)\right\rangle
\le -\|x(t)-z\|^2.
$$

First, the contraction hypothesis on $T$ gives

$$
\|T(x(t))-T(z)\| \le \frac12 \|x(t)-z\|.
$$

This is obtained from `hcontraction.norm_sub_le (x t) z` and simplified to the real-valued form. Since $T(z)=z$, this is a Lipschitz estimate for $T(x(t))$ relative to $z$.

Next, the proof uses the Cauchy-Schwarz inequality for the real inner product,

$$
\langle u,v\rangle \le \|u\|\,\|v\|,
$$

with $u=x(t)-z$ and $v=T(x(t))-T(z)$. This yields

$$
\left\langle x(t)-z,\ T(x(t))-T(z)\right\rangle
\le \|x(t)-z\| \cdot \|T(x(t))-T(z)\|.
$$

Using the Lipschitz bound, the right-hand side is at most

$$
\|x(t)-z\| \cdot \left(\frac12 \|x(t)-z\|\right)
= \frac12 \|x(t)-z\|^2.
$$

Thus

$$
\left\langle x(t)-z,\ T(x(t))-T(z)\right\rangle
\le \frac12 \|x(t)-z\|^2.
$$

The proof then rewrites

$$
T(x(t))-x(t) = \bigl(T(x(t))-T(z)\bigr) - \bigl(x(t)-z\bigr).
$$

This equality uses $T(z)=z$. Applying `inner_sub_right` and `real_inner_self_eq_norm_sq`, the proof obtains

$$
\left\langle x(t)-z,\ T(x(t))-x(t)\right\rangle
=\left\langle x(t)-z,\ T(x(t))-T(z)\right\rangle
-\|x(t)-z\|^2.
$$

Substituting the previous upper bound gives

$$
\left\langle x(t)-z,\ T(x(t))-x(t)\right\rangle
\le \frac12 \|x(t)-z\|^2 - \|x(t)-z\|^2
= -\frac12 \|x(t)-z\|^2.
$$

Multiplying by $2$ gives the desired energy inequality. The tactic `nlinarith` closes this nonlinear arithmetic step.

The proof then introduces the Lyapunov function

$$
p(t) = e^t \|x(t)-z\|^2.
$$

Using the differentiability of $x$, the derivative of $x(t)-z$ is $T(x(t))-x(t)$. The derivative of the squared norm gives the factor

$$
2 \left\langle x(t)-z,\ T(x(t))-x(t)\right\rangle.
$$

The product rule with $e^t$ therefore gives

$$
p'(t)
=e^t \|x(t)-z\|^2
+e^t \cdot 2 \left\langle x(t)-z,\ T(x(t))-x(t)\right\rangle.
$$

This is recorded as `hp`. The proof then shows $p'(t)\le 0$. Indeed, multiplying the energy inequality by the nonnegative factor $e^t$ gives

$$
e^t \cdot 2 \left\langle x(t)-z,\ T(x(t))-x(t)\right\rangle
\le -e^t \|x(t)-z\|^2.
$$

Adding $e^t \|x(t)-z\|^2$ to both sides yields $p'(t)\le 0$. The tactic `nlinarith` closes this inequality.

Since $p$ is differentiable everywhere and $p'(t)\le 0$ for every $t$, the cited result `antitone_of_deriv_nonpos` implies that $p$ is antitone. In ordinary terms, if $s\le t$, then $p(t)\le p(s)$. In particular, for $t\ge 0$,

$$
p(t) \le p(0).
$$

Because

$$
p(t)=e^t \|x(t)-z\|^2,\qquad p(0)=\|x(0)-z\|^2,
$$

this gives

$$
e^t \|x(t)-z\|^2 \le \|x(0)-z\|^2.
$$

Multiplying by the positive number $e^{-t}$ yields the bound

$$
\|x(t)-z\|^2 \le e^{-t} \|x(0)-z\|^2
$$

for every $t\ge 0$. This is the exponential decay estimate `hbound`.

To convert this one-sided bound into a limit statement, the proof defines

$$
q(t)=
\begin{cases}
\|x(t)-z\|^2, & 0\le t,\\
0, & t<0.
\end{cases}
$$

It checks that $q(t)\ge 0$ for all $t$, and that

$$
q(t)\le e^{-t}\|x(0)-z\|^2
$$

for all $t$. For $t\ge 0$, this is the decay bound; for $t<0$, it follows from $q(t)=0$ and the nonnegativity of the right-hand side. Since

$$
e^{-t}\|x(0)-z\|^2 \to 0
$$

as $t\to +\infty$, the squeeze theorem `squeeze_zero` gives

$$
q(t)\to 0.
$$

The proof then uses `hq_zero.congr'` and `filter_upwards` with the eventual condition $t\ge 0$ to replace $q(t)$ by $\|x(t)-z\|^2$ eventually. Hence

$$
\|x(t)-z\|^2 \to 0.
$$

Applying the continuous square-root function gives

$$
\sqrt{\|x(t)-z\|^2} \to 0.
$$

Since $\|x(t)-z\|\ge 0$, one has

$$
\sqrt{\|x(t)-z\|^2}=\|x(t)-z\|.
$$

Therefore

$$
\|x(t)-z\|\to 0.
$$

By the characterization of convergence in a normed group, this is equivalent to strong convergence

$$
x(t)\to z.
$$

The proof records this as `hstrong`.

Finally, the proof uses the canonical continuous linear map from $H$ to its weak space. Since continuous maps preserve limits, strong convergence $x(t)\to z$ implies convergence of the images:

$$
\mathrm{toWeakSpace}(x(t))\to \mathrm{toWeakSpace}(z).
$$

This is exactly the weak convergence asserted in the theorem, and the proof finishes by combining this with the already established $z\in S$.

The displayed proof does not use the hypotheses `_hB`, `_hB_maximal_monotone`, or `_hdynamics`, nor does it use the inequality $\mu<2\beta$. Those remain part of the theorem statement, but the argument given here obtains the conclusion from nonemptiness of $S$, the subdifferential characterization of $S$, the proximal definition of $T$, the Lipschitz contraction of $T$, and the differentiability of the trajectory $x$.

