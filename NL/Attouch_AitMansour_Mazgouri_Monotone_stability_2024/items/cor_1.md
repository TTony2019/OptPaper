## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/cor_1.lean`

## Lean statement
```lean
theorem cor_1 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup M] (V : Set M) (φ : M → H → ℝ) (gradφ : M → H → H)
    (γ : ℝ) (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H)
    (β : M → ℝ) (k₁ γ₁ : ℝ)
    (hconv : ∀ μ ∈ V, IsConvex (φ μ))
    (hdiff : ∀ μ ∈ V, Differentiable ℝ (φ μ))
    (hgrad_id : ∀ μ ∈ V, ∀ q : H, HasGradientAt (φ μ) (gradφ μ q) q)
    (hgrad : ∀ μ ∈ V, LipschitzWith (Real.toNNReal (1 / (β μ))) (gradφ μ))
    (hsol : ∀ μ ∈ V, ext_def_2 (gradφ μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (h9 : ∀ x_ : H, ∀ μ ∈ V, ∀ μ' ∈ V, ‖gradφ μ x_ - gradφ μ' x_‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁)
    (hβ : ∀ μ ∈ V, 0 < β μ) (hk₁ : 0 < k₁) (hγ₁_pos : 0 < γ₁) (hγ₁_le : γ₁ ≤ 1) :
    (∀ μ ∈ V, ∃ x_μ dx_μ ddx_μ : ℝ → H,
      ext_def_2 (gradφ μ) γ (u₀ μ) (v₀ μ) x_μ dx_μ ddx_μ ∧
        ∀ y dy ddy : ℝ → H,
          ext_def_2 (gradφ μ) γ (u₀ μ) (v₀ μ) y dy ddy →
            Set.EqOn x_μ y (Set.Ici 0)) ∧
    (∀ μ ∈ V, ∀ μ' ∈ V,
      let m_μ := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((β μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((β μ') ^ 2))
      let m := max m_μ m_μ'
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ Real.exp (m * t) * Real.sqrt (‖u₀ μ - u₀ μ'‖ ^ 2 + ‖v₀ μ - v₀ μ'‖ ^ 2) +
          (k₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ γ₁)
```

## Statement explanation
The declaration `cor_1` is a parameterized stability corollary for a family of convex functions on a real Hilbert space. Let $H$ be a real Hilbert space, let $M$ be a normed additive commutative group, and let $V\subseteq M$ be a parameter set. For each $\mu\in M$, write

$$
\phi_\mu=\phi(\mu):H\to\mathbb R,\qquad G_\mu=\mathrm{gradφ}(\mu):H\to H.
$$

Thus $G_\mu(q)$ is asserted to be the gradient of $\phi_\mu$ at $q$. The theorem also has a damping parameter $\gamma\in\mathbb R$, initial data

$$
u_0,v_0:M\to H,
$$

given curves

$$
x,dx,ddx:M\to \mathbb R\to H,
$$

and a function $\beta:M\to\mathbb R$, together with constants $k_1,\gamma_1\in\mathbb R$.

The hypotheses are as follows.

- For every $\mu\in V$, $\phi_\mu$ is convex: $\mathrm{IsConvex}(\phi_\mu)$.
- For every $\mu\in V$, $\phi_\mu$ is differentiable over $\mathbb R$: $\mathrm{Differentiable}_{\mathbb R}(\phi_\mu)$.
- For every $\mu\in V$ and every $q\in H$, $G_\mu(q)$ is the gradient of $\phi_\mu$ at $q$:

  $$
  \mathrm{HasGradientAt}(\phi_\mu,G_\mu(q),q).
  $$

- For every $\mu\in V$, $G_\mu$ is Lipschitz with constant $\mathrm{toNNReal}(1/\beta_\mu)$, where $\beta_\mu=\beta(\mu)$. Since $\beta_\mu>0$ is assumed below, this is the nonnegative real constant $1/\beta_\mu$.
- For every $\mu\in V$, the triple $(x_\mu,dx_\mu,ddx_\mu)=(x(\mu),dx(\mu),ddx(\mu))$ satisfies the predicate

  $$
  \mathrm{ext\_def\_2}(G_\mu,\gamma,u_0(\mu),v_0(\mu),x_\mu,dx_\mu,ddx_\mu).
  $$

  The internal definition of `ext_def_2` is not included in the supplied context; the statement only uses it as a solution predicate for the second-order problem with operator $G_\mu$, damping $\gamma$, and initial data $u_0(\mu),v_0(\mu)$.
- The gradients depend Hölder continuously on the parameter: for all $q\in H$ and all $\mu,\mu'\in V$,

  $$
  \|G_\mu(q)-G_{\mu'}(q)\|\le k_1\|\mu-\mu'\|^{\gamma_1}.
  $$

- The scalar parameters satisfy $\beta_\mu>0$ for all $\mu\in V$, $k_1>0$, $0<\gamma_1$, and $\gamma_1\le 1$.

The conclusion has two parts.

First, for every $\mu\in V$, there exists a solution triple $(\tilde x_\mu,\widetilde{dx}_\mu,\widetilde{ddx}_\mu):\mathbb R\to H$ of

$$
\mathrm{ext\_def\_2}(G_\mu,\gamma,u_0(\mu),v_0(\mu),\tilde x_\mu,\widetilde{dx}_\mu,\widetilde{ddx}_\mu),
$$

and any other solution $(y,dy,ddy)$ of the same problem satisfies

$$
\tilde x_\mu(t)=y(t)\qquad\text{for all }t\ge 0.
$$

Thus the solution is unique on the nonnegative half-line $[0,\infty)$.

Second, for all $\mu,\mu'\in V$, define

$$
m_\mu=\sqrt{1+2\gamma^2+\frac{2}{(\beta_\mu)^2}},\qquad
m_{\mu'}=\sqrt{1+2\gamma^2+\frac{2}{(\beta_{\mu'})^2}},\qquad
m=\max(m_\mu,m_{\mu'}).
$$

Then for almost every $t$ with respect to Lebesgue measure on $\mathbb R$, if $0\le t$, the given solutions $x_\mu$ and $x_{\mu'}$ satisfy

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+\frac{k_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\gamma_1}.
$$

In ordinary language: under convexity, differentiability, gradient, Lipschitz/cocoercivity, and parameter-Hölder assumptions, the family of second-order problems has unique solutions on $[0,\infty)$, and the solutions depend on the parameter with an explicit exponential-in-time Hölder stability estimate.

## Lean proof
```lean
by
  by_cases hV : V.Nonempty
  · rcases hV with ⟨μ0, hμ0⟩
    have hγpos : 0 < γ := (hsol μ0 hμ0).1
    have hC1 : ∀ μ ∈ V, 0 < β μ ∧ ∀ u v : H,
        β μ * ‖gradφ μ u - gradφ μ v‖ ^ 2 ≤
          inner ℝ (gradφ μ u - gradφ μ v) (u - v) := by
      intro μ hμ
      have hc : CocoerciveOn (β μ) Set.univ (fun x : Set.univ => gradφ μ x) := by
        simpa [one_div] using
          (ext_thm_4 (φ μ) (gradφ μ) (1 / β μ) (one_div_pos.mpr (hβ μ hμ))
            (hconv μ hμ) (hdiff μ hμ) (hgrad_id μ hμ) (hgrad μ hμ))
      exact ⟨hβ μ hμ, fun u v => by
        simpa [real_inner_comm] using
          (hc.2 ⟨u, Set.mem_univ u⟩ ⟨v, Set.mem_univ v⟩)⟩
    have hC2 : 0 < k₁ ∧ 0 < γ₁ ∧ γ₁ ≤ 1 ∧
        ∀ u μ μ', μ ∈ V → μ' ∈ V →
          ‖gradφ μ u - gradφ μ' u‖ ≤ k₁ * ‖μ - μ'‖ ^ γ₁ :=
      ⟨hk₁, hγ₁_pos, hγ₁_le, by
        intro u μ μ' hμ hμ'
        exact h9 u μ hμ μ' hμ'⟩
    obtain ⟨hunique, hstable⟩ :=
      thm_1 V gradφ γ u₀ v₀ β k₁ γ₁ hγpos hC1 hC2
    refine ⟨hunique, ?_⟩
    intro μ hμ μ' hμ'
    rcases hstable μ hμ μ' hμ' with
      ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hbound⟩
    obtain ⟨z, dz, ddz, hz, hzuniq⟩ := hunique μ hμ
    have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
      (hzuniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
        (hzuniq y dy ddy hy ht)
    obtain ⟨z', dz', ddz', hz', hz'uniq⟩ := hunique μ' hμ'
    have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
      (hz'uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
        (hz'uniq y' dy' ddy' hy' ht)
    filter_upwards [hbound] with t ht
    intro ht_nonneg
    rw [hxy ht_nonneg, hxy' ht_nonneg]
    exact ht ht_nonneg
  · rw [Set.not_nonempty_iff_eq_empty.mp hV]
    simp
```

## Proof explanation
The proof begins with a case split on whether $V$ is nonempty, using `by_cases hV : V.Nonempty`.

In the nonempty case, `rcases hV with ⟨μ0, hμ0⟩` chooses a parameter $\mu_0\in V$. The proof then extracts

$$
0<\gamma
$$

from `(hsol μ0 hμ0).1`. This means the predicate `ext_def_2`, at the chosen $\mu_0$, has the positivity of the damping parameter as its first component. This is the only structural fact about `ext_def_2` used directly in extracting $0<\gamma$.

Next the proof constructs the hypothesis `hC1`, which is exactly the pointwise cocoercivity condition required by `thm_1`. For an arbitrary $\mu\in V$, it must prove

$$
0<\beta_\mu
$$

and, for all $u,v\in H$,

$$
\beta_\mu\|G_\mu(u)-G_\mu(v)\|^2
\le
\langle G_\mu(u)-G_\mu(v),u-v\rangle.
$$

The positivity $0<\beta_\mu$ is supplied by `hβ μ hμ`.

To obtain the cocoercivity inequality, the proof applies the external result `ext_thm_4` to the function $\phi_\mu$, its gradient $G_\mu$, and the constant

$$
L=\frac{1}{\beta_\mu}.
$$

The hypotheses of `ext_thm_4` are precisely that $L>0$, $\phi_\mu$ is convex, $\phi_\mu$ is differentiable, $G_\mu(q)$ is the gradient of $\phi_\mu$ at every $q$, and $G_\mu$ is Lipschitz with constant $\mathrm{toNNReal}(L)$. These are supplied respectively by $0<\beta_\mu$, `hconv μ hμ`, `hdiff μ hμ`, `hgrad_id μ hμ`, and `hgrad μ hμ`.

The mathematical content of `ext_thm_4` is: if a convex differentiable function on a real Hilbert space has gradient map that is $L$-Lipschitz, then that gradient map is $(1/L)$-cocoercive on the whole space. Its conclusion is therefore

$$
\mathrm{CocoerciveOn}\left(\frac{1}{L},\mathrm{Set.univ},G_\mu\right).
$$

Since $L=1/\beta_\mu$, we have $1/L=\beta_\mu$. The command `simpa [one_div]` performs this reciprocal simplification, yielding

$$
\mathrm{CocoerciveOn}(\beta_\mu,\mathrm{Set.univ},G_\mu).
$$

The definition of `CocoerciveOn` says that $\beta_\mu>0$ and that for all $x,y$ in the domain,

$$
\beta_\mu\|G_\mu(x)-G_\mu(y)\|^2
\le
\langle x-y,G_\mu(x)-G_\mu(y)\rangle.
$$

Applying this to $u,v\in H$ gives

$$
\beta_\mu\|G_\mu(u)-G_\mu(v)\|^2
\le
\langle u-v,G_\mu(u)-G_\mu(v)\rangle.
$$

The proof then uses `real_inner_comm`, the symmetry of the real inner product, to rewrite the right-hand side as

$$
\langle G_\mu(u)-G_\mu(v),u-v\rangle.
$$

This is exactly the inequality required for `hC1`.

Next the proof assembles `hC2`. This is the parameter-Hölder condition required by `thm_1`: it combines `hk₁`, `hγ₁_pos`, `hγ₁_le`, and the hypothesis `h9`. Concretely, it states

$$
0<k_1,\qquad 0<\gamma_1,\qquad \gamma_1\le 1,
$$

and for all $q\in H$ and all $\mu,\mu'\in V$,

$$
\|G_\mu(q)-G_{\mu'}(q)\|\le k_1\|\mu-\mu'\|^{\gamma_1}.
$$

The inner proof simply introduces $q,\mu,\mu'$ and applies `h9`.

The proof then applies `thm_1` with

$$
A=G,\qquad \alpha=\beta,\qquad \theta_1=k_1,\qquad \theta_2=\gamma_1.
$$

The hypotheses of `thm_1` are $0<\gamma$, the pointwise cocoercivity condition `hC1`, and the parameter-Hölder condition `hC2`. Its conclusion is twofold. First, for every $\mu\in V$, there exists a solution triple of

$$
\mathrm{ext\_def\_2}(G_\mu,\gamma,u_0(\mu),v_0(\mu),\cdot,\cdot,\cdot),
$$

and any two such solutions agree on $[0,\infty)$. Second, for every $\mu,\mu'\in V$, with

$$
m_\mu=\sqrt{1+2\gamma^2+\frac{2}{\beta_\mu^2}},\qquad
m_{\mu'}=\sqrt{1+2\gamma^2+\frac{2}{\beta_{\mu'}^2}},\qquad
m=\max(m_\mu,m_{\mu'}),
$$

there exist solutions $y,y'$ for $\mu,\mu'$ such that for almost every $t$,

$$
0\le t\implies
\|y(t)-y'(t)\|
\le e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+\frac{k_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\gamma_1}.
$$

The proof binds these two conclusions as `hunique` and `hstable`.

The command `refine ⟨hunique, ?_⟩` uses `hunique` directly for the first assertion of `cor_1`, because that assertion is exactly the existence-and-uniqueness statement produced by `thm_1`. The remaining goal is the stability estimate for the originally given solutions $x_\mu,x_{\mu'}$.

Fix $\mu,\mu'\in V$. From `hstable μ hμ μ' hμ'`, the proof obtains solutions $y,y'$, derivative witnesses $dy,ddy,dy',ddy'$, proofs `hy` and `hy'` that these are solutions for $\mu$ and $\mu'$, and an almost-everywhere inequality `hbound`:

$$
\|y(t)-y'(t)\|
\le e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+\frac{k_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\gamma_1}
$$

for almost every $t$ satisfying $0\le t$.

The proof must replace $y,y'$ by the given functions $x_\mu,x_{\mu'}$. It does this using uniqueness. From `hunique μ hμ`, it obtains a canonical solution $z$ with derivatives $dz,ddz$, together with the uniqueness statement `hzuniq`: every solution for $\mu$ equals $z$ on $[0,\infty)$.

Now `hzuniq` is applied twice. Applied to $(x_\mu,dx_\mu,ddx_\mu)$ and the hypothesis `hsol μ hμ`, it gives

$$
z(t)=x_\mu(t)
$$

for all $t\ge 0$. Applied to $(y,dy,ddy)$ and `hy`, it gives

$$
z(t)=y(t)
$$

for all $t\ge 0$. Combining these equalities symmetrically and transitively gives

$$
x_\mu(t)=y(t)
$$

for all $t\ge 0$. This is `hxy`. The same argument for $\mu'$ gives `hxy'`:

$$
x_{\mu'}(t)=y'(t)
$$

for all $t\ge 0$.

Finally the proof establishes the almost-everywhere estimate for $x_\mu,x_{\mu'}$. The tactic command `filter_upwards [hbound] with t ht` reduces the goal from an almost-everywhere statement to the pointwise situation where the almost-everywhere fact `hbound` is available. The variable `ht` is the inequality from `hbound` at the point $t$. After `intro ht_nonneg`, the proof assumes $0\le t$. The goal is then

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le e^{mt}\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
+\frac{k_1}{m}(e^{mt}-1)\|\mu-\mu'\|^{\gamma_1}.
$$

Using `rw [hxy ht_nonneg, hxy' ht_nonneg]`, the proof rewrites $x_\mu(t)$ to $y(t)$ and $x_{\mu'}(t)$ to $y'(t)$. The goal becomes exactly the inequality supplied by `ht`. Then `exact ht ht_nonneg` closes the goal. Since this works on the almost-everywhere set where `hbound` holds, the desired almost-everywhere statement follows.

In the empty case, `Set.not_nonempty_iff_eq_empty.mp hV` turns the hypothesis that $V$ is not nonempty into $V=\emptyset$. Then `simp` simplifies the universally quantified statements over the empty set to true, so the entire conclusion holds vacuously.

No step in this proof uses `linarith`.

