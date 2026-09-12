## Source file
`Attouch_AitMansour_Mazgouri_Monotone_stability_2024/items/rem_1.lean`

## Lean statement
```lean
theorem rem_1_common_init {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H) (γ : ℝ)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α : M → ℝ) (θ₁ θ₂ : ℝ)
    (hC₁ : ∀ μ ∈ V, 0 < α μ ∧ ∀ u v : H, α μ * ‖A μ u - A μ v‖ ^ 2 ≤ inner ℝ (A μ u - A μ v) (u - v))
    (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧ ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hsol : ∀ μ ∈ V, ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hu₀ : ∀ μ ∈ V, ∀ μ' ∈ V, u₀ μ = u₀ μ') (hv₀ : ∀ μ ∈ V, ∀ μ' ∈ V, v₀ μ = v₀ μ') :
    ∀ μ ∈ V, ∀ μ' ∈ V,
      let m_μ
```

## Statement explanation
The theorem `rem_1_common_init` states a parameter-stability estimate for a family of solutions, under the additional hypothesis that all parameters share the same initial data. The ambient spaces are $H$, a complete real inner product space, and $M$, a normed additive group. The set $V\subseteq M$ is the parameter set. The operator is $A:M\to H\to H$, written $A_\mu u=A(\mu,u)$, with a real parameter $\gamma$. For each $\mu\in V$, the data are $u_0(\mu)\in H$, $v_0(\mu)\in H$, and a real function $\alpha(\mu)$. The functions $x,dx,ddx:M\to\mathbb R\to H$ encode, for each parameter $\mu$, a curve $x_\mu(t)=x(\mu)(t)$ and two associated curves $dx_\mu(t)$, $ddx_\mu(t)$.

The hypotheses are the same coercivity/monotonicity and parameter-regularity assumptions as in `thm_1`. First,

$$
\forall \mu\in V,\quad 0<\alpha(\mu)
$$

and for all $u,v\in H$,

$$
\alpha(\mu)\|A_\mu u-A_\mu v\|^2
\le \langle A_\mu u-A_\mu v,\,u-v\rangle_{\mathbb R}.
$$

Second,

$$
0<\theta_1,\qquad 0<\theta_2,\qquad \theta_2\le 1,
$$

and for all $u\in H$ and all $\mu,\mu'\in V$,

$$
\|A_\mu u-A_{\mu'}u\|\le \theta_1\|\mu-\mu'\|^{\theta_2}.
$$

The hypothesis `hsol` says that for every $\mu\in V$, the triple $(x_\mu,dx_\mu,ddx_\mu)$ satisfies the solution predicate `ext_def_2` for the problem associated to $A_\mu,\gamma,u_0(\mu),v_0(\mu)$. The definition of `ext_def_2` itself is not expanded in the source; the proof uses only that `thm_1` recognizes it as the relevant solution predicate and that the first projection `(hsol μ hμ).1` provides a proof of $0<\gamma$, which `thm_1` requires. The hypotheses `hu₀` and `hv₀` say that the initial position and initial velocity are constant on $V$:

$$
\forall \mu,\mu'\in V,\quad u_0(\mu)=u_0(\mu'),\qquad
\forall \mu,\mu'\in V,\quad v_0(\mu)=v_0(\mu').
$$

The conclusion is a stability estimate for two parameters $\mu,\mu'\in V$. Define

$$
m_\mu=\sqrt{1+2\gamma^2+\frac{2}{\alpha(\mu)^2}},\qquad
m_{\mu'}=\sqrt{1+2\gamma^2+\frac{2}{\alpha(\mu')^2}},\qquad
m=\max\{m_\mu,m_{\mu'}\}.
$$

Then, for almost every $t$ with respect to Lebesgue measure on $\mathbb R$, if $0\le t$, then

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le
\left(\frac{\theta_1}{m}\right)
\left(e^{mt}-1\right)
\|\mu-\mu'\|^{\theta_2}.
$$

Thus, when all parameters have the same initial data, the difference between the two solution curves is bounded purely by the parameter difference, with an exponential factor in $t$; the initial-data term present in `thm_1` disappears.

## Lean proof
```lean
Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ) ^ 2))
      let m_μ' := Real.sqrt (1 + 2 * γ ^ 2 + 2 / ((α μ') ^ 2))
      let m := max m_μ m_μ'
      ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t →
        ‖x μ t - x μ' t‖ ≤ (θ₁ / m) * (Real.exp (m * t) - 1) * ‖μ - μ'‖ ^ θ₂ := by
  intro μ hμ μ' hμ'
  dsimp only
  rcases thm_1 V A γ u₀ v₀ α θ₁ θ₂ (hsol μ hμ).1 hC₁ hC₂ with ⟨hunique, hpairs⟩
  specialize hpairs μ hμ μ' hμ'
  dsimp only at hpairs
  rcases hpairs with ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hyy⟩
  obtain ⟨z, dz, ddz, hz, hzuniq⟩ := hunique μ hμ
  have hxy : Set.EqOn (x μ) y (Set.Ici 0) := fun t ht =>
    (hzuniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans
      (hzuniq y dy ddy hy ht)
  obtain ⟨z', dz', ddz', hz', hz'uniq⟩ := hunique μ' hμ'
  have hxy' : Set.EqOn (x μ') y' (Set.Ici 0) := fun t ht =>
    (hz'uniq (x μ') (dx μ') (ddx μ') (hsol μ' hμ') ht).symm.trans
      (hz'uniq y' dy' ddy' hy' ht)
  filter_upwards [hyy] with t ht
  intro ht_nonneg
  have ht_bound := ht ht_nonneg
  rw [← hxy ht_nonneg, ← hxy' ht_nonneg] at ht_bound
  simpa [hu₀ μ hμ μ' hμ', hv₀ μ hμ μ' hμ'] using ht_bound
```

## Proof explanation
The proof begins with `intro μ hμ μ' hμ'`, introducing arbitrary parameters $\mu,\mu'\in V$. The command `dsimp only` unfolds the local `let` definitions for $m_\mu$, $m_{\mu'}$, and $m$ in the goal, so the goal is reduced to the concrete estimate involving $m=\max\{m_\mu,m_{\mu'}\}$.

Next the proof invokes `thm_1`:

$$
\text{`thm\_1 V A γ u₀ v₀ α θ₁ θ₂ (hsol μ hμ).1 hC₁ hC₂`}.
$$

The argument `(hsol μ hμ).1` supplies the positivity $0<\gamma$ needed by `thm_1`; this is the only part of `ext_def_2` explicitly unpacked here. The theorem `thm_1` returns two components, named `hunique` and `hpairs`.

The first component `hunique` states that for every $\nu\in V$, there exists a solution triple $(z,dz,ddz)$ satisfying `ext_def_2`, and any other solution triple for the same problem agrees with it on $[0,\infty)$. The second component `hpairs` states a two-parameter stability estimate: for every $\nu,\nu'\in V$, there exist solutions $y,y'$ for the two problems and an almost-everywhere bound

$$
\|y(t)-y'(t)\|
\le
e^{mt}
\sqrt{\|u_0(\nu)-u_0(\nu')\|^2+\|v_0(\nu)-v_0(\nu')\|^2}
+\frac{\theta_1}{m}
\left(e^{mt}-1\right)
\|\nu-\nu'\|^{\theta_2}.
$$

The proof specializes `hpairs` to the chosen pair by `specialize hpairs μ hμ μ' hμ'`, then `dsimp only at hpairs` unfolds the corresponding definitions of $m_\mu$, $m_{\mu'}$, and $m$ inside that estimate.

The command `rcases hpairs with ⟨y, y', ⟨dy, ddy, hy⟩, ⟨dy', ddy', hy'⟩, hyy⟩` extracts from `thm_1` two curves $y,y'$, their auxiliary derivative curves $dy,ddy$ and $dy',ddy'$, proofs `hy` and `hy'` that they solve the two `ext_def_2` problems, and the almost-everywhere inequality `hyy`.

To compare the originally given solutions $x_\mu,x_{\mu'}$ with the solutions $y,y'$ produced by `thm_1`, the proof uses uniqueness. It obtains `⟨z, dz, ddz, hz, hzuniq⟩ := hunique μ hμ`, where $z$ is a solution for $\mu$ and `hzuniq` says that every other solution for $\mu$ equals $z$ on $[0,\infty)$. Since $x_\mu$ is a solution by `hsol μ hμ`, and $y$ is a solution by `hy`, both equal $z$ on $[0,\infty)$. The definition of `hxy` uses the chain

$$
x_\mu(t)=z(t)=y(t)\qquad(t\ge 0),
$$

which is exactly what the expression `(hzuniq (x μ) (dx μ) (ddx μ) (hsol μ hμ) ht).symm.trans (hzuniq y dy ddy hy ht)` constructs. The same reasoning for $\mu'$ gives `hxy'`:

$$
x_{\mu'}(t)=y'(t)\qquad(t\ge 0).
$$

Now the proof turns to the almost-everywhere estimate. The tactic `filter_upwards [hyy] with t ht` uses the almost-everywhere statement `hyy` from `thm_1`: it suffices to prove the desired property for an arbitrary $t$ satisfying `hyy`'s statement. The statement `ht` is the implication

$$
0\le t\Rightarrow
\|y(t)-y'(t)\|\le \cdots,
$$

so `intro ht_nonneg` assumes $0\le t$, and `have ht_bound := ht ht_nonneg` obtains the numerical bound for $y(t)-y'(t)$.

The rewrite

$$
\text{`rw [← hxy ht\_nonneg, ← hxy' ht\_nonneg] at ht\_bound`}
$$

replaces $y(t)$ by $x_\mu(t)$ and $y'(t)$ by $x_{\mu'}(t)$ in that bound, using the equalities from `hxy` and `hxy'`. Finally, `simpa [hu₀ μ hμ μ' hμ', hv₀ μ hμ μ' hμ'] using ht_bound` uses the common-initial-data hypotheses to simplify

$$
\sqrt{\|u_0(\mu)-u_0(\mu')\|^2+\|v_0(\mu)-v_0(\mu')\|^2}
$$

to $0$, because $u_0(\mu)=u_0(\mu')$ and $v_0(\mu)=v_0(\mu')$. The initial-data term in `thm_1` therefore vanishes, leaving exactly

$$
\|x_\mu(t)-x_{\mu'}(t)\|
\le
\frac{\theta_1}{m}
\left(e^{mt}-1\right)
\|\mu-\mu'\|^{\theta_2}.
$$

That closes the goal. No `linarith` or `exact` is used; the final arithmetic simplification and rewriting are performed by `simpa`.

