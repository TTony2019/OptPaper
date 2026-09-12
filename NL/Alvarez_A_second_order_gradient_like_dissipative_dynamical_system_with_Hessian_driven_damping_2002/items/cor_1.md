## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/cor_1.lean`

## Lean statement
```lean
theorem coercive_potential_bounds_din {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ)
    (x : ℝ → H) (hΦ : AssumptionH H Φ)
    (hΦreg : ContDiff ℝ 2 Φ)
    (hxreg : ContDiff ℝ 2 x)
    (hcoercive : ERealFunction.Coercive (fun z => (Φ z : EReal)))
    (hsol : IsDINTrajectory H Φ α β x) :
    (∃ R : ℝ, ∀ t, 0 ≤ t → ‖x t‖ ≤ R) ∧
      Bornology.IsBounded ((deriv x) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((deriv (deriv x)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => gradient Φ (x t)) '' Set.Ici (0 : ℝ)) ∧
      Bornology.IsBounded ((fun t => fderiv ℝ (gradient Φ) (x t)) '' Set.Ici (0 : ℝ)) ∧
      Tendsto (deriv x) atTop (nhds 0) ∧ Tendsto (deriv (deriv x)) atTop (nhds 0) ∧
      Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0)
```

## Statement explanation
The theorem `coercive_potential_bounds_din` is stated in a real Hilbert space $H$. Its data are a potential $\Phi:H\to\mathbb R$, two real parameters $\alpha,\beta$, and a curve $x:\mathbb R\to H$. The hypotheses are:

- `hΦ : AssumptionH H Φ`, a bundled standing assumption on $\Phi$; the supplied source does not expand its internal definition.
- `hΦreg : ContDiff ℝ 2 Φ`, saying that $\Phi$ is $C^2$.
- `hxreg : ContDiff ℝ 2 x`, saying that the trajectory $x$ is $C^2$.
- `hcoercive : ERealFunction.Coercive (fun z => (Φ z : EReal))`, saying that the extended-real-valued function $z\mapsto(\Phi z:\operatorname{EReal})$ is coercive, i.e. it tends to $+\infty$ as $z$ tends to infinity.
- `hsol : IsDINTrajectory H Φ α β x`, saying that $x$ is a trajectory of the DIN system for the potential $\Phi$ and the parameters $\alpha,\beta$. In the proof, the only visible consequences of this hypothesis are that $\alpha>0$ and $\beta>0$.

The conclusion is a long conjunction. First, there is a real number $R$ such that every nonnegative time $t$ satisfies

$$
\|x(t)\|\le R.
$$

Thus the whole forward trajectory $x$ on $[0,\infty)$ stays in a bounded set. Second, each of the following images is bounded:

$$
\operatorname{deriv}x\bigl( [0,\infty) \bigr),\qquad
\operatorname{deriv}(\operatorname{deriv}x)\bigl( [0,\infty) \bigr),
$$

$$
t\mapsto \nabla\Phi(x(t))\quad\text{on } [0,\infty),
\qquad
t\mapsto \operatorname{fderiv}_{\mathbb R}(\nabla\Phi)(x(t))\quad\text{on } [0,\infty).
$$

Here $\operatorname{deriv}x$ is the velocity, $\operatorname{deriv}(\operatorname{deriv}x)$ is the acceleration, $\nabla\Phi$ is the gradient of $\Phi$, and $\operatorname{fderiv}_{\mathbb R}(\nabla\Phi)(x(t))$ is the Fréchet derivative of the gradient at $x(t)$, i.e. the Hessian operator at that point. Finally, as $t\to+\infty$, the velocity, the acceleration, and the gradient along the trajectory all tend to $0$:

$$
\operatorname{deriv}x(t)\to 0,\qquad
\operatorname{deriv}(\operatorname{deriv}x)(t)\to 0,\qquad
\nabla\Phi(x(t))\to 0.
$$

In ordinary language, the theorem says that a coercive potential forces the forward DIN trajectory to be bounded, and then the standard DIN asymptotic conclusions give bounded velocity, acceleration, gradient, and Hessian, with the velocity, acceleration, and gradient decaying to zero.

## Lean proof
```lean
by
  have hα : 0 < α := hsol.1
  have hβ : 0 < β := hsol.2.1
  -- The middle Liapounov coefficient `αβ + 1` lies in the admissible range.
  let ell : ℝ := α * β + 1
  have hell_pos : 0 < ell := by
    dsimp [ell]
    nlinarith [mul_pos hα hβ]
  have hs2 : (Real.sqrt (α * β)) ^ 2 = α * β :=
    Real.sq_sqrt (mul_nonneg hα.le hβ.le)
  have hsnn : 0 ≤ Real.sqrt (α * β) := Real.sqrt_nonneg _
  have hell_low : (1 - Real.sqrt (α * β)) ^ 2 ≤ ell := by
    dsimp [ell]
    nlinarith [hs2, hsnn]
  have hell_high : ell ≤ (1 + Real.sqrt (α * β)) ^ 2 := by
    dsimp [ell]
    nlinarith [hs2, hsnn]
  -- The energy `E_t = (αβ+1)Φ(x t) + ½‖ẋ+β∇Φ‖²` is decreasing on `[0,∞)`.
  obtain ⟨_, hanti, _, _⟩ :=
    (din_global_properties_part_ii Φ hΦ α β hα hβ (x 0) (deriv x 0) x rfl rfl hsol hxreg).1
      ell hell_low hell_high
  -- Hence `Φ(x t) ≤ E(0)/(αβ+1)` for every `t ≥ 0`.
  have hΦbound : ∀ t : ℝ, 0 ≤ t → Φ (x t) ≤ dinForwardEnergy Φ β ell x 0 / ell := by
    intro t ht
    have hEt : dinForwardEnergy Φ β ell x t ≤ dinForwardEnergy Φ β ell x 0 :=
      hanti (by simp) (by simpa using ht) ht
    have hfac : ell * Φ (x t) ≤ dinForwardEnergy Φ β ell x t := by
      have hnonneg : (0 : ℝ) ≤ (1 / 2) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2 := by
        positivity
      simp only [dinForwardEnergy]
      linarith
    exact (le_div_iff₀' hell_pos).mpr (le_trans hfac hEt)
  -- Coercivity turns that upper bound into a bound on `‖x t‖`.
  have hcoer : ∀ c : ℝ, ∃ a : ℝ, ∀ z : H, a ≤ ‖z‖ → c < Φ z := by
    intro c
    have h : ∀ᶠ z in Bornology.cobounded H, (c : EReal) < (Φ z : EReal) :=
      (EReal.tendsto_nhds_top_iff_real.mp hcoercive) c
    rw [Filter.hasBasis_cobounded_norm.eventually_iff] at h
    obtain ⟨a, -, ha⟩ := h
    exact ⟨a, fun z hz => EReal.coe_lt_coe_iff.mp (ha hz)⟩
  obtain ⟨a, ha⟩ := hcoer (dinForwardEnergy Φ β ell x 0 / ell)
  have hle_a : ∀ t : ℝ, 0 ≤ t → ‖x t‖ ≤ a := by
    intro t ht
    by_contra hcon
    have hlt : a < ‖x t‖ := not_le.mp hcon
    exact (not_lt.mpr (hΦbound t ht)) (ha (x t) hlt.le)
  have hxbound : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max a 0, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact le_trans (hle_a t ht) (le_max_left a 0)
  -- Now Theorem 2.1(iii) supplies all the remaining conclusions.
  obtain ⟨hvB, haccB, hgradB, hhessB, hvT, haccT, hgradT⟩ :=
    din_global_properties_part_iii Φ hΦ α β hα hβ (x 0) (deriv x 0) x rfl rfl hsol hxreg hxbound
  exact ⟨⟨max a 0, fun t ht => le_trans (hle_a t ht) (le_max_left a 0)⟩,
    hvB, haccB, hgradB, hhessB, hvT, haccT, hgradT⟩
```

## Proof explanation
The proof first extracts the positivity of the two parameters from the trajectory hypothesis. Since `hsol : IsDINTrajectory H Φ α β x`, the projections `hsol.1` and `hsol.2.1` give

$$
0<\alpha,\qquad 0<\beta.
$$

These are then used as the positivity hypotheses required by the previously established DIN theorems.

Next the proof chooses the Liapounov coefficient

$$
\ell=\alpha\beta+1.
$$

It proves $\ell>0$ by unfolding the definition of $\ell$ and using `nlinarith` with the fact that $\alpha\beta>0$, obtained from `mul_pos hα hβ`.

It then verifies that this $\ell$ lies in the admissible interval for the forward energy. Let

$$
s=\sqrt{\alpha\beta}.
$$

The proof establishes

$$
s^2=\alpha\beta
$$

using `Real.sq_sqrt` and the nonnegativity of $\alpha\beta$, and also

$$
0\le s
$$

using `Real.sqrt_nonneg`. With these two facts, `nlinarith` proves

$$
(1-\sqrt{\alpha\beta})^2\le \ell
$$

and

$$
\ell\le (1+\sqrt{\alpha\beta})^2.
$$

Indeed, writing $s=\sqrt{\alpha\beta}$, we have $\ell=1+s^2$, while

$$
(1-s)^2=1-2s+s^2\le 1+s^2
$$

because $s\ge0$, and

$$
1+s^2\le 1+2s+s^2=(1+s)^2
$$

again because $s\ge0$.

The proof now invokes `din_global_properties_part_ii`. Specialized to the present data, that theorem assumes $\Phi$, the standing assumption `AssumptionH H Φ`, positive parameters $\alpha,\beta$, a $C^2$ trajectory $x$ satisfying the DIN trajectory condition, and initial conditions compatible with $x$. It concludes, among other things, that for every $\ell$ in the interval

$$
(1-\sqrt{\alpha\beta})^2\le \ell\le(1+\sqrt{\alpha\beta})^2,
$$

there is a real $l$ such that the forward energy

$$
E_\ell(t)=\ell\Phi(x(t))+\frac12\|\operatorname{deriv}x(t)+\beta\nabla\Phi(x(t))\|^2
$$

is antitone on $[0,\infty)$, is bounded below on $[0,\infty)$, and converges to $l$ as $t\to+\infty$. It also gives $L^2$-integrability of the velocity and of the gradient on $(0,\infty)$, convergence of $\Phi(x(t))$, and convergence of $\operatorname{deriv}x(t)+\beta\nabla\Phi(x(t))$ to $0$. In the proof here, only the first part is used, and from it only the antitone statement is retained:

$$
E_\ell \text{ is antitone on } [0,\infty).
$$

The Lean line
```lean
obtain ⟨_, hanti, _, _⟩ :=
  (din_global_properties_part_ii ...).1 ell hell_low hell_high
```
selects this antitone property and discards the existence of the limit, the lower bound, and the convergence information.

From antitonicity the proof derives the upper bound

$$
\Phi(x(t))\le \frac{E_\ell(0)}{\ell}
$$

for every $t\ge0$. Fix such a $t$. The command `intro t ht` introduces $t$ and the hypothesis $0\le t$. The antitone property gives

$$
E_\ell(t)\le E_\ell(0).
$$

Indeed, `hanti (by simp) (by simpa using ht) ht` applies antitonicity with $0\le t$; the first two arguments verify that $0$ and $t$ lie in $[0,\infty)$, and the third is $0\le t$. Since

$$
E_\ell(t)=\ell\Phi(x(t))+\frac12\|\operatorname{deriv}x(t)+\beta\nabla\Phi(x(t))\|^2
$$

and the second summand is nonnegative, the proof obtains

$$
\ell\Phi(x(t))\le E_\ell(t).
$$

The nonnegativity of the second summand is discharged by `positivity`, and then `simp only [dinForwardEnergy]` unfolds the definition while `linarith` uses the nonnegativity to conclude the inequality. Combining this with $E_\ell(t)\le E_\ell(0)$ gives

$$
\ell\Phi(x(t))\le E_\ell(0).
$$

Because $\ell>0$, the proof divides by $\ell$, using `le_div_iff₀' hell_pos`, to obtain

$$
\Phi(x(t))\le \frac{E_\ell(0)}{\ell}.
$$

The next step converts coercivity into a norm bound. The hypothesis `hcoercive` says that the extended-real-valued function $z\mapsto(\Phi z:\operatorname{EReal})$ is coercive. Through `EReal.tendsto_nhds_top_iff_real`, this yields, for every real $c$,

$$
\forall^{\mathrm{f}} z\text{ in }\operatorname{cobounded}H,\quad (c:\operatorname{EReal})<(\Phi z:\operatorname{EReal}).
$$

Here `Bornology.cobounded H` is the filter describing $z$ tending to infinity in the bornological sense. Rewriting with `Filter.hasBasis_cobounded_norm.eventually_iff` turns this eventual statement into the existence of a radius $a$ such that

$$
a\le \|z\|\implies (c:\operatorname{EReal})<(\Phi z:\operatorname{EReal}).
$$

Using `EReal.coe_lt_coe_iff`, this becomes the real inequality

$$
a\le \|z\|\implies c<\Phi(z).
$$

Thus the proof obtains the real-coercivity statement

$$
\forall c\in\mathbb R,\ \exists a\in\mathbb R,\ \forall z\in H,\quad
a\le \|z\|\implies c<\Phi(z).
$$

Applying this with

$$
c=\frac{E_\ell(0)}{\ell},
$$

the proof gets a radius $a$ such that whenever $a\le \|z\|$,

$$
\frac{E_\ell(0)}{\ell}<\Phi(z).
$$

It then shows that for every $t\ge0$,

$$
\|x(t)\|\le a.
$$

The argument is by contradiction. Suppose $\|x(t)\|\not\le a$. Then `not_le.mp` gives

$$
a<\|x(t)\|,
$$

hence $a\le \|x(t)\|$, and the coercivity consequence gives

$$
\frac{E_\ell(0)}{\ell}<\Phi(x(t)).
$$

But the earlier energy bound gives

$$
\Phi(x(t))\le \frac{E_\ell(0)}{\ell},
$$

so this is impossible. The Lean expression `not_lt.mpr (hΦbound t ht)` turns the upper bound into the negation of the strict lower bound, and `ha (x t) hlt.le` supplies the strict lower bound. The contradiction proves $\|x(t)\|\le a$.

The proof then packages this pointwise norm bound as bornological boundedness of the image of $x$. It applies `isBounded_iff_forall_norm_le.mpr`, which says that a set in a normed space is bounded if all its elements have norm at most some fixed real number. The chosen bound is

$$
\max(a,0).
$$

For any $z$ in the image $x( [0,\infty) )$, there is $t\ge0$ with $z=x(t)$. Then

$$
\|z\|=\|x(t)\|\le a\le \max(a,0).
$$

The `rintro z ⟨t, ht, rfl⟩` destructs the image membership, and `le_trans` with `le_max_left` finishes the bound. This produces

$$
\operatorname{Bornology.IsBounded}\bigl(x( [0,\infty) )\bigr).
$$

Finally the proof invokes `din_global_properties_part_iii`. Specialized to the present data, that theorem assumes the same hypotheses as before and additionally assumes that the forward trajectory image $x( [0,\infty) )$ is bounded. Under that extra boundedness hypothesis it concludes exactly the remaining assertions needed here:

$$
\operatorname{deriv}x( [0,\infty) ) \text{ is bounded},
$$

$$
\operatorname{deriv}(\operatorname{deriv}x)( [0,\infty) ) \text{ is bounded},
$$

$$
t\mapsto \nabla\Phi(x(t)) \text{ is bounded on } [0,\infty),
$$

$$
t\mapsto \operatorname{fderiv}_{\mathbb R}(\nabla\Phi)(x(t)) \text{ is bounded on } [0,\infty),
$$

and

$$
\operatorname{deriv}x(t)\to0,\qquad
\operatorname{deriv}(\operatorname{deriv}x)(t)\to0,\qquad
\nabla\Phi(x(t))\to0
$$

as $t\to+\infty$. The proof obtains these seven facts from `din_global_properties_part_iii`.

The final `exact` assembles the target conjunction. Its first component is the existential bound on $\|x(t)\|$, using $R=\max(a,0)$ and the already proved pointwise inequality. The remaining seven components are precisely the four boundedness statements and the three convergence statements supplied by `din_global_properties_part_iii`. The hypothesis `hΦreg` is not used in the supplied proof; the cited theorems are invoked with `hΦ`, `hsol`, and `hxreg`.

