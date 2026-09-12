## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/cor_2.lean`

## Lean statement
```lean
theorem corollary10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (u y : ℕ → H) (ρ : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hstrong : IsStronglyConvexWith Θ ρ)
    -- TODO: derive this source-implied fact from proper lsc strong convexity once the
    -- extended-real attainment infrastructure is available.
    (hS : (Optimization.argminSet Θ).Nonempty) :
    ∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto u Filter.atTop (nhds q)
```

## Statement explanation
The theorem `corollary10` is a convergence statement for a trajectory of the inertial forward-backward algorithm, under an additional strong-convexity assumption. Let $H$ be a real inner product space which is complete, so $H$ is a real Hilbert space. The symbol $\overline{\mathbb R}$ denotes the extended real line `EReal`, with bottom $\bot=-\infty$ and top $\top=+\infty$.

The data are:

- $\phi,\Theta:H\to\overline{\mathbb R}$, extended-real functions;
- $\psi:H\to\mathbb R$, a real-valued function;
- $\mathrm{grad}\psi:H\to H$, a map denoted `gradPsi`;
- $a,b,\lambda,L_\psi\in\mathbb R$, real parameters;
- $u,y:\mathbb N\to H$, two sequences, written $u_k$ and $y_k$;
- $\rho\in\mathbb R$, the strong-convexity parameter.

The hypotheses are:

- `hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi`, which packages the standing assumptions of the inertial forward-backward setting. In the proof, only two visible parts of this package are used: the properness of $\phi$ and the identity expressing $\Theta$ as the sum of $\phi$ and the real-valued $\psi$. Other consequences are supplied by the cited lemmas below.
- `hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y`, saying that $(u,y)$ is an inertial forward-backward trajectory for those data.
- `hstrong : IsStronglyConvexWith Θ ρ`, saying that $\Theta$ is strongly convex with modulus $\rho$. In particular, the first component of this hypothesis provides positivity of $\rho$.
- `hS : (Optimization.argminSet Θ).Nonempty`, saying that the set of minimizers of $\Theta$ is nonempty. This is assumed rather than derived.

The conclusion is:

$$
\exists q\in \mathrm{argminSet}\Theta,\qquad
u_k \to q \quad \text{as } k\to\infty,
$$

where the convergence is in the norm topology on $H$. Thus the theorem says that if the extended-real objective $\Theta$ is strongly convex and has at least one minimizer, then an inertial forward-backward trajectory converges to some minimizer of $\Theta$.

## Lean proof
```lean
by
  rcases hS with ⟨q, hq⟩
  obtain ⟨x0, hx0⟩ := hH.phi_proper.2
  have hx0top : Θ x0 < ⊤ := by
    rw [hH.theta_eq]
    exact EReal.add_lt_top (ne_of_lt hx0) (EReal.coe_ne_top _)
  have hqtop : Θ q < ⊤ := by
    rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
    rw [hq]
    exact lt_of_le_of_lt (sInf_le ⟨x0, rfl⟩) hx0top
  have hqdom : q ∈ ERealFunction.dom Θ := by
    rw [ERealFunction.mem_dom_iff]
    exact hqtop
  have hqbot : Θ q ≠ ⊥ := theta_ne_bot phi Θ psi gradPsi a b lam Lpsi hH q
  have hqcoe : ((Θ q).toReal : EReal) = Θ q :=
    EReal.coe_toReal (ne_of_lt hqdom) hqbot
  have hdom : ∀ k : ℕ, u (k + 1) ∈ ERealFunction.dom Θ := fun k ↦
    trajectory_theta_mem_dom phi Θ psi gradPsi a b lam Lpsi u y hH hIFB k
  have hbot : ∀ k : ℕ, Θ (u (k + 1)) ≠ ⊥ := fun k ↦
    theta_ne_bot phi Θ psi gradPsi a b lam Lpsi hH (u (k + 1))
  have hgrowth : ∀ k : ℕ, Θ q + ((ρ / 4 * ‖u (k + 1) - q‖ ^ 2 : ℝ) : EReal) ≤
      Θ (u (k + 1)) := fun k ↦
    strongConvex_midpoint_growth Θ ρ hstrong hq hqdom (hdom k) hqbot (hbot k)
  have hobj : Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds (Θ q)) := by
    rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
    rw [hq]
    exact (proposition6 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB).1
  have hobj_succ : Filter.Tendsto (fun k ↦ Θ (u (k + 1))) Filter.atTop (nhds (Θ q)) := by
    simpa [Function.comp_def] using hobj.comp (Filter.tendsto_add_atTop_nat 1)
  have hnorm : Filter.Tendsto (fun k ↦ ‖u (k + 1) - q‖) Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hc : 0 < ρ / 4 * ε ^ 2 := by
      have := hstrong.1
      positivity
    have hlt : Θ q < Θ q + ((ρ / 4 * ε ^ 2 : ℝ) : EReal) := by
      rw [← hqcoe, ← EReal.coe_add]
      exact_mod_cast (by linarith : (Θ q).toReal < (Θ q).toReal + ρ / 4 * ε ^ 2)
    rcases Filter.eventually_atTop.1
        (hobj_succ.eventually (Iio_mem_nhds hlt)) with ⟨N, hN⟩
    refine ⟨N, fun k hk ↦ ?_⟩
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    by_contra hnot
    have hle : ε ≤ ‖u (k + 1) - q‖ := le_of_not_gt hnot
    have hsquare : ε ^ 2 ≤ ‖u (k + 1) - q‖ ^ 2 := by nlinarith [sq_nonneg (‖u (k + 1) - q‖ - ε)]
    have hmul : ρ / 4 * ε ^ 2 ≤ ρ / 4 * ‖u (k + 1) - q‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left hsquare
      linarith [hstrong.1]
    have headd : Θ q + ((ρ / 4 * ε ^ 2 : ℝ) : EReal) ≤
        Θ q + ((ρ / 4 * ‖u (k + 1) - q‖ ^ 2 : ℝ) : EReal) := by
      simpa [add_comm] using add_le_add_left (EReal.coe_le_coe_iff.mpr hmul) (Θ q)
    exact (not_lt_of_ge (headd.trans (hgrowth k))) (hN k hk)
  have hu_succ : Filter.Tendsto (fun k ↦ u (k + 1)) Filter.atTop (nhds q) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  exact ⟨q, hq, (Filter.tendsto_add_atTop_iff_nat 1).mp hu_succ⟩
```

## Proof explanation
The proof begins by destructing the assumed nonemptiness of the minimizer set. The tactic `rcases hS with ⟨q, hq⟩` chooses a point $q$ and a proof $hq$ that

$$
q\in \mathrm{argminSet}\Theta.
$$

The rest of the proof is devoted to showing that the original sequence $u_k$ converges to this particular minimizer $q$.

Next, the proof extracts a point where $\phi$ is not infinite above. The command `obtain ⟨x0, hx0⟩ := hH.phi_proper.2` uses the properness part of the `IFBHypothesis` package to obtain $x_0$ and a proof $hx_0$, used in the form $\phi(x_0)\lt \top$. The block proving `hx0top` shows

$$
\Theta(x_0)<\top.
$$

It uses `hH.theta_eq`, which identifies $\Theta$ with the sum of $\phi$ and the real-valued function $\psi$ coerced into $\overline{\mathbb R}$. Then `EReal.add_lt_top` is applied: since $hx_0$ implies $\phi(x_0)\neq\top$, and since a real number coerced to $\overline{\mathbb R}$ is never $\top$ by `EReal.coe_ne_top`, their sum is $\lt \top$. Hence $\Theta(x_0)\lt \top$.

The next step proves `hqtop`, namely

$$
\Theta(q)<\top.
$$

The proof rewrites $hq$ using `Optimization.mem_argminSet_iff_eq_sInf`. That theorem says that, in a complete linear order, a point $x$ lies in the argmin set of $f$ exactly when

$$
f(x)=\inf(\mathrm{range} f).
$$

Applying it to $f=\Theta$ and $x=q$, the hypothesis $hq$ becomes

$$
\Theta(q)=\inf(\mathrm{range}\Theta).
$$

Since $\Theta(x_0)$ belongs to $\mathrm{range}\Theta$, the lemma `sInf_le` gives

$$
\inf(\mathrm{range}\Theta)\le \Theta(x_0).
$$

Together with $\Theta(x_0)\lt \top$, this yields $\Theta(q)\lt \top$. The proof then converts this into membership in the extended-real domain: `hqdom` uses `ERealFunction.mem_dom_iff`, which states that

$$
q\in \mathrm{dom}\Theta \iff \Theta(q)<\top.
$$

So $q$ lies in the domain of $\Theta$.

The proof also needs that the value $\Theta(q)$ is not bottom. The fact `hqbot` is obtained by applying `theta_ne_bot` to $q$. That lemma says that under the hypothesis `hH`, for every $x$,

$$
\Theta(x)\neq \bot.
$$

Thus $\Theta(q)\neq \bot$. Then `hqcoe` uses `EReal.coe_toReal`. This lemma says that if an extended-real value is finite above and not bottom, then coercing its real part back into $\overline{\mathbb R}$ recovers the value. In symbols,

$$
\bigl((\Theta(q))_{\mathrm{toReal}}:\overline{\mathbb R}\bigr)=\Theta(q).
$$

This is important because later inequalities need to treat $\Theta(q)$ as a real number.

Next, the proof records domain and bottom facts along the trajectory. For every $k$, `hdom k` applies `trajectory_theta_mem_dom`, which says that under `hH` and `hIFB`,

$$
u_{k+1}\in \mathrm{dom}\Theta,
$$

equivalently $\Theta(u_{k+1})\lt \top$. Also, `hbot k` applies `theta_ne_bot` again, giving

$$
\Theta(u_{k+1})\neq \bot.
$$

The central quantitative estimate is `hgrowth`. It is obtained by applying `strongConvex_midpoint_growth` to $\Theta$, $\rho$, the strong-convexity hypothesis `hstrong`, the minimizer $q$, the domain memberships of $q$ and $u_{k+1}$, and the non-bottom facts for $\Theta(q)$ and $\Theta(u_{k+1})$. The lemma gives, for every $k$,

```math
\Theta(q)+\left(\frac{\rho}{4}\|u_{k+1}-q\|^2:\overline{\mathbb R}\right)
\le \Theta(u_{k+1}).
```

Thus strong convexity supplies a quadratic lower bound for $\Theta(u_{k+1})$ in terms of its distance from the minimizer $q$.

The proof then obtains convergence of the objective values. The fact `hobj` first rewrites $hq$ using `Optimization.mem_argminSet_iff_eq_sInf`, turning it into

$$
\Theta(q)=\inf(\mathrm{range}\Theta).
$$

Then the first part of `proposition6` is used. That theorem assumes the same hypotheses `hH` and `hIFB` and states three things: first, that

$$
\Theta(u_k)\to \inf(\mathrm{range}\Theta);
$$

second, that every sequential weak cluster point of $u_k$ is a minimizer of $\Theta$; and third, that if the argmin set of $\Theta$ is empty, then $`\|u_k\|\to\infty`$. Only the first conclusion is used here. Combining it with$\Theta(q)=\inf(\mathrm{range}\Theta)$, the proof obtains

$$
\Theta(u_k)\to \Theta(q).
$$

The fact `hobj_succ` shifts this convergence by one index. Since $k\mapsto k+1$ tends to infinity, the composition rule for limits gives

$$
\Theta(u_{k+1})\to \Theta(q).
$$

This is the convergence that will be used to force the distance $`\|u_{k+1}-q\|`$ to tend to zero.

The proof of `hnorm` is the main analytic step. It shows

```math
\|u_{k+1}-q\|\to 0.
```

The command `rw [Metric.tendsto_atTop]` converts the goal into the usual $\varepsilon\text{-}N$ formulation: for every $\varepsilon\gt 0$, there is $N$ such that for every $k\ge N$,

```math
\mathrm{dist}\bigl(\|u_{k+1}-q\|,0\bigr)<\varepsilon.
```

The command `intro` introduces an arbitrary $\varepsilon$ and its positivity hypothesis. Let

$$
c=\frac{\rho}{4}\varepsilon^2.
$$

The proof shows $c\gt 0$. This uses `hstrong.1`, the part of the strong-convexity hypothesis giving positivity of $\rho$, together with positivity of $\varepsilon^2$. The proof then establishes

$$
\Theta(q)<\Theta(q)+c
$$

in $\overline{\mathbb R}$. The equality `hqcoe`, which identifies $\Theta(q)$ with the coercion of its real part, and `EReal.coe_add`, which collects real additions under a single coercion, reduce this extended-real inequality to the real inequality

$$
(\Theta(q))_{\mathrm{toReal}}
<
(\Theta(q))_{\mathrm{toReal}}+\frac{\rho}{4}\varepsilon^2,
$$

which follows from $c\gt 0$ by `linarith`.

Because $\Theta(u_{k+1})\to \Theta(q)$, and because the interval below $\Theta(q)+c$ is a neighborhood of $\Theta(q)$, eventually

$$
\Theta(u_{k+1})<\Theta(q)+c.
$$

The proof converts this eventual statement into an index $N$ via `Filter.eventually_atTop.1`. For $k\ge N$, it then proves the desired norm inequality.

It argues by contradiction using `by_contra`. After simplifying the distance to

```math
\|u_{k+1}-q\|,
```

suppose the desired inequality fails. Then

```math
\varepsilon\le \|u_{k+1}-q\|.
```

Squaring gives

```math
\varepsilon^2\le \|u_{k+1}-q\|^2.
```

This is proved by `nlinarith` using nonnegativity of a square. Multiplying by the nonnegative quantity $\rho/4$ gives

```math
\frac{\rho}{4}\varepsilon^2
\le
\frac{\rho}{4}\|u_{k+1}-q\|^2.
```

The nonnegativity of $\rho/4$ again comes from `hstrong.1`. Coercing this real inequality into $\overline{\mathbb R}$ via `EReal.coe_le_coe_iff` and adding $\Theta(q)$ to both sides gives

```math
\Theta(q)+c
\le
\Theta(q)+\left(\frac{\rho}{4}\|u_{k+1}-q\|^2:\overline{\mathbb R}\right).
```

Combining this with the strong-convexity growth estimate `hgrowth k` yields

$$
\Theta(q)+c\le \Theta(u_{k+1}).
$$

But the eventual inequality from the choice of $N$ says

$$
\Theta(u_{k+1})<\Theta(q)+c.
$$

These contradict each other. Therefore the assumption that the norm is at least $\varepsilon$ was false, so

```math
\|u_{k+1}-q\|<\varepsilon.
```

Since $\varepsilon\gt 0$ was arbitrary, this proves `hnorm`, namely $`\|u_{k+1}-q\|\to 0`$.

Finally, the proof converts this norm convergence into convergence of the shifted sequence. The theorem `tendsto_iff_norm_sub_tendsto_zero` says that convergence to $q$ is equivalent to the norm of the difference tending to zero. Applying it with `hnorm` gives

$$
u_{k+1}\to q.
$$

Then `Filter.tendsto_add_atTop_iff_nat` for the shift by $1$ says that convergence of the shifted sequence $u_{k+1}$ to $q$ is equivalent to convergence of the original sequence $u_k$ to $q$. The proof uses the direction from shifted to original, obtaining

$$
u_k\to q.
$$

The existential conclusion is then closed with the chosen minimizer $q$, the proof `hq` that $q\in \mathrm{argminSet}\Theta$, and the just-proved convergence $u_k\to q$.

