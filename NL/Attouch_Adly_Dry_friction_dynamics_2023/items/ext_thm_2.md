## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_thm_2.lean`

## Lean statement
```lean
theorem time_scaling_and_averaging_theorem {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (z : ℝ → H) (τ dτ ddτ : ℝ → ℝ) (x y dx dy ddx : ℝ → H) (s₀ : ℝ)
    (hy : y = timeScaledTrajectory z τ) (haverage : IsWeightedAverageOn τ dτ x y dx s₀)
    (hdτ_pos : ∀ s ∈ Set.Ici s₀, 0 < dτ s)
    (hdy : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hddx : ∀ s ∈ Set.Ici s₀, HasDerivAt dx (ddx s) s)
    (hddτ : ∀ s ∈ Set.Ici s₀, HasDerivAt dτ (ddτ s) s) :
    (∀ s ∈ Set.Ici s₀, x s = x s₀ + ∫ u in s₀..s, dx u) ∧
      ∀ s ∈ Set.Ioi s₀,
        ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s) = 0
```

## Statement explanation
The theorem is stated in a complete real normed vector space $H$, i.e. a real Banach space. It involves a real-valued parameter $s_0$, functions

$$
z:\mathbb R\to H,\qquad \tau,d\tau,dd\tau:\mathbb R\to\mathbb R,
$$

and functions

$$
x,y,dx,dy,ddx:\mathbb R\to H.
$$

The hypotheses are the following. First, $y$ is assumed to be the time-scaled trajectory of $z$ by $\tau$, written in Lean as $y=\operatorname{timeScaledTrajectory} z \tau$. The definition of $\operatorname{timeScaledTrajectory}$ is not provided in the source, so this hypothesis is only identified here as saying that $y$ is obtained from $z$ by the time change $\tau$. Second, the hypothesis

$$
\operatorname{IsWeightedAverageOn} \tau\,d\tau\,x\,y\,dx\,s_0
$$

is assumed. The definition of this predicate is not given in the provided source, but the proof unpacks it. The part actually used in the proof says that for every $s\in [s_0,\infty)$,

$$
\operatorname{HasDerivAt} x (dx(s)) s
$$

and

$$
dx(s)+d\tau(s)^{-1}\cdot (x(s)-y(s))=0.
$$

Here $\cdot$ denotes scalar multiplication in $H$. The other two components unpacked in the proof, named `hτ` and `hxy0`, are not used later. Third, $d\tau$ is assumed positive on $[s_0,\infty)$:

$$
\forall s\in [s_0,\infty),\quad d\tau(s)>0.
$$

Fourth, $y$ has derivative $dy(s)$ at each $s\in [s_0,\infty)$, $dx$ has derivative $ddx(s)$ at each $s\in [s_0,\infty)$, and $d\tau$ has derivative $dd\tau(s)$ at each $s\in [s_0,\infty)$:

$$
\forall s\in [s_0,\infty),\quad \operatorname{HasDerivAt} y (dy(s)) s,
$$

$$
\forall s\in [s_0,\infty),\quad \operatorname{HasDerivAt} dx (ddx(s)) s,
$$

$$
\forall s\in [s_0,\infty),\quad \operatorname{HasDerivAt} d\tau (dd\tau(s)) s.
$$

The conclusion is a conjunction of two statements. The first says that for every $s\in [s_0,\infty)$,

$$
x(s)=x(s_0)+\int_{s_0}^{s} dx(u)\,du.
$$

Thus $x$ is recovered from its derivative $dx$ by the fundamental theorem of calculus on the interval $[s_0,s]$. The second says that for every $s\in (s_0,\infty)$,

$$
ddx(s)-\frac{dd\tau(s)}{(d\tau(s))^2}\cdot (x(s)-y(s))
+\frac{1}{d\tau(s)}\cdot (dx(s)-dy(s))=0.
$$

This is the derivative of the ODE

$$
dx(s)+d\tau(s)^{-1}\cdot (x(s)-y(s))=0
$$

supplied by the weighted-average hypothesis. The hypothesis $y=\operatorname{timeScaledTrajectory} z \tau$ is not used in the proof.

## Lean proof
```lean
by
  rcases haverage with ⟨hτ, hxy0, haverage⟩
  have hdx : ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s := fun s hs =>
    (haverage s hs).1
  have hode : ∀ s ∈ Set.Ici s₀, dx s + (dτ s)⁻¹ • (x s - y s) = 0 := fun s hs =>
    (haverage s hs).2
  constructor
  · intro s hs
    have hsle : s₀ ≤ s := hs
    have hxDeriv : ∀ u ∈ Set.uIcc s₀ s, HasDerivAt x (dx u) u := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact hdx u (Set.mem_Ici.mpr hu.1)
    have hdxCont : ContinuousOn dx (Set.uIcc s₀ s) := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact (hddx u (Set.mem_Ici.mpr hu.1)).continuousAt.continuousWithinAt
    have hdxInt : IntervalIntegrable dx MeasureTheory.volume s₀ s := hdxCont.intervalIntegrable
    have hftc : ∫ u in s₀..s, dx u = x s - x s₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hxDeriv hdxInt
    rw [hftc]
    abel
  · intro s hs
    have hsIci : s ∈ Set.Ici s₀ := Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hs))
    have hdτne : dτ s ≠ 0 := ne_of_gt (hdτ_pos s hsIci)
    let F : ℝ → H := fun t => dx t + (dτ t)⁻¹ • (x t - y t)
    have hinv : HasDerivAt (fun t : ℝ => (dτ t)⁻¹)
        (-ddτ s / (dτ s) ^ 2) s :=
      (hddτ s hsIci).inv hdτne
    have hdiff : HasDerivAt (fun t : ℝ => x t - y t) (dx s - dy s) s :=
      (hdx s hsIci).sub (hdy s hsIci)
    have hFderiv : HasDerivAt F
        (ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s)) s := by
      dsimp [F]
      convert (hddx s hsIci).add (hinv.smul hdiff) using 1
      all_goals simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, div_eq_mul_inv]
    have hFzero : (fun _ : ℝ => (0 : H)) =ᶠ[nhds s] F := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      simpa [F] using (hode t (le_of_lt ht)).symm
    have hconst : HasDerivAt (fun _ : ℝ => (0 : H))
        (ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s)) s :=
      hFderiv.congr_of_eventuallyEq hFzero
    exact hconst.unique (hasDerivAt_const s (0 : H))
```

## Proof explanation
The proof begins with

$$
\texttt{rcases haverage with }\langle h\tau, hxy0, haverage\rangle.
$$

This destructs the predicate $\operatorname{IsWeightedAverageOn} \tau\,d\tau\,x\,y\,dx\,s_0$ into three components. The first two, `hτ` and `hxy0`, are not used later. The third component, now also named `haverage`, is the only part needed. From it the proof extracts two facts. First,

$$
\texttt{hdx}:\quad \forall s\in [s_0,\infty),\ \operatorname{HasDerivAt} x (dx(s)) s,
$$

by taking the first coordinate of `(haverage s hs)`. Second,

$$
\texttt{hode}:\quad \forall s\in [s_0,\infty),\quad dx(s)+d\tau(s)^{-1}\cdot (x(s)-y(s))=0,
$$

by taking the second coordinate of `(haverage s hs)`. The command `have` introduces these named facts for later use.

The command

$$
\texttt{constructor}
$$

splits the conjunction in the goal into two subgoals: first the integral identity for $x$, then the differentiated ODE.

For the first subgoal, the proof fixes $s\in [s_0,\infty)$ by `intro s hs`. Since `hs` is membership in $\operatorname{Ici} s_0$, it gives $s_0\le s$, named `hsle`. The proof then shows that $x$ has derivative $dx(u)$ at every $u\in [s_0,s]$. It uses `Set.uIcc_of_le hsle` to rewrite the unordered interval $\operatorname{uIcc} s_0 s$ as the ordinary interval $[s_0,s]$. For $u\in [s_0,s]$, one has $u\in [s_0,\infty)$, so `hdx u` applies.

Next the proof shows that $dx$ is continuous on $[s_0,s]$. For each $u\in [s_0,s]$, the hypothesis `hddx` says that $dx$ is differentiable at $u$, with derivative $ddx(u)$. Differentiability at a point implies continuity at that point, and continuity at a point implies continuity within the interval. Thus `hdxCont` is obtained. From continuity on the compact interval $[s_0,s]$, the lemma `ContinuousOn.intervalIntegrable` gives that $dx$ is interval integrable over $[s_0,s]$, named `hdxInt`.

The proof then invokes the vector-valued fundamental theorem of calculus in the form

$$
\texttt{intervalIntegral.integral\_eq\_sub\_of\_hasDerivAt}.
$$

Its content here is: if $x$ has derivative $dx(u)$ at every $u\in [s_0,s]$, and if $dx$ is interval integrable over $[s_0,s]$, then

$$
\int_{s_0}^{s} dx(u)\,du=x(s)-x(s_0).
$$

This is exactly the fact named `hftc`. Rewriting with `rw [hftc]` replaces the integral in the goal by $x(s)-x(s_0)$. The remaining goal is

$$
x(s)=x(s_0)+(x(s)-x(s_0)),
$$

which is an additive identity in the abelian group $H$. The tactic `abel` normalizes and closes this identity.

For the second subgoal, the proof fixes $s\in (s_0,\infty)$ by `intro s hs`. From $s_0<s$ it obtains $s\in [s_0,\infty)$, named `hsIci`. Since $d\tau(s)>0$ on $[s_0,\infty)$, it also gets $d\tau(s)\neq0$, named `hdτne`.

The proof then defines the auxiliary function

$$
F:\mathbb R\to H,\qquad F(t)=dx(t)+d\tau(t)^{-1}\cdot (x(t)-y(t)).
$$

This is precisely the left-hand side of the ODE supplied by `hode`. The goal is to show that the derivative of $F$ at $s$ is zero, because the desired conclusion is the derivative expression of $F$ set equal to $0$.

To compute the derivative of $F$, the proof uses three derivative facts. First,

$$
\texttt{hinv}:\quad \operatorname{HasDerivAt}\bigl(t\mapsto d\tau(t)^{-1}\bigr)
\left(-\frac{dd\tau(s)}{(d\tau(s))^2}\right) s.
$$

This comes from applying the reciprocal rule `HasDerivAt.inv` to `hddτ s hsIci`, which says $d\tau$ has derivative $dd\tau(s)$ at $s$, together with the nonzero condition $d\tau(s)\neq0$. Mathematically, if $u$ is differentiable at $s$ with derivative $u'(s)$, then $t\mapsto u(t)^{-1}$ has derivative $-u'(s)/u(s)^2$ at $s$. Second,

$$
\texttt{hdiff}:\quad \operatorname{HasDerivAt}\bigl(t\mapsto x(t)-y(t)\bigr)(dx(s)-dy(s)) s,
$$

obtained from `hdx s hsIci` and `hdy s hsIci` by the difference rule `HasDerivAt.sub`. Third,

$$
\texttt{hFderiv}:\quad \operatorname{HasDerivAt} F
\left(
ddx(s)-\frac{dd\tau(s)}{(d\tau(s))^2}\cdot (x(s)-y(s))
+\frac{1}{d\tau(s)}\cdot (dx(s)-dy(s))
\right) s.
$$

This is obtained by unfolding $F$ with `dsimp [F]`, applying the sum rule `HasDerivAt.add` to the derivative of $dx$ and the derivative of the scalar-vector product $d\tau(t)^{-1}\cdot (x(t)-y(t))$, and applying the product rule `HasDerivAt.smul`. The product rule gives

$$
\left(-\frac{dd\tau(s)}{(d\tau(s))^2}\right)\cdot (x(s)-y(s))
+\frac{1}{d\tau(s)}\cdot (dx(s)-dy(s)).
$$

The `convert` and `simp` steps rewrite this expression into the displayed one, using the identity $-\frac{dd\tau(s)}{(d\tau(s))^2}=-\left(\frac{dd\tau(s)}{(d\tau(s))^2}\right)$ and elementary algebraic rearrangements.

Next the proof shows that $F$ agrees with the zero function near $s$. Since $s>s_0$, the lemma `eventually_gt_nhds hs` gives that for all $t$ sufficiently close to $s$, one has $t>s_0$. Using `filter_upwards`, the proof restricts to such $t$. For those $t$, $t\ge s_0$, so `hode t` applies and says

$$
dx(t)+d\tau(t)^{-1}\cdot (x(t)-y(t))=0.
$$

Since the left-hand side is exactly $F(t)$, this gives $0=F(t)$ eventually. Thus

$$
\texttt{hFzero}:\quad (\text{the constant zero function})=_{\text{eventually near }s} F.
$$

The fact that eventual equality is symmetric is what allows the proof to move between $F(t)=0$ and $0=F(t)$.

From `hFderiv` and the eventual equality `hFzero`, the proof uses `HasDerivAt.congr_of_eventuallyEq` to conclude

$$
\texttt{hconst}:\quad
\operatorname{HasDerivAt}(\text{constant zero function})
\left(
ddx(s)-\frac{dd\tau(s)}{(d\tau(s))^2}\cdot (x(s)-y(s))
+\frac{1}{d\tau(s)}\cdot (dx(s)-dy(s))
\right) s.
$$

Mathematically, if a function has a derivative at $s$ and is eventually equal to another function near $s$, then that other function has the same derivative at $s$.

Finally, the constant zero function has derivative $0$ at $s$, by `hasDerivAt_const`. The proof applies uniqueness of derivatives: since the zero function has derivative both the displayed expression and $0$ at $s$, those two quantities are equal. This is the invocation

$$
\texttt{exact hconst.unique (hasDerivAt\_const s (0 : H))}.
$$

Therefore

$$
ddx(s)-\frac{dd\tau(s)}{(d\tau(s))^2}\cdot (x(s)-y(s))
+\frac{1}{d\tau(s)}\cdot (dx(s)-dy(s))=0,
$$

which is exactly the second conjunct of the theorem.

