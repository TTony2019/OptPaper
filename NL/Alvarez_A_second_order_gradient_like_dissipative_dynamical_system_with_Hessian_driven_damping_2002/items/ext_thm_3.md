## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_thm_3.lean`

## Lean statement
```lean
theorem bruck_strong_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (E : H → ℝ) (X : ℝ → H) (M : Set H)
    (hconvex : ConvexOn ℝ Set.univ E) (heven : ∀ x, E (-x) = E x)
    (hmin : M = argmin E) (hM : M.Nonempty)
    (hproper : ERealFunction.IsProper fun x => (E x : EReal))
    (hlsc : LowerSemicontinuous fun x => (E x : EReal))
    (hconvexEpi : Convex ℝ (ERealFunction.epigraph fun x => (E x : EReal)))
    (hsol : ∃ uExt : ℝ → H,
      (∀ t : Set.Ici (0 : ℝ), uExt t = X t) ∧
      (∀ t : Set.Ici (0 : ℝ), (0 : ℝ) < t → (E (X t) : EReal) ≠ ⊤) ∧
      (∀ δ : ℝ, 0 < δ → ∃ K : NNReal, LipschitzOnWith K uExt (Set.Ici δ)) ∧
      ContinuousOn uExt (Set.Ici 0) ∧
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        0 ≤ t → -deriv uExt t ∈ subdifferential (fun x => (E x : EReal)) (uExt t)) :
    ∃ m ∈ M, Filter.Tendsto X Filter.atTop (nhds m)
```

## Statement explanation
The theorem `bruck_strong_convergence` is a strong-convergence theorem for a subgradient-flow trajectory in a real Hilbert space $H$. The space $H$ is assumed to be a complete real inner product space. The data are an energy $E:H\to\mathbb R$, a curve $X:\mathbb R\to H$, and a set $M\subseteq H$.

The hypotheses are:

- $E$ is convex on all of $H$: $E$ is a convex function on the whole space.
- $E$ is even: $E(-x)=E(x)$ for every $x\in H$.
- $M=\mathrm{argmin}E$. In the proof the unqualified `argmin` is used through its pointwise minimizer meaning: $z\in\mathrm{argmin}E$ means $E(z)\le E(y)$ for every $y$.
- $M$ is nonempty.
- The extended-real-valued function

$$
F(x)=(E(x):\mathrm{EReal})
$$

  is proper, lower semicontinuous, and has convex epigraph. Here $\mathrm{EReal}$ is the extended real line.
- There exists an extension $u_{\mathrm{ext}}:\mathbb R\to H$ of $X$ from the nonnegative times such that:
  - $u_{\mathrm{ext}}(t)=X(t)$ for all $t\ge0$;
  - for every $t\ge0$ with $t\gt 0$, the value $F(X(t))$ is not $+\infty$;
  - for every $\delta\gt 0$, $u_{\mathrm{ext}}$ is Lipschitz on $[\delta,\infty)$ with some nonnegative real constant $K$;
  - $u_{\mathrm{ext}}$ is continuous on $[0,\infty)$;
  - for almost every $t$ with respect to Lebesgue measure on $\mathbb R$, if $t\ge0$, then

$$
-\mathrm{deriv} u_{\mathrm{ext}}(t)\in \partial F(u_{\mathrm{ext}}(t)).
$$

    That is, $u_{\mathrm{ext}}$ satisfies the subgradient-flow differential inclusion

$$
\dot u(t)+\partial F(u(t))\ni0
$$

    for almost every nonnegative $t$.

The conclusion is that there exists $m\in M$ such that

$$
X(t)\to m \quad\text{in }H\text{ as }t\to\infty.
$$

Thus the theorem says that, under an even convex energy, a suitable subgradient-flow trajectory converges strongly to a minimizer of the energy. The hypothesis `hconvex` is present in the statement, but the displayed proof does not use it explicitly; the convexity passed to the Bruck convergence theorem is the convex-epigraph hypothesis `hconvexEpi`.

## Lean proof
```lean
by
  rcases hM with ⟨z, hzM⟩
  rw [hmin] at hzM
  have hminEreal : ∃ z : H, z ∈ argmin (fun x => (E x : EReal)) := by
    refine ⟨z, ?_⟩
    intro y
    exact EReal.coe_le_coe (hzM y)
  have hminEreal' : ∃ z : H, z ∈ Alvarez2002.argmin (fun x => (E x : EReal)) := by
    rcases hminEreal with ⟨w, hw⟩
    exact ⟨w, mem_argmin_of_forall (fun x => (E x : EReal)) hw⟩
  let u : Set.Ici (0 : ℝ) → H := fun t => X t
  have hsol' : ∃ uExt : ℝ → H,
      (∀ t : Set.Ici (0 : ℝ), uExt t = u t) ∧
      (∀ t : Set.Ici (0 : ℝ), (0 : ℝ) < t → (E (u t) : EReal) ≠ ⊤) ∧
      (∀ δ : ℝ, 0 < δ → ∃ K : NNReal, LipschitzOnWith K uExt (Set.Ici δ)) ∧
      ContinuousOn uExt (Set.Ici 0) ∧
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        0 ≤ t → -deriv uExt t ∈ subdifferential (fun x => (E x : EReal)) (uExt t) := by
    simpa [u] using hsol
  rcases bruck_subgradient_flow_convergence (E := H) (fun x => (E x : EReal))
      hproper hlsc hconvexEpi u hminEreal' hsol' with ⟨m, hm, _, hstrong⟩
  have hevenEreal : ∀ x : H, (E (-x) : EReal) = (E x : EReal) := by
    intro x
    exact congrArg (fun r : ℝ => (r : EReal)) (heven x)
  have hu : Filter.Tendsto u Filter.atTop (nhds m) := hstrong hevenEreal
  have hmReal : m ∈ argmin E := by
    intro y
    exact EReal.coe_le_coe_iff.mp (forall_min_of_mem_argmin (fun x => (E x : EReal)) hm y)
  have hmM : m ∈ M := by
    rw [hmin]
    exact hmReal
  have hX : Filter.Tendsto X Filter.atTop (nhds m) := by
    have hg : Filter.Tendsto (fun t : ℝ =>
        (⟨max t (0 : ℝ), le_max_right t (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
        Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro a
      refine Filter.eventually_atTop.2 ⟨(max (a : ℝ) (0 : ℝ) : ℝ), ?_⟩
      intro t ht
      change (a : ℝ) ≤ (max t (0 : ℝ) : ℝ)
      exact le_trans (le_trans (le_max_left (a : ℝ) (0 : ℝ)) ht) (le_max_left t (0 : ℝ))
    have hcomp : Filter.Tendsto
        (fun t : ℝ => X (⟨max t (0 : ℝ), le_max_right t (0 : ℝ)⟩ : Set.Ici (0 : ℝ)))
        Filter.atTop (nhds m) := hu.comp hg
    refine hcomp.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hmax : max t (0 : ℝ) = t := max_eq_left (le_of_lt ht)
    simp [u, hmax]
  exact ⟨m, hmM, hX⟩
```

## Proof explanation
The proof begins by extracting a minimizer from the nonempty set $M$. The command `rcases hM with ⟨z, hzM⟩` gives a point $z\in M$. Then `rw [hmin] at hzM` rewrites $M=\mathrm{argmin}E$, so $hzM$ becomes $z\in\mathrm{argmin}E$. Since the unqualified `argmin` is being used as the pointwise minimizer predicate, this means

$$
E(z)\le E(y)\quad\text{for every }y\in H.
$$

Next the proof creates a minimizer for the extended-real energy $F(x)=(E(x):\mathrm{EReal})$. The statement

$$
\texttt{hminEreal}:\exists z,\ z\in\mathrm{argmin}F
$$

is proved by taking the same point $z$. For an arbitrary $y$, the hypothesis $hzM$ gives $E(z)\le E(y)$. Applying `EReal.coe_le_coe` turns the real inequality into the extended-real inequality

$$
(E(z):\mathrm{EReal})\le (E(y):\mathrm{EReal}),
$$

that is, $F(z)\le F(y)$. Hence $z$ is a pointwise minimizer of $F$.

The proof then converts this pointwise minimizer into a minimizer in the namespaced sense `Alvarez2002.argmin`. The new statement is

$$
\texttt{hminEreal'}:\exists z,\ z\in \texttt{Alvarez2002.argmin}(F).
$$

The cited lemma `mem_argmin_of_forall` says that for a function $f:X\to L$ into a complete linear order $L$, if $f(z)\le f(y)$ for every $y$, then $z\in \texttt{Alvarez2002.argmin}(f)$. Here $L=\mathrm{EReal}$, and the definition of the namespaced `argmin` is the set of points where $f$ equals the infimum of its range. Thus the lemma turns the pointwise minimality of $z$ for $F$ into the statement

$$
F(z)=\inf(\mathrm{range}F).
$$

This is the minimizer notion expected by the Bruck convergence theorem.

The proof next restricts $X$ to the nonnegative half-line. It defines

```math
u:\{t\in\mathbb R\mid t\ge0\}\to H,\qquad u(t)=X(t).
```

The hypothesis `hsol` is then restated as `hsol'` using `simpa [u] using hsol`. This changes the agreement condition $u_{\mathrm{ext}}(t)=X(t)$ into $u_{\mathrm{ext}}(t)=u(t)$, and similarly rewrites the finite-energy condition $F(X(t))\ne\top$ as $F(u(t))\ne\top$. The Lipschitz, continuity, and subgradient-flow conditions are unchanged.

The main convergence input is now invoked:

```math
\texttt{bruck\_subgradient\_flow\_convergence}
```

applied to the extended-real energy $F(x)=(E(x):\mathrm{EReal})$, its properness `hproper`, lower semicontinuity `hlsc`, convex epigraph `hconvexEpi`, the restricted curve $u$, the existence of a minimizer in `Alvarez2002.argmin`, and the flow data `hsol'`. The proof destructs the conclusion as

```math
\langle m,hm,\_,hstrong\rangle.
```

The component we use is $hm:m\in \texttt{Alvarez2002.argmin}(F)$. The component `hstrong` is a conditional convergence statement: when it is supplied with a proof that $F$ is even, it yields convergence of the restricted trajectory $u$ to $m$. The ignored component is not used.

The proof then establishes that $F$ is even. For each $x\in H$, the hypothesis `heven` gives $E(-x)=E(x)$. Applying the coercion $\mathbb R\to\mathrm{EReal}$ to both sides, via `congrArg (fun r : ℝ => (r : EReal))`, gives

$$
(E(-x):\mathrm{EReal})=(E(x):\mathrm{EReal}),
$$

so $F(-x)=F(x)$. This is the statement `hevenEreal`.

Applying `hstrong` to `hevenEreal` gives

```math
\texttt{hu}:\mathrm{Tendsto}u\,\mathrm{atTop}\,(\mathrm{nhds}m),
```

meaning $u(t)\to m$ as $t\to\infty$ along the nonnegative half-line.

Next the proof converts $hm$ into a minimizer statement for the original real-valued energy $E$. The goal is

$$
\texttt{hmReal}:m\in\mathrm{argmin}E.
$$

It is proved by introducing an arbitrary $y$ and applying `forall_min_of_mem_argmin` to $F$ and $hm$. That lemma says that if $z\in\texttt{Alvarez2002.argmin}(f)$, then $f(z)\le f(y)$ for every $y$. Here it gives

$$
(E(m):\mathrm{EReal})\le (E(y):\mathrm{EReal}).
$$

Then `EReal.coe_le_coe_iff.mp` strips the extended-real coercions and returns the real inequality

$$
E(m)\le E(y).
$$

Since $y$ was arbitrary, $m$ is a pointwise minimizer of $E$. Rewriting $M=\mathrm{argmin}E$ with `rw [hmin]` then gives `hmM : m ∈ M`.

Finally the proof transfers convergence from the subtype $`\{t\ge0\}`$ back to the full real line. It defines the map

```math
g(t)=(\max(t,0))\in\{s\in\mathbb R\mid s\ge0\}.
```

The proof first shows

$$
g(t)\to\mathrm{atTop}\quad\text{as }t\to\infty.
$$

Using `rw [Filter.tendsto_atTop]`, this is reduced to showing that for every real $a$, eventually $a\le g(t)$. The proof chooses the threshold $T=\max(a,0)$. If $T\le t$, then

$$
a\le \max(a,0)=T\le t\le \max(t,0)=g(t).
$$

Thus $a\le g(t)$ eventually, so $g\to\mathrm{atTop}$.

Since `hu` says $u\to m$ along `atTop`, and $g\to\mathrm{atTop}$, the composition `hu.comp hg` gives

$$
u(g(t))=X(g(t))\to m.
$$

For $t\gt 0$, one has $\max(t,0)=t$, so $g(t)=t$. The proof uses `filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)]` to get an eventual hypothesis $t\gt 0$, then `max_eq_left` to obtain $\max(t,0)=t$, and `simp [u, hmax]` to show that $X(t)$ and $X(g(t))$ agree eventually. Finally `Filter.Tendsto.congr'` transfers the convergence of $X(g(t))$ to convergence of $X(t)$. Therefore

$$
X(t)\to m\quad\text{as }t\to\infty.
$$

The proof closes by packaging the two conclusions:

$$
m\in M
$$

and

$$
X(t)\to m,
$$

which is exactly the desired existence statement.

