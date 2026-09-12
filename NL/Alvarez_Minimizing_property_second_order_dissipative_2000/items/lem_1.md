## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/lem_1.lean`

## Lean statement
```lean
theorem converges_of_integrable_positive_derivative (theta : ℝ → ℝ)
    (hDiff : ContDiffOn ℝ 1 theta (Set.Ici 0))
    (hLower : ∃ m : ℝ, ∀ t ∈ Set.Ici 0, m ≤ theta t)
    (hInt : IntegrableOn (fun t => max (deriv theta t) 0) (Set.Ici 0)) :
    ∃ l : ℝ, Tendsto theta atTop (nhds l)
```

## Statement explanation
The theorem `converges_of_integrable_positive_derivative` concerns a function $\theta:\mathbb R\to\mathbb R$. It assumes three hypotheses. First, $\theta$ is continuously differentiable on $[0,\infty)$, meaning in Lean that `ContDiffOn ℝ 1 theta (Set.Ici 0)` holds: $\theta$ has a continuous first derivative on the nonnegative half-line. Second, $\theta$ is bounded below on $[0,\infty)$: there exists $m\in\mathbb R$ such that $m\le \theta(t)$ for every $t\ge 0$. Third, the positive part of the derivative,

$$
t\mapsto \max(\theta'(t),0),
$$

is Lebesgue integrable on $[0,\infty)$. The conclusion is that there exists a real number $l$ such that

$$
\theta(t)\to l \qquad \text{as } t\to\infty,
$$

i.e. $\theta$ has a finite limit at $+\infty$.

Mathematically, the proof defines $g(t)=\max(\theta'(t),0)$, so $g\ge \theta'$ and $g\ge0$. The auxiliary function

$$
\mathrm{rawW}(u)=\theta(u)-\int_0^u g(x)\,dx
$$

has derivative $\theta'(u)-g(u)\le0$ on $[0,\infty)$, so it is nonincreasing there. It is also bounded below: the lower bound on $\theta$ and the bound $\int_0^u g\le \int_{(0,\infty)}g$ show that $\mathrm{rawW}(u)\ge m-\int_{(0,\infty)}g$. Hence $\mathrm{rawW}$ converges to its infimum. Meanwhile the cumulative integral $\int_0^t g$ converges to the total integral $\int_{(0,\infty)}g$, because $g$ is integrable on $(0,\infty)$. Since for $t\ge0$,

$$
\theta(t)=\mathrm{rawW}(t)+\int_0^t g(x)\,dx,
$$

the sum of the two limits gives the limit of $\theta$.

## Lean proof
```lean
by
  let g : ℝ → ℝ := fun x => max (deriv theta x) 0
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hderiv_le_g : ∀ x, deriv theta x ≤ g x := fun x => le_max_left _ _
  have hIntIoi : IntegrableOn g (Set.Ioi 0) := by
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mp hInt
  have hgInt : ∀ s t, 0 ≤ s → s ≤ t → IntervalIntegrable g volume s t := by
    intro s t hs hst
    apply IntegrableOn.intervalIntegrable
    apply hInt.mono_set
    intro x hx
    exact hs.trans (by simpa [min_eq_left hst] using hx.1)
  let rawW : ℝ → ℝ := fun u => theta u - ∫ x in 0..u, g x
  have hrawW : AntitoneOn rawW (Set.Ici 0) := by
    simpa [rawW] using rawW_antitoneOn_Ici theta hDiff g hderiv_le_g hgInt
  let W : ℝ → ℝ := fun t => rawW (max t 0)
  have hWanti : Antitone W := by
    intro s t hst
    change rawW (max t 0) ≤ rawW (max s 0)
    refine hrawW ?_ ?_ (max_le_max_right 0 hst)
    · exact le_max_right s 0
    · exact le_max_right t 0
  obtain ⟨m, hm⟩ := hLower
  let G : ℝ := ∫ x in Set.Ioi 0, g x
  have hWbdd : BddBelow (Set.range W) := by
    refine ⟨m - G, ?_⟩
    rintro _ ⟨t, rfl⟩
    have hu : 0 ≤ max t 0 := le_max_right _ _
    have hprim : (∫ x in 0..max t 0, g x) ≤ G := by
      exact intervalIntegral_le_integral_Ioi_of_nonneg hIntIoi hg_nonneg hu
    dsimp [W, rawW]
    exact sub_le_sub (hm _ hu) hprim
  have hWlim : Tendsto W atTop (nhds (⨅ t : ℝ, W t)) :=
    tendsto_atTop_ciInf hWanti hWbdd
  have hPlim : Tendsto (fun t => ∫ x in 0..t, g x) atTop (nhds G) := by
    simpa [G] using intervalIntegral_tendsto_integral_Ioi 0 hIntIoi tendsto_id
  refine ⟨(⨅ t : ℝ, W t) + G, ?_⟩
  apply (hWlim.add hPlim).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp [W, rawW, max_eq_left ht]
```

## Proof explanation
The proof begins by defining the positive part of the derivative:

$$
g(x)=\max(\theta'(x),0).
$$

The two immediate facts are

$$
0\le g(x),\qquad \theta'(x)\le g(x)
$$

for every $x$, which are the elementary inequalities $0\le \max(a,0)$ and $a\le \max(a,0)$. These are used later to make the adjusted function $\mathrm{rawW}$ nonincreasing and bounded below.

Next, the proof obtains integrability of $g$ on $(0,\infty)$. The hypothesis `hInt` gives integrability on $[0,\infty)$. The invocation `(integrableOn_Ici_iff_integrableOn_Ioi).mp hInt` uses the fact that the single point $0$ is null for Lebesgue measure, so integrability on $[0,\infty)$ is equivalent to integrability on $(0,\infty)$. Thus `hIntIoi` says $g$ is integrable on $\operatorname{Ioi}0=(0,\infty)$.

The proof then shows that for any $0\le s\le t$, $g$ is interval-integrable on the interval from $s$ to $t$. Since $s\le t$, the unordered interval $\operatorname{uIcc}s t$ is just $[s,t]$. The subset $[s,t]\subseteq[0,\infty)$ holds because $0\le s$. The command `hInt.mono_set` restricts the integrability on $[0,\infty)$ to this smaller interval, and `IntegrableOn.intervalIntegrable` converts integrability on the interval set into `IntervalIntegrable g volume s t`. This supplies the interval-integrability hypothesis needed by the local lemma `rawW_antitoneOn_Ici`.

Now the proof defines

$$
\mathrm{rawW}(u)=\theta(u)-\int_0^u g(x)\,dx.
$$

It applies `rawW_antitoneOn_Ici` to $\theta$, $g$, the $C^1$ hypothesis on $[0,\infty)$, the pointwise inequality $\theta'\le g$, and the interval-integrability fact just proved. The lemma states that under exactly these assumptions,

$$
u\mapsto \theta(u)-\int_0^u g
$$

is antitone on $[0,\infty)$. Concretely, for $0\le a\le b$,

$$
\mathrm{rawW}(b)-\mathrm{rawW}(a)
=\theta(b)-\theta(a)-\int_a^b g
=\int_a^b \theta'-\int_a^b g
=\int_a^b(\theta'-g)\le0,
$$

so `rawW` is nonincreasing.

The proof then extends `rawW` to all of $\mathbb R$ by defining

$$
W(t)=\mathrm{rawW}(\max(t,0)).
$$

Since $\max(t,0)\ge0$, this clamps every real input to the nonnegative half-line. To prove $W$ is antitone, take $s\le t$. Then

$$
\max(s,0)\le \max(t,0),
$$

and both arguments lie in $[0,\infty)$. The antitone property of $\mathrm{rawW}$ on $[0,\infty)$ gives

$$
\mathrm{rawW}(\max(t,0))\le \mathrm{rawW}(\max(s,0)),
$$

which is exactly $W(t)\le W(s)$. Thus `hWanti` establishes that $W$ is nonincreasing on all of $\mathbb R$.

The proof then extracts the lower bound from the hypothesis `hLower`: there is $m$ such that $m\le\theta(t)$ for every $t\ge0$. It also defines the total integral

$$
G=\int_{(0,\infty)} g(x)\,dx.
$$

Because $g$ is integrable on $(0,\infty)$, this real number is finite.

To prove that $W$ is bounded below, the proof shows that $m-G$ is a lower bound for the range of $W$. For an arbitrary $t$, put $u=\max(t,0)$. Then $u\ge0$, so the lower bound on $\theta$ gives

$$
m\le \theta(u).
$$

The local lemma `intervalIntegral_le_integral_Ioi_of_nonneg`, applied to $g$, its integrability on $(0,\infty)$, its nonnegativity everywhere, and the fact $u\ge0$, gives

$$
\int_0^u g\le \int_{(0,\infty)}g=G.
$$

Combining $m\le\theta(u)$ with $\int_0^u g\le G$ via the subtraction inequality `sub_le_sub` yields

$$
m-G\le \theta(u)-\int_0^u g=W(t).
$$

Thus every value of $W$ is at least $m-G$, so the range of $W$ is bounded below.

Since $W$ is antitone and bounded below, the invocation `tendsto_atTop_ciInf hWanti hWbdd` gives exactly

$$
W(t)\to \inf_{t\in\mathbb R} W(t)
\qquad\text{as }t\to\infty.
$$

This is the monotone-convergence fact for a nonincreasing function bounded below: it decreases to its infimum.

Separately, the proof shows that the cumulative integral of $g$ converges to its total integral. The invocation `intervalIntegral_tendsto_integral_Ioi 0 hIntIoi tendsto_id` gives the specialized consequence

$$
\int_0^t g(x)\,dx\to \int_{(0,\infty)}g(x)\,dx=G
\qquad\text{as }t\to\infty.
$$

This is the standard improper-integral convergence statement for an integrable function on $(0,\infty)$.

The proof now chooses the candidate limit

$$
l=\inf_{t\in\mathbb R}W(t)+G.
$$

Adding the two limits using `Tendsto.add` gives

$$
W(t)+\int_0^t g(x)\,dx\to l.
$$

It remains to identify $W(t)+\int_0^t g$ with $\theta(t)$ eventually. The command `filter_upwards [eventually_ge_atTop (0 : ℝ)]` restricts attention to all sufficiently large $t$, in fact to all $t\ge0$. For such $t$, $\max(t,0)=t$, so

$$
W(t)=\mathrm{rawW}(t)=\theta(t)-\int_0^t g(x)\,dx.
$$

Therefore

$$
W(t)+\int_0^t g(x)\,dx=\theta(t).
$$

The `simp` step performs this unfolding and cancellation. Finally, `Tendsto.congr'` transfers the limit from the eventually equal function $W(t)+\int_0^t g$ to $\theta(t)$. Hence

$$
\theta(t)\to l
\qquad\text{as }t\to\infty,
$$

which is exactly the existential conclusion of the theorem.

