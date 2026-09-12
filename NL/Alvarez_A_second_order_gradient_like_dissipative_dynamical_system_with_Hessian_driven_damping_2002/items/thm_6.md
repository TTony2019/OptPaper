## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_6.lean`

## Lean statement
```lean
theorem gdin_weakly_converges_to_argmin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (β a b : ℝ)
    (x y : ℝ → H) (hbounded : ∃ m : ℝ, ∀ x, m ≤ Φ x) (x₀ y₀ : H)
    (hΦ : ContDiff ℝ 1 Φ)
    (hloclip : ∀ R : ℝ, ∃ L : ℝ, ∀ x y, ‖x‖ ≤ R →
      ‖y‖ ≤ R → ‖gradient Φ x - gradient Φ y‖ ≤ L * ‖x - y‖)
    (hβ : 0 < β) (hb : 0 < b) (hab : 0 < b + a)
    (hconvex : ConvexOn ℝ Set.univ Φ)
    (hxy : ContDiffOn ℝ 1 x (Set.Ici 0) ∧ ContDiffOn ℝ 2 y (Set.Ici 0))
    (hmin : (Optimization.argminSet Φ).Nonempty)
    (hsol : IsSolution_gDIN Φ β a b x₀ y₀ x y) :
    ∃ z, z ∈ Optimization.argminSet Φ ∧
      Tendsto (fun t => toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H z))
```

## Statement explanation
The declaration `gdin_weakly_converges_to_argmin` is a theorem about the long-time asymptotic behavior of the trajectory $x$ of a second-order dissipative dynamical system with Hessian-driven damping. It assumes the ambient space $H$ is a complete real inner product space, i.e. a real Hilbert space, and considers a real-valued potential $\Phi : H \to \mathbb R$, real parameters $\beta,a,b$, two curves $x,y : \mathbb R \to H$, and initial points $x_0,y_0 \in H$.

The hypotheses are:

- $\Phi$ is bounded below: there exists $m\in\mathbb R$ such that $m\le \Phi(u)$ for every $u\in H$.
- $\Phi$ is $C^1$: `hΦ : ContDiff ℝ 1 Φ`.
- The gradient $\nabla\Phi$ is locally Lipschitz on bounded balls: for every radius $R$, there exists $L$ such that whenever $`\|u\|\le R`$and$`\|v\|\le R`$,

```math
\|\nabla\Phi(u)-\nabla\Phi(v)\|\le L\|u-v\|.
```

- The parameters satisfy $\beta\gt 0$, $b\gt 0$, and $b+a\gt 0$.
- $\Phi$ is convex on the whole space: `hconvex : ConvexOn ℝ Set.univ Φ`.
- The curve $x$ is $C^1$ on $[0,\infty)$, and the auxiliary curve $y$ is $C^2$ on $[0,\infty)$.
- The set of global minimizers of $\Phi$,

```math
\mathrm{argminSet}\Phi=\{u\in H\mid \forall v\in H,\ \Phi(u)\le \Phi(v)\},
```

  is nonempty.
- The pair $(x,y)$ is a solution of the gDIN system with potential $\Phi$, parameters $\beta,a,b$, and initial data $x_0,y_0$, expressed by the predicate `IsSolution_gDIN`. The exact differential equations of that predicate are not defined in the supplied source; the proof only passes this hypothesis to the cited gDIN results.

The conclusion is that there exists a global minimizer $z\in \mathrm{argminSet}\Phi$ such that

$$
x(t)\rightharpoonup z \qquad \text{as } t\to\infty,
$$

i.e. $x(t)$ converges weakly to $z$. In Lean this is written using the canonical map `toWeakSpace ℝ H` from $H$ to the same space with the weak topology:

$$
\mathrm{Tendsto}\bigl(t\mapsto \mathrm{toWeakSpace}_{\mathbb R,H}(x(t))\bigr)
\ \mathrm{atTop}\
\bigl(\mathrm{nhds}(\mathrm{toWeakSpace}_{\mathbb R,H}(z))\bigr).
$$

Thus, in ordinary mathematical language, the theorem says that under convexity, $C^1$, local Lipschitz gradient, boundedness below, positivity of the damping parameters, and the existence of a minimizer, every solution trajectory of the gDIN system converges weakly to some global minimizer of $\Phi$.

## Lean proof
```lean
by
  have hab' : 0 < a + b := by linarith
  have hgrad_lip : LipschitzOnBoundedSets (gradient Φ) :=
    gdin_grad_lipschitzOnBounded_thm6 (gradient Φ) hloclip
  have hdist : ∀ z, z ∈ Optimization.argminSet Φ →
      ∃ d : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds d) := by
    intro z hz
    exact gdin_distance_limit Φ β a b x y hbounded x₀ y₀ hΦ hloclip hβ hb hab
      hconvex hxy hsol hz
  have hphi_x : ∃ l : ℝ, Tendsto (fun t => Φ (x t)) atTop (nhds l) :=
    gdin_phi_limit Φ β a b hΦ hbounded hgrad_lip hβ hb hab' x₀ y₀ x y hxy hsol
  have hx_bounded : Bornology.IsBounded (x '' Set.Ici (0 : ℝ)) := by
    rcases hmin with ⟨z₀, hz₀⟩
    rcases hdist z₀ hz₀ with ⟨d₀, hd₀⟩
    obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hd₀) 1 zero_lt_one
    let T₀ : ℝ := max T 0
    have htail : ∀ t, T₀ ≤ t → ‖x t - z₀‖ ≤ |d₀| + 1 := by
      intro t ht
      have hdist' : dist (‖x t - z₀‖) d₀ < 1 := by
        simpa [Real.dist_eq] using hT t (le_trans (le_max_left T 0) ht)
      have habs : |‖x t - z₀‖ - d₀| < 1 := by simpa [Real.dist_eq] using hdist'
      have hle : ‖x t - z₀‖ - d₀ ≤ |‖x t - z₀‖ - d₀| := le_abs_self _
      have hnormd : ‖x t - z₀‖ ≤ d₀ + 1 := by nlinarith
      exact hnormd.trans (by linarith [le_abs_self d₀])
    have hcompact : IsCompact (x '' Set.Icc (0 : ℝ) T₀) := by
      exact isCompact_Icc.image_of_continuousOn
        (hxy.1.continuousOn.mono Set.Icc_subset_Ici_self)
    rcases isBounded_iff_forall_norm_le.mp hcompact.isBounded with ⟨R₀, hR₀⟩
    refine isBounded_iff_forall_norm_le.mpr ⟨max R₀ (|d₀| + 1 + ‖z₀‖), ?_⟩
    rintro q ⟨t, ht, rfl⟩
    by_cases hle : t ≤ T₀
    · exact (hR₀ _ ⟨t, ⟨ht, hle⟩, rfl⟩).trans (le_max_left _ _)
    · have hge : T₀ ≤ t := le_of_not_ge hle
      have htri : ‖x t‖ ≤ ‖x t - z₀‖ + ‖z₀‖ := by
        calc
          ‖x t‖ = ‖(x t - z₀) + z₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖x t - z₀‖ + ‖z₀‖ := norm_add_le _ _
      have htri' : ‖x t - z₀‖ + ‖z₀‖ ≤ (|d₀| + 1) + ‖z₀‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_right (htail t hge) ‖z₀‖)
      exact (htri.trans htri').trans (le_max_right _ _)
  have hbounded_asym := gdin_bounded_asymptotics Φ β a b hΦ hbounded hgrad_lip
    hβ hb hab' x₀ y₀ x y hxy hsol hx_bounded
  have hgrad_at_top : Tendsto (fun t => gradient Φ (x t)) atTop (nhds 0) := hbounded_asym.2.2.2
  have hgrad_at (y : H) : HasGradientAt Φ (gradient Φ y) y :=
    (hΦ.differentiable (by norm_num) y).hasGradientAt
  have hsupport : ∀ y p : H,
      Φ y + inner ℝ (gradient Φ y) (p - y) ≤ Φ p := by
    intro y p
    exact convex_supporting_baillon_haddad Φ (gradient Φ) hconvex
      (fun w => hgrad_at w) y p
  have hinner_zero_of_strong_bounded : ∀ (a b : ℕ → H),
      Tendsto a atTop (nhds 0) → Bornology.IsBounded (Set.range b) →
        Tendsto (fun n => inner ℝ (a n) (b n)) atTop (nhds 0) := by
    intro a b ha hb
    rcases isBounded_iff_forall_norm_le.mp hb with ⟨C, hC⟩
    let M : ℝ := max C 0
    have hbM : ∀ n, ‖b n‖ ≤ M := by
      intro n
      exact (hC _ ⟨n, rfl⟩).trans (le_max_left _ _)
    have hanorm : Tendsto (fun n => ‖a n‖) atTop (nhds 0) := by
      simpa using ha.norm
    have hbound : ∀ n, |inner ℝ (a n) (b n)| ≤ ‖a n‖ * M := by
      intro n
      calc
        |inner ℝ (a n) (b n)| ≤ ‖a n‖ * ‖b n‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (a n) (b n)
        _ ≤ ‖a n‖ * M := mul_le_mul_of_nonneg_left (hbM n) (norm_nonneg _)
    have hmajor : Tendsto (fun n => ‖a n‖ * M) atTop (nhds 0) := by
      simpa [zero_mul] using hanorm.mul tendsto_const_nhds
    have habs : Tendsto (fun n => |inner ℝ (a n) (b n)|) atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hbound hmajor
    have hneg : Tendsto (fun n => -|inner ℝ (a n) (b n)|) atTop (nhds 0) := by
      simpa using habs.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
      (fun _ => neg_abs_le _) (fun _ => le_abs_self _)
  have hcluster : ∀ s : ℕ → ℝ, Tendsto s atTop atTop → ∀ z,
      Tendsto (fun n => toWeakSpace ℝ H (x (s n))) atTop
        (nhds (toWeakSpace ℝ H z)) → z ∈ Optimization.argminSet Φ := by
    intro s hs z hweak
    rcases hphi_x with ⟨l, hl⟩
    have hgrad_seq : Tendsto (fun n => gradient Φ (x (s n))) atTop (nhds 0) :=
      hgrad_at_top.comp hs
    have hxseq_bounded : Bornology.IsBounded (Set.range (fun n => x (s n))) :=
      bounded_range_of_tendsto_weakly hweak
    have hinner_x : Tendsto
        (fun n => inner ℝ (gradient Φ (x (s n))) (x (s n))) atTop (nhds 0) :=
      hinner_zero_of_strong_bounded _ _ hgrad_seq hxseq_bounded
    have hineq_limit : ∀ p : H, l ≤ Φ p := by
      intro p
      have hlseq : Tendsto (fun n => Φ (x (s n))) atTop (nhds l) := hl.comp hs
      have hinner_p : Tendsto
          (fun n => inner ℝ (gradient Φ (x (s n))) p) atTop (nhds 0) := by
        simpa using hinner_zero_of_strong_bounded _ (fun _ => p) hgrad_seq
          (by simp)
      have hinner_diff : Tendsto
          (fun n => inner ℝ (gradient Φ (x (s n))) (p - x (s n))) atTop (nhds 0) := by
        simpa [inner_sub_right] using hinner_p.sub hinner_x
      have hsum : Tendsto
          (fun n => Φ (x (s n)) + inner ℝ (gradient Φ (x (s n)))
            (p - x (s n))) atTop (nhds l) := by
        simpa using hlseq.add hinner_diff
      apply le_of_tendsto hsum
      exact Filter.Eventually.of_forall (fun n => hsupport (x (s n)) p)
    let f : H → EReal := fun y => (Φ y : EReal)
    have hf_lsc : LowerSemicontinuous f := by
      simpa [f] using (continuous_coe_real_ereal.comp hΦ.continuous).lowerSemicontinuous
    have hf_quasi : QuasiconvexOn ℝ Set.univ f := by
      rw [ERealFunction.quasiconvexOn_univ_iff_convex_lowerLevelSet f]
      intro ξ
      apply (convex_iff_forall_pos).2
      intro a ha b hb wa wb hwa hwb hwab
      have haE := (ERealFunction.mem_lowerLevelSet_iff f ξ a).1 ha
      have hbE := (ERealFunction.mem_lowerLevelSet_iff f ξ b).1 hb
      change (Φ a : EReal) ≤ (ξ : EReal) at haE
      change (Φ b : EReal) ≤ (ξ : EReal) at hbE
      have ha' : Φ a ≤ ξ := by exact_mod_cast haE
      have hb' : Φ b ≤ ξ := by exact_mod_cast hbE
      have hconv := hconvex.2 (Set.mem_univ a) (Set.mem_univ b) hwa.le hwb.le hwab
      have hconv' : Φ (wa • a + wb • b) ≤ wa * Φ a + wb * Φ b := by
        simpa [smul_eq_mul] using hconv
      have hweighted : wa * Φ a + wb * Φ b ≤ ξ := by
        calc
          wa * Φ a + wb * Φ b ≤ wa * ξ + wb * ξ := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left ha' hwa.le)
              (mul_le_mul_of_nonneg_left hb' hwb.le)
          _ = ξ := by rw [← add_mul, hwab, one_mul]
      have hcombo : Φ (wa • a + wb • b) ≤ ξ := hconv'.trans hweighted
      apply (ERealFunction.mem_lowerLevelSet_iff f ξ (wa • a + wb • b)).2
      change (Φ (wa • a + wb • b) : EReal) ≤ (ξ : EReal)
      exact_mod_cast hcombo
    have hfweak_lsc := ERealFunction.weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
    have hlseq : Tendsto (fun n => Φ (x (s n))) atTop (nhds l) := hl.comp hs
    have hlseqE : Tendsto (fun n => f (x (s n))) atTop (nhds (l : EReal)) := by
      simpa [f] using (continuous_coe_real_ereal.tendsto l).comp hlseq
    have hz_le_l : f z ≤ (l : EReal) := by
      calc
        f z = (f ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H z) := by simp
        _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm)
            (nhds (toWeakSpace ℝ H z)) := hfweak_lsc.le_liminf _
        _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm)
            (Filter.map (fun n => toWeakSpace ℝ H (x (s n))) atTop) :=
          Filter.liminf_le_liminf_of_le hweak
        _ = liminf (f ∘ (fun n => x (s n))) atTop := by
          rw [← Filter.liminf_comp]
          congr 1
        _ = (l : EReal) := hlseqE.liminf_eq
    have hz_le_l_real : Φ z ≤ l := by
      change (Φ z : EReal) ≤ (l : EReal) at hz_le_l
      exact_mod_cast hz_le_l
    have hl_le_z := hineq_limit z
    have hz_eq : Φ z = l := le_antisymm hz_le_l_real hl_le_z
    intro y
    have hl_le_y := hineq_limit y
    rw [hz_eq]
    exact hl_le_y
  exact Alvarez2002.opial_continuous_time x (Optimization.argminSet Φ) hmin hcluster hdist
```

## Proof explanation
The proof proceeds by verifying the hypotheses of the continuous-time Opial lemma and then applying it.

First, the proof derives $`\,0<a+b\,`$from the hypothesis$`\,0<b+a\,`$ by commutativity of addition. The tactic `linarith` closes this linear arithmetic goal. This variant is needed because some cited results state positivity as $0\lt a+b$.

Next, the hypothesis `hloclip`, saying that $\nabla\Phi$ is Lipschitz on every bounded ball, is converted into the global-on-bounded-sets property `LipschitzOnBoundedSets (gradient Φ)`. The cited theorem `gdin_grad_lipschitzOnBounded_thm6` states exactly this implication: if a map $g:H\to H$ satisfies, for every radius $R$, an estimate

```math
\|g(u)-g(v)\|\le L\|u-v\|
```

whenever $`\|u\|\le R`$and$`\|v\|\le R`$, then for every bounded set$S\subseteq H$there is a nonnegative constant$K$such that$g$is$K$-Lipschitz on$S$. Applied to$g=\nabla\Phi$, this gives `hgrad_lip`.

The proof then defines the distance-limit property `hdist`: for every global minimizer $z$ of $\Phi$, the real-valued function

```math
t\mapsto \|x(t)-z\|
```

has a finite limit as $t\to\infty$. This is obtained from the cited theorem `gdin_distance_limit`. That theorem says that, under the same boundedness, $C^1$, local-Lipschitz-gradient, positivity, convexity, regularity, and solution assumptions, if $z\in\mathrm{argminSet}\Phi$, then there exists $d\in\mathbb R$ such that

```math
\|x(t)-z\|\to d.
```

The proof invokes it for an arbitrary minimizer $z$, using `intro z hz` to introduce the arbitrary point and its minimizer property, and then `exact` to supply precisely the required instance.

The proof also obtains `hphi_x`, the assertion that the energy along the trajectory has a limit:

$$
\exists l\in\mathbb R,\qquad \Phi(x(t))\to l.
$$

This is supplied by the cited result `gdin_phi_limit`, invoked with the data and hypotheses of the problem, together with the just-derived Lipschitz-on-bounded-sets fact. The visible consequence used in the proof is exactly that the scalar function $t\mapsto \Phi(x(t))$ converges.

The next major step is to prove that the trajectory is bounded on $[0,\infty)$. The proof chooses a minimizer $z_0$ from `hmin`. Using `hdist z₀ hz₀`, it obtains a real number $d_0$ and the convergence

```math
\|x(t)-z_0\|\to d_0.
```

The characterization `Metric.tendsto_atTop` converts this into an $\varepsilon\text{-}T$ statement. Taking $\varepsilon=1$, the proof obtains a time $T$ such that for all $t\ge T$,

```math
\mathrm{dist}\bigl(\|x(t)-z_0\|,d_0\bigr)<1.
```

Since distance on $\mathbb R$ is absolute value, this says

```math
\bigl|\|x(t)-z_0\|-d_0\bigr|<1.
```

Letting $T_0=\max(T,0)$, the proof shows for all $t\ge T_0$,

```math
\|x(t)-z_0\|\le |d_0|+1.
```

Indeed, from the absolute-value inequality one gets $`\|x(t)-z_0\|\le d_0+1`$, and then$d_0+1\le |d_0|+1$. The tactics `simpa [Real.dist_eq]`, `nlinarith`, and the standard inequality $a\le |a|$ handle these estimates.

On the compact interval $[0,T_0]$, the curve $x$ is continuous because `hxy.1` gives $C^1$ regularity on $[0,\infty)$. The proof uses `isCompact_Icc.image_of_continuousOn` to conclude that the image $x''[0,T_0]$ is compact. A compact subset of a normed space is bounded, so `isBounded_iff_forall_norm_le` gives a uniform norm bound $R_0$:

```math
\|x(t)\|\le R_0\qquad\text{for }0\le t\le T_0.
```

For times $t\gt T_0$, the proof uses the tail estimate and the triangle inequality:

```math
\|x(t)\|
=\|(x(t)-z_0)+z_0\|
\le \|x(t)-z_0\|+\|z_0\|
\le |d_0|+1+\|z_0\|.
```

Therefore the entire image $x''[0,\infty)$ is bounded by

```math
\max\bigl(R_0,\ |d_0|+1+\|z_0\|\bigr).
```

This establishes `hx_bounded`, the boundedness of $x$ on nonnegative times.

With boundedness of $x$ available, the proof applies the cited theorem `gdin_bounded_asymptotics` to the data and hypotheses. That theorem gives a conjunction:

$$
\text{boundedness of }\dot x,\quad
\text{boundedness of }t\mapsto \nabla\Phi(x(t)),\quad
\dot x(t)\to 0,\quad
\nabla\Phi(x(t))\to 0.
$$

The proof only extracts the last conjunct:

$$
\nabla\Phi(x(t))\to 0
$$

strongly in $H$.

Next, the proof records that since $\Phi$ is $C^1$, at every point $u\in H$ the vector $\nabla\Phi(u)$ is the gradient of $\Phi$ at $u$:

$$
D\Phi(u)(v)=\langle \nabla\Phi(u),v\rangle.
$$

In Lean this is `HasGradientAt Φ (gradient Φ u) u`, obtained from differentiability of $\Phi$. This is used to invoke the cited convex supporting inequality `convex_supporting_baillon_haddad`. That theorem states that if $f:H\to\mathbb R$ is convex on all of $H$, and if `grad` is a gradient of $f$ at every point, then for all $y,p\in H$,

$$
f(y)+\langle \mathrm{grad}(y),p-y\rangle\le f(p).
$$

Applied to $f=\Phi$ and `grad = gradient Φ`, this gives the supporting-hyperplane inequality

$$
\Phi(y)+\langle \nabla\Phi(y),p-y\rangle\le \Phi(p)
$$

for all $y,p\in H$.

The proof then proves an auxiliary convergence fact: if $a_n\to0$ strongly in $H$ and the sequence $b_n$ is bounded in norm, then

$$
\langle a_n,b_n\rangle\to 0.
$$

The proof uses the boundedness of $b_n$ to get a constant $M\ge0$ with $`\|b_n\|\le M`$. Cauchy–Schwarz gives

```math
|\langle a_n,b_n\rangle|\le \|a_n\|\|b_n\|\le \|a_n\|M.
```

Since $`\|a_n\|\to0`$, the product$`\|a_n\|M\to0`$. The squeeze theorem `squeeze_zero` gives $|\langle a_n,b_n\rangle|\to0$, and then the two-sided bounds

$$
-|\langle a_n,b_n\rangle|\le \langle a_n,b_n\rangle\le |\langle a_n,b_n\rangle|
$$

together with `tendsto_of_tendsto_of_tendsto_of_le_of_le` give $\langle a_n,b_n\rangle\to0$.

This auxiliary fact is used in the main cluster-point argument. The proof defines `hcluster`: for every sequence of times $s:\mathbb N\to\mathbb R$ with $s_n\to\infty$, and every $z\in H$, if

$$
x(s_n)\rightharpoonup z
$$

weakly, then $z\in\mathrm{argminSet}\Phi$. This is the key Opial-type condition.

Inside the proof of `hcluster`, let $s_n\to\infty$ and suppose $x(s_n)\rightharpoonup z$. From `hphi_x`, the proof has

$$
\Phi(x(s_n))\to l.
$$

From $\nabla\Phi(x(t))\to0$, composing with $s_n\to\infty$ gives

$$
\nabla\Phi(x(s_n))\to0.
$$

From the weak convergence $x(s_n)\rightharpoonup z$, the cited lemma `bounded_range_of_tendsto_weakly` gives that the range of the sequence $n\mapsto x(s_n)$ is bounded. Therefore, using the auxiliary inner-product fact above,

$$
\langle \nabla\Phi(x(s_n)),x(s_n)\rangle\to0.
$$

For an arbitrary $p\in H$, the supporting inequality applied to $y=x(s_n)$ gives

$$
\Phi(x(s_n))+\langle \nabla\Phi(x(s_n)),p-x(s_n)\rangle\le \Phi(p).
$$

The first term tends to $l$. The inner-product term tends to $0$: by linearity in the second variable,

$$
\langle \nabla\Phi(x(s_n)),p-x(s_n)\rangle
=\langle \nabla\Phi(x(s_n)),p\rangle
-\langle \nabla\Phi(x(s_n)),x(s_n)\rangle,
$$

and both summands tend to $0$, the first because $p$ is constant and bounded and the second as shown above. Hence the left-hand side tends to $l$. Since every term is at most $\Phi(p)$, the limit comparison `le_of_tendsto` yields

$$
l\le \Phi(p)
$$

for every $p\in H$. Thus $l$ is a lower bound for $\Phi$ on all of $H$.

To relate this lower bound to the weak limit $z$, the proof introduces the extended-real function

$$
f:H\to \mathrm{EReal},\qquad f(u)=(\Phi(u):\mathrm{EReal}).
$$

Since the coercion $\mathbb R\to\mathrm{EReal}$ is continuous and $\Phi$ is continuous, $f$ is lower semicontinuous. The proof also shows that $f$ is quasiconvex. The cited equivalence `quasiconvexOn_univ_iff_convex_lowerLevelSet` says that quasiconvexity of $f$ on all of $H$ is equivalent to convexity of every lower level set

```math
\mathrm{lowerLevelSet} f \xi=\{u\in H\mid f(u)\le (\xi:\mathrm{EReal})\}.
```

The proof checks this convexity directly. If $a,b$ satisfy $\Phi(a)\le \xi$ and $\Phi(b)\le \xi$, then for positive weights $w_a,w_b$ with $w_a+w_b=1$, convexity of $\Phi$ gives

$$
\Phi(w_a a+w_b b)\le w_a\Phi(a)+w_b\Phi(b)\le w_a\xi+w_b\xi=\xi.
$$

Thus the lower level sets of $f$ are convex, so $f$ is quasiconvex. The proof uses `convex_iff_forall_pos` to check convexity by positive convex combinations, `exact_mod_cast` to pass between inequalities in $\mathbb R$ and their images in $\mathrm{EReal}$, and `mem_lowerLevelSet_iff` to translate membership in a lower level set into the corresponding inequality.

Now the cited theorem `weaklyLowerSemicontinuous_of_quasiconvexOn_univ` applies: a quasiconvex and lower semicontinuous function $f:H\to\mathrm{EReal}$ becomes lower semicontinuous when $H$ is equipped with the weak topology, i.e. $f\circ(\mathrm{toWeakSpace}_{\mathbb R,H})^{-1}$ is lower semicontinuous. Since $x(s_n)\rightharpoonup z$, this weak lower semicontinuity gives

$$
f(z)\le \liminf_n f(x(s_n)).
$$

But $f(x(s_n))=\Phi(x(s_n))\to l$, so

$$
\liminf_n f(x(s_n))=(l:\mathrm{EReal}).
$$

Therefore

$$
f(z)\le (l:\mathrm{EReal}),
$$

which, after casting back to real numbers, gives

$$
\Phi(z)\le l.
$$

On the other hand, the earlier lower-bound conclusion $l\le \Phi(p)$ for every $p$ gives in particular $l\le \Phi(z)$. Hence

$$
\Phi(z)=l.
$$

Then for every $y\in H$, the inequality $l\le \Phi(y)$ becomes

$$
\Phi(z)\le \Phi(y).
$$

Thus $z\in\mathrm{argminSet}\Phi$. This completes the proof of `hcluster`.

Finally, the proof applies the cited continuous-time Opial theorem `opial_continuous_time`. That theorem says: if $S\subseteq H$ is nonempty, if every weak cluster point of a curve $x(t)$ along sequences $t_n\to\infty$ lies in $S$, and if for every $z\in S$ the distance $`\|x(t)-z\|`$has a limit as$t\to\infty$, then there exists$z\in S$such that$x(t)\rightharpoonup z$. The proof instantiates this with

$$
S=\mathrm{argminSet}\Phi.
$$

The nonemptiness hypothesis is `hmin`. The cluster-point hypothesis is `hcluster`. The distance-limit hypothesis is `hdist`. The theorem's conclusion is exactly the desired statement: there exists $z\in\mathrm{argminSet}\Phi$ such that $x(t)$ converges weakly to $z$.

Throughout the proof, `intro` introduces an arbitrary object or hypothesis, `rw` and `simp` rewrite definitions and known identities, `exact` closes a goal by supplying a term of the required type, and `linarith` or `nlinarith` close arithmetic and inequality goals. The proof also uses `rcases` and `obtain` to eliminate existential and conjunction hypotheses, `calc` to organize chains of inequalities, `apply` to reduce a goal to a known lemma, and `exact_mod_cast` to transfer order statements between $\mathbb R$ and $\mathrm{EReal}$.

