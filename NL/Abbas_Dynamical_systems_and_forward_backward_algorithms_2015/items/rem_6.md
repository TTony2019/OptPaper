## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/rem_6.lean`

## Lean statement
```lean
theorem semigroup_strong_convergence_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (B : H → H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (S : Set H) (x : ℝ → H)
    (beta : ℝ) (hS : S.Nonempty) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hsolution : ∀ z, z ∈ S ↔ -B z ∈ ERealFunction.subdifferential Phi z)
    (horbit : ForwardBackwardSemigroupOrbit Phi B x)
    (hA : ∀ y, A y = ERealFunction.subdifferential Phi y + ({B y} : Set H))
    (hstrongly_monotone :
      (∃ rho : ℝ, 0 < rho ∧ ∀ ⦃a b u w⦄, u ∈ A a → w ∈ A b → rho * ‖a - b‖ ^ 2 ≤
          inner ℝ (a - b) (u - w)) ∨
      ((∀ r a : ℝ, IsCompact {y | ‖y‖ ≤ r ∧ (Phi y : EReal) ≤ (a : EReal)}) ∧
        ∃ a : ℝ, ∀ᶠ t in atTop, (Phi (x t) : EReal) ≤ (a : EReal))) :
    ∃ z ∈ S, Tendsto x atTop (nhds z)
```

## Statement explanation
The declaration is a strong-convergence theorem for a continuous forward-backward trajectory in a real Hilbert space $H$. The space $H$ is assumed to be a complete real inner product space. The data are a set-valued operator $A:H\to\mathcal P(H)$, a single-valued map $B:H\to H$, an extended-real function $\Phi:H\to \mathrm{Ioi}(\bot)$, a set $S\subseteq H$, a trajectory $x:\mathbb R\to H$, and a real number $\beta$. Here $\mathrm{Ioi}(\bot)$ means values strictly larger than the bottom extended real element, so $\Phi$ never takes the value $-\infty$. The hypothesis $hPhi$ says that $\Phi$ belongs to `ERealFunction.gammaZero H`, the admissibility class used by the forward-backward theory; the proof passes this hypothesis directly to `semigroup_convergence`.

The hypotheses are as follows. The set $S$ is nonempty. The number $\beta$ is positive. The map $B$ is $\beta$-cocoercive on all of $H$, meaning the Lean predicate `CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)` holds. The hypothesis `hsolution` says that for every $z$,

$$
z\in S \iff -B z\in \partial\Phi(z).
$$

Equivalently, $S$ is the set of solutions of $0\in \partial\Phi(z)+B(z)$. The hypothesis `horbit` says that $x$ is a forward-backward semigroup orbit for $\Phi$ and $B$. The proof uses the associated residual $r(t)=\mathrm{horbit.residual}(t)$, which satisfies

$$
r(t)=-\mathrm{deriv}x(t)
$$

and, for $t\ge0$,

```math
r(t)\in \partial\Phi(x(t))+\{B(x(t))\},
```

and whose norm $`t\mapsto \|r(t)\|`$is antitone on$[0,\infty)$.

The operator $A$ is linked to $\Phi$ and $B$ by

```math
hA:\quad \forall y,\quad A(y)=\partial\Phi(y)+\{B(y)\}.
```

Thus $A$ is the set-valued sum of the subdifferential of $\Phi$ and the singleton operator $B$. The final hypothesis `hstrongly_monotone` is a disjunction. The first alternative says that $A$ is $\rho$-strongly monotone for some $\rho\gt 0$: for all $a,b,u,w$,

```math
u\in A(a),\ w\in A(b)\implies
\rho\|a-b\|^2\le \langle a-b,u-w\rangle.
```

The second alternative says that all sublevel sets of $\Phi$ with bounded norm are compact, i.e.

```math
\forall r,a\in\mathbb R,\quad
\{y\mid \|y\|\le r,\ \Phi(y)\le a\}
```

is compact, and that along the trajectory $\Phi(x(t))$ is eventually bounded above by some real constant $a$, i.e.

$$
\exists a\in\mathbb R,\quad \forall^{\mathrm{eventually}}t,\quad \Phi(x(t))\le a.
$$

The conclusion is

$$
\exists z\in S,\quad x(t)\to z\quad\text{strongly in }H
$$

as $t\to\infty$. Thus the theorem upgrades the weak convergence obtained from the forward-backward semigroup theory to genuine norm convergence, under either strong monotonicity of $A$ or compactness of the sublevel sets of $\Phi$ together with eventual boundedness of $\Phi$ along the orbit.

## Lean proof
```lean
by
  obtain ⟨hdxint, ⟨z, hz, hxweak⟩, _⟩ :=
    semigroup_convergence Phi hPhi S B x beta hS hbeta hB hsolution horbit
  have hressqint : IntegrableOn (fun t ↦ ‖horbit.residual t‖ ^ 2) (Set.Ici 0) := by
    refine Integrable.congr hdxint ?_
    filter_upwards [horbit.residual_eq_neg_deriv] with t ht
    rw [ht, norm_neg]
  have hreszero := antitone_norm_sq_integrableOn_Ici_tendsto_zero horbit.residual
    horbit.residual_norm_antitone hressqint
  rcases hstrongly_monotone with hsm | ⟨hinfcompact, a, hPhiTail⟩
  · rcases hsm with ⟨rho, hrho, hsm⟩
    have hzeroA : 0 ∈ A z := by
      rw [hA z]
      refine Set.mem_add.mpr ⟨-B z, (hsolution z).mp hz, B z, by simp, by abel⟩
    have hresA (t : ℝ) (ht : 0 ≤ t) : horbit.residual t ∈ A (x t) := by
      rw [hA (x t)]
      exact horbit.residual_mem t ht
    have hupper : Tendsto (fun t ↦ rho⁻¹ * ‖horbit.residual t‖) atTop (nhds 0) := by
      simpa using hreszero.norm.const_mul rho⁻¹
    have hnorm : Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hupper_event : ∀ᶠ t in atTop, rho⁻¹ * ‖horbit.residual t‖ ∈
          Metric.ball 0 ε := hupper.eventually (Metric.ball_mem_nhds _ hε)
      apply Filter.eventually_atTop.mp
      filter_upwards [Filter.eventually_ge_atTop 0, hupper_event] with t ht hupper_t
      have hmono := hsm (hresA t ht) hzeroA
      have hinner : inner ℝ (x t - z) (horbit.residual t) ≤
          ‖x t - z‖ * ‖horbit.residual t‖ := real_inner_le_norm _ _
      have hmono' : rho * ‖x t - z‖ ^ 2 ≤ inner ℝ (x t - z) (horbit.residual t) := by
        simpa using hmono
      have hsquare : rho * ‖x t - z‖ ^ 2 ≤ ‖x t - z‖ * ‖horbit.residual t‖ :=
        le_trans hmono' hinner
      have hdistance : rho * ‖x t - z‖ ≤ ‖horbit.residual t‖ := by
        by_cases hzero : ‖x t - z‖ = 0
        · simp [hzero, norm_nonneg]
        · have hpos : 0 < ‖x t - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
          nlinarith
      have hbound : ‖x t - z‖ ≤ rho⁻¹ * ‖horbit.residual t‖ := by
        calc
          ‖x t - z‖ = rho⁻¹ * (rho * ‖x t - z‖) := by
            field_simp [hrho.ne']
          _ ≤ rho⁻¹ * ‖horbit.residual t‖ :=
            mul_le_mul_of_nonneg_left hdistance (by positivity)
      have hupper_lt : rho⁻¹ * ‖horbit.residual t‖ < ε := by
        have hnonneg : 0 ≤ rho⁻¹ * ‖horbit.residual t‖ :=
          mul_nonneg (le_of_lt (inv_pos.mpr hrho)) (norm_nonneg _)
        simpa [Real.dist_eq, abs_of_nonneg hnonneg, abs_of_pos hrho] using hupper_t
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using lt_of_le_of_lt hbound hupper_lt
    exact ⟨z, hz, tendsto_iff_norm_sub_tendsto_zero.mpr hnorm⟩
  · obtain ⟨C, hC⟩ := eventually_norm_le_of_tendsto_weakly_trajectory hxweak
    let R : ℝ := max 1 C
    let K : Set H := {y | ‖y‖ ≤ R ∧ (Phi y : EReal) ≤ (a : EReal)}
    have hK : IsCompact K := hinfcompact R a
    have hEventuallyK : ∀ᶠ t in atTop, x t ∈ K := by
      filter_upwards [hC, hPhiTail] with t htC htPhi
      exact ⟨le_trans htC (le_max_right _ _), htPhi⟩
    have hweakScalar : ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun t => ell (x t)) atTop (nhds (ell z)) := by
      intro ell
      let u : H := (InnerProductSpace.toDual ℝ H).symm ell
      have hu := (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ H z) |>.comp hxweak
      have hrepr (y : H) : ell y = inner ℝ y u := by
        calc
          ell y = inner ℝ u y := (InnerProductSpace.toDual_symm_apply).symm
          _ = inner ℝ y u := real_inner_comm _ _
      simpa only [hrepr] using hu
    exact ⟨z, hz,
      strong_tendsto_of_eventually_compact_and_weak_scalar_convergence x z K hK hEventuallyK
        hweakScalar⟩
```

## Proof explanation
The proof begins by applying `semigroup_convergence` to $\Phi$, $S$, $B$, $x$, and $\beta$, using the hypotheses $hPhi$, $hS$, $hbeta$, $hB$, $hsolution$, and $horbit$. That theorem provides three facts. First, the derivative of the trajectory is square-integrable:

```math
\int_0^\infty \|\mathrm{deriv}x(t)\|^2\,dt<\infty.
```

Second, there is a point $z\in S$ such that the trajectory converges weakly to $z$:

$$
\mathrm{toWeakSpace}(x(t))\to \mathrm{toWeakSpace}(z).
$$

Third, for every solution point, $B(x(t))$ converges to the corresponding value of $B$; the proof discards this third part. The `obtain` command destructures the triple into `hdxint`, the weak-limit witness $\langle z,hz,hxweak\rangle$, and an ignored third component.

Next the proof shows that the squared norm of the residual is integrable. Since the residual satisfies $r(t)=-\mathrm{deriv}x(t)$, we have

```math
\|r(t)\|^2=\|-\mathrm{deriv}x(t)\|^2=\|\mathrm{deriv}x(t)\|^2.
```

The tactic `Integrable.congr` transfers the integrability of $`t\mapsto \|\mathrm{deriv}x(t)\|^2`$to$`t\mapsto \|r(t)\|^2`$, because the two functions agree almost everywhere. The `filter_upwards` and `rw [ht, norm_neg]` steps are exactly this pointwise identification using the orbit identity for the residual.

The theorem `antitone_norm_sq_integrableOn_Ici_tendsto_zero` is then applied to the residual $r$. Its mathematical content is: for a normed additive commutative group $E$ and a function $r:\mathbb R\to E$, if $`t\mapsto \|r(t)\|`$is antitone on$[0,\infty)$and$`t\mapsto \|r(t)\|^2`$is integrable on$[0,\infty)$, then

$$
r(t)\to 0\quad\text{as }t\to\infty.
$$

The idea is that a nonincreasing nonnegative function whose square is integrable on a half-line must tend to $0$; otherwise its square would have positive lower bounds on arbitrarily long intervals. The hypotheses required by the lemma are supplied by `horbit.residual_norm_antitone` and `hressqint`, giving `hreszero`, i.e.

$$
r(t)\to 0.
$$

The proof now splits on `hstrongly_monotone`.

In the first case, $A$ is $\rho$-strongly monotone for some $\rho\gt 0$. The proof first shows that $0\in A(z)$. Since $z\in S$, the solution hypothesis gives $-B z\in \partial\Phi(z)$. By `hA`, $`A(z)=\partial\Phi(z)+\{B(z)\}`$. The sum of the element$-B z\in \partial\Phi(z)$and the singleton element$`B z\in\{B z\}`$is$0$. The `Set.mem_add.mpr` step constructs this membership, and `abel` verifies $-B z+B z=0$. Hence $0\in A(z)$.

For every $t\ge0$, the residual satisfies $r(t)\in A(x(t))$. Indeed, by `hA` it is enough to show

```math
r(t)\in \partial\Phi(x(t))+\{B(x(t))\},
```

which is exactly the orbit residual membership `horbit.residual_mem t ht`.

Since $r(t)\to0$, its norm also tends to $0$. Multiplying by the constant $\rho^{-1}$ gives

```math
\rho^{-1}\|r(t)\|\to 0.
```

This is the `hupper` step, obtained from the continuity of the norm and of scalar multiplication.

The proof then shows

```math
\|x(t)-z\|\to 0.
```

It uses the metric characterization of convergence: for every $\varepsilon\gt 0$, one must eventually have $`\|x(t)-z\|<\varepsilon`$. Since$`\rho^{-1}\|r(t)\|\to0`$, eventually

```math
\rho^{-1}\|r(t)\|<\varepsilon,
```

and also eventually $t\ge0$. For such a $t$, apply strong monotonicity of $A$ with

$$
a=x(t),\quad b=z,\quad u=r(t),\quad w=0.
$$

Because $r(t)\in A(x(t))$ and $0\in A(z)$, strong monotonicity gives

```math
\rho\|x(t)-z\|^2
\le \langle x(t)-z,\, r(t)-0\rangle
= \langle x(t)-z,r(t)\rangle.
```

The inequality `real_inner_le_norm` gives the Cauchy-Schwarz bound

```math
\langle x(t)-z,r(t)\rangle
\le \|x(t)-z\|\,\|r(t)\|.
```

Therefore

```math
\rho\|x(t)-z\|^2
\le \|x(t)-z\|\,\|r(t)\|.
```

If $`\|x(t)-z\|=0`$, the desired distance bound is immediate. Otherwise$`\|x(t)-z\|>0`$, and dividing the inequality by this positive quantity yields

```math
\rho\|x(t)-z\|\le \|r(t)\|.
```

Multiplying by $\rho^{-1}\gt 0$ gives

```math
\|x(t)-z\|\le \rho^{-1}\|r(t)\|<\varepsilon.
```

This is the key estimate. The `nlinarith` step performs the division by the positive norm, while `field_simp` and `positivity` handle the factor $\rho^{-1}$. Thus $`\|x(t)-z\|\to0`$, and by `tendsto_iff_norm_sub_tendsto_zero` this is equivalent to

$$
x(t)\to z\quad\text{strongly}.
$$

The witness $z\in S$ is already available, so the first disjunct is complete.

In the second case, the strong monotonicity of $A$ is replaced by compactness of the sublevel sets of $\Phi$ and eventual boundedness of $\Phi$ along the trajectory. The proof has already obtained weak convergence $x(t)\rightharpoonup z$. The lemma `eventually_norm_le_of_tendsto_weakly_trajectory` now gives a real constant $C$ such that eventually

```math
\|x(t)\|\le C.
```

Its mathematical content is that a weakly convergent trajectory in a Hilbert space is eventually bounded in norm.

The proof defines

$$
R=\max(1,C)
$$

and

```math
K=\{y\mid \|y\|\le R,\ \Phi(y)\le a\},
```

where $a$ is the real bound supplied by the second part of `hstrongly_monotone`. By the compactness assumption, $K$ is compact. Since eventually $`\|x(t)\|\le C\le R`$and eventually$\Phi(x(t))\le a$, the trajectory is eventually contained in$K$. The `filter_upwards` step combines those two eventual properties.

It remains to upgrade the weak convergence of $x(t)$ to $z$ to convergence against every continuous linear functional. For an arbitrary continuous linear functional $\ell:H\to\mathbb R$, the Riesz representation theorem for real Hilbert spaces gives a vector $u\in H$ such that

$$
\ell(y)=\langle u,y\rangle=\langle y,u\rangle.
$$

The theorem `weakSpace_continuous_inner_right` states that for fixed $u$, the map on the weak space

$$
X\mapsto \left\langle (\mathrm{toWeakSpace})^{-1}X,u\right\rangle
$$

is continuous. Composing this continuity with the weak convergence of $x(t)$ to $z$ gives

$$
\langle x(t),u\rangle\to \langle z,u\rangle.
$$

Using the representation of $\ell$, this becomes

$$
\ell(x(t))\to \ell(z)
$$

for every continuous linear functional $\ell$.

Finally, the theorem `strong_tendsto_of_eventually_compact_and_weak_scalar_convergence` is applied with $x$, $x^*=z$, and the compact set $K$. Its content is: if a trajectory is eventually contained in a compact set $K$ and every continuous linear functional $\ell$ satisfies $\ell(x(t))\to\ell(x^*)$, then $x(t)\to x^*$ strongly. The hypotheses have just been established: $K$ is compact, $x(t)\in K$ eventually, and $\ell(x(t))\to\ell(z)$ for all $\ell$. Therefore

$$
x(t)\to z\quad\text{strongly in }H,
$$

with $z\in S$. This concludes the proof in the second case, and hence the theorem holds under either alternative of `hstrongly_monotone`.

