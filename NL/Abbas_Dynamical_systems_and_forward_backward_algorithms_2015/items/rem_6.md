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
Let \(H\) be a complete real inner product space; in Lean this is expressed by the typeclasses `NormedAddCommGroup H`, `InnerProductSpace ℝ H`, and `CompleteSpace H`.  
The theorem involves:

- \(A:H\to \operatorname{Set} H\), a set-valued operator.
- \(B:H\to H\), a single-valued operator.
- \(\Phi:H\to \operatorname{Set.Ioi}(\bot:\operatorname{EReal})\), an extended-real-valued function on \(H\) whose values are strictly above the bottom element of \( \operatorname{EReal} \), i.e. never \(-\infty\). The hypothesis `hPhi` says \(\Phi\) belongs to the class `ERealFunction.gammaZero H`.
- \(S\subseteq H\), a set.
- \(x:\mathbb{R}\to H\), a trajectory parameterized by real time.
- \(\beta\in\mathbb{R}\), a parameter.

The hypotheses are:

- \(S\neq\varnothing\).
- \(0<\beta\).
- \(B\) is \(\beta\)-cocoercive on the whole space; the `Set.univ` argument means the cocoercivity condition is global.
- For every \(z\), \(z\in S\) iff \(-Bz\) belongs to the subdifferential \(\partial\Phi(z)\).
- \(x\) is a forward-backward semigroup orbit for \(\Phi\) and \(B\).
- For every \(y\), \(A(y)=\partial\Phi(y)+\{B(y)\}\), where the sum is set addition.
- Either:
  1. there exists \(\rho>0\) such that for all \(a,b,u,w\), if \(u\in A(a)\) and \(w\in A(b)\), then  
     \[
     \rho\|a-b\|^2\le \langle a-b,u-w\rangle_{\mathbb{R}};
     \]
     this is a strong monotonicity condition for \(A\).
  2. or, for every real \(r,a\), the sublevel set  
     \[
     \{y\mid \|y\|\le r \text{ and } \Phi(y)\le a\}
     \]
     is compact, and there exists some real \(a\) such that eventually along `atTop`, \(\Phi(x(t))\le a\).

The conclusion is that there exists \(z\in S\) such that \(x(t)\to z\) in \(H\) as \(t\to\infty\), i.e. \(Tendsto\ x\ atTop\ (nhds\ z)\).

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
The proof begins by invoking the previously proved lemma `semigroup_convergence` with the hypotheses on \(\Phi\), \(S\), \(B\), \(x\), \(\beta\), etc. This returns three pieces of data: an integrability property `hdxint`, a point \(z\in S\), and weak convergence `hxweak` of \(x\) to \(z\). The third returned component is ignored.

Next, the proof establishes that the squared norm of the forward-backward residual is integrable on \([0,\infty)\). The command `have hressqint` does this by using `Integrable.congr` to transfer the integrability from `hdxint` to the residual. The proof uses `filter_upwards` with the orbit property `horbit.residual_eq_neg_deriv` and then `rw [ht, norm_neg]`: the residual equals minus the derivative along the orbit, and the norm of a vector equals the norm of its negative.

The lemma `antitone_norm_sq_integrableOn_Ici_tendsto_zero` is then applied. Since the residual norm is antitone and its square is integrable on \([0,\infty)\), the residual itself tends to \(0\) at infinity. This gives `hreszero`.

The proof then splits on the two alternatives in `hstrongly_monotone` using `rcases`.

### First alternative: strong monotonicity

In the first alternative, one obtains \(\rho>0\) and the strong monotonicity inequality `hsm`.

The proof first shows `0 ∈ A z`. Using `hA z`, it rewrites \(A(z)\) as \(\partial\Phi(z)+\{B(z)\}\). Since \(z\in S\), the hypothesis `hsolution` gives \(-B(z)\in\partial\Phi(z)\). Also \(B(z)\) belongs to the singleton \(\{B(z)\}\). Their sum is \(0\), so \(0\in A(z)\).

It also records that for every \(t\ge 0\), the residual satisfies
\[
\operatorname{residual}(t)\in A(x(t)).
\]
This is `horbit.residual_mem`.

Since the residual tends to \(0\), multiplying its norm by the constant \(\rho^{-1}\) also tends to \(0\). This gives `hupper`.

The proof now wants to show \(\|x(t)-z\|\to 0\). It uses the metric characterization of tendsto. For any \(\varepsilon>0\), eventually two things hold: \(t\ge 0\), and
\[
\rho^{-1}\|\operatorname{residual}(t)\|<\varepsilon.
\]
For such a \(t\), strong monotonicity is applied to the pair
\[
a=x(t),\qquad b=z,\qquad u=\operatorname{residual}(t)\in A(x(t)),\qquad w=0\in A(z).
\]
Thus
\[
\rho\|x(t)-z\|^2
\le
\langle x(t)-z,\operatorname{residual}(t)\rangle.
\]
The Cauchy-Schwarz inequality, via `real_inner_le_norm`, gives
\[
\langle x(t)-z,\operatorname{residual}(t)\rangle
\le
\|x(t)-z\|\,\|\operatorname{residual}(t)\|.
\]
Therefore
\[
\rho\|x(t)-z\|^2
\le
\|x(t)-z\|\,\|\operatorname{residual}(t)\|.
\]
If \(\|x(t)-z\|\neq 0\), one divides by the positive norm, using `by_cases` and `nlinarith`, to get
\[
\rho\|x(t)-z\|\le \|\operatorname{residual}(t)\|.
\]
If the norm is zero, the inequality is trivial.

Then, using `field_simp` and `mul_le_mul_of_nonneg_left`, the proof multiplies by \(\rho^{-1}\) to obtain
\[
\|x(t)-z\|\le \rho^{-1}\|\operatorname{residual}(t)\|.
\]
The right-hand side is eventually smaller than \(\varepsilon\), so \(\|x(t)-z\|<\varepsilon\). Thus \(\|x(t)-z\|\to 0\). Finally, the equivalence
\[
x(t)\to z
\quad\iff\quad
\|x(t)-z\|\to 0
\]
is used through `tendsto_iff_norm_sub_tendsto_zero` to conclude strong convergence of \(x\) to \(z\).

### Second alternative: compact sublevel sets

In the second alternative, the proof gets constants and eventual bounds from weak convergence. The lemma `eventually_norm_le_of_tendsto_weakly_trajectory` applied to `hxweak` gives a constant \(C\) such that eventually
\[
\|x(t)\|\le C.
\]
Set \(R=\max(1,C)\) and define the set
\[
K=\{y\mid \|y\|\le R \text{ and } \Phi(y)\le a\}.
\]
By the compactness assumption, \(K\) is compact. The proof then shows that eventually \(x(t)\in K\): the norm bound follows from \(\|x(t)\|\le C\le R\), and the \(\Phi\)-bound is exactly the eventual bound from the hypothesis. This is done with `filter_upwards`.

Next, the proof shows that for every continuous linear functional \(\ell:H\to_{\mathbb{R}}\mathbb{R}\),
\[
\ell(x(t))\to \ell(z).
\]
Via the Riesz representation theorem for real Hilbert spaces, \(\ell\) is represented by a vector \(u\), so that
\[
\ell(y)=\langle y,u\rangle.
\]
The weak convergence `hxweak` is in the weak space. The map \(y\mapsto \langle y,u\rangle\) is continuous for the weak topology, so composing it with the weak convergence of \(x(t)\) to \(z\) gives
\[
\langle x(t),u\rangle\to \langle z,u\rangle.
\]
After rewriting using the Riesz representation, this becomes
\[
\ell(x(t))\to \ell(z).
\]

Finally, the lemma `strong_tendsto_of_eventually_compact_and_weak_scalar_convergence` upgrades this situation to strong convergence: since the trajectory is eventually in the compact set \(K\) and all continuous linear functionals converge to their values at \(z\), the trajectory converges strongly to \(z\). This gives the desired point \(z\in S\).

