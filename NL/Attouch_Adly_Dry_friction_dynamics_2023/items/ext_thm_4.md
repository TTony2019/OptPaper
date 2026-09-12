## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_thm_4.lean`

## Lean statement
```lean
theorem classical_gradient_flow_value_rate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ : ℝ} (f : H → ℝ) (y dy : ℝ → H) (fstar : ℝ)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (hregular : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hflow : ∀ s ∈ Set.Ici s₀, dy s + gradient f (y s) = 0)
    (hmin : ∃ xstar, f xstar = fstar ∧ ∀ x, fstar ≤ f x) :
    Filter.Tendsto (fun s : ℝ => s * (f (y s) - fstar)) Filter.atTop (nhds 0)
```

## Statement explanation
`classical_gradient_flow_value_rate` is a theorem about the decay rate of the value of a convex function along a classical gradient flow. The ambient space \(H\) is a real Hilbert space: it is a complete normed additive group with a real inner product. The theorem has the following data and hypotheses.

- \(s_0\) is a real number, serving as the initial time of the flow.
- \(f : H \to \mathbb{R}\) is a real-valued function on \(H\).
- \(y : \mathbb{R} \to H\) is the trajectory, and \(dy : \mathbb{R} \to H\) is its derivative.
- \(f^\star \in \mathbb{R}\) is intended to be the minimal value of \(f\).
- \(f\) is convex on all of \(H\), expressed as \( \operatorname{ConvexOn} \mathbb{R} \operatorname{Set.univ} f\).
- \(f\) is differentiable over \(\mathbb{R}\), expressed as \( \operatorname{Differentiable} \mathbb{R} f\).
- For every \(s \in [s_0,\infty)\), the curve \(y\) has derivative \(dy(s)\) at time \(s\):
  \[
  \operatorname{HasDerivAt} y (dy(s)) s.
  \]
- For every \(s \in [s_0,\infty)\), the flow equation holds:
  \[
  dy(s) + \nabla f(y(s)) = 0,
  \]
  equivalently \(dy(s) = -\nabla f(y(s))\). This is exactly the classical gradient-flow equation \(y'(s) = -\nabla f(y(s))\).
- There exists \(x^\star \in H\) such that
  \[
  f(x^\star) = f^\star
  \qquad\text{and}\qquad
  \forall x \in H,\ f^\star \le f(x).
  \]
  Thus \(f^\star\) is a global minimum of \(f\), attained at \(x^\star\).

The conclusion is
\[
\operatorname{Tendsto}
\left(s \mapsto s\bigl(f(y(s)) - f^\star\bigr)\right)
\operatorname{atTop}
(\operatorname{nhds} 0),
\]
which means
\[
s\bigl(f(y(s)) - f^\star\bigr) \longrightarrow 0
\qquad\text{as } s \to \infty.
\]
Since \(f^\star\) is a global minimum, the value gap \(f(y(s))-f^\star\) is nonnegative. Therefore the conclusion says that this gap tends to zero faster than \(1/s\), along the gradient flow.

## Lean proof
```lean
by
  have hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (gradient f x) v := by
    intro x v
    rw [(hdiff x).hasGradientAt.hasFDerivAt.fderiv]
    rfl
  rcases hmin with ⟨xstar, hxstar, hmin_le⟩
  let gap : ℝ → ℝ := fun s => f (y s) - fstar
  let dist2 : ℝ → ℝ := fun s => ‖y s - xstar‖ ^ 2
  have hgap_nonneg (s : ℝ) : 0 ≤ gap s := by
    dsimp [gap]
    linarith [hmin_le (y s)]
  have hgap_deriv (s : ℝ) (hs : s ∈ Set.Ici s₀) :
      HasDerivAt gap (inner ℝ (gradient f (y s)) (dy s)) s := by
    have hcomp := hdiff.differentiableAt.hasFDerivAt.comp_hasDerivAt s (hregular s hs)
    simpa [gap, Function.comp_def, hgradient] using hcomp.sub_const fstar
  have hgap_anti : AntitoneOn gap (Set.Ici s₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici s₀)
    · intro s hs
      exact (hgap_deriv s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hgap_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Set.Ici s₀ := interior_subset hs
      rw [(hgap_deriv s hs').deriv]
      have hdy : dy s = -gradient f (y s) := eq_neg_of_add_eq_zero_left (hflow s hs')
      rw [hdy, inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_nonpos.mpr (sq_nonneg _)
  have hdist_deriv (s : ℝ) (hs : s ∈ Set.Ici s₀) :
      HasDerivAt dist2 (2 * inner ℝ (y s - xstar) (dy s)) s := by
    simpa [dist2] using ((hregular s hs).sub_const xstar).norm_sq
  have hdist_bound (s : ℝ) (hs : s ∈ Set.Ici s₀) :
      deriv dist2 s ≤ -2 * gap s := by
    have hsupport := convex_gradient_support f fstar hconvex hdiff hxstar
      (x := y s)
    have hdy : dy s = -gradient f (y s) := eq_neg_of_add_eq_zero_left (hflow s hs)
    rw [(hdist_deriv s hs).deriv, hdy, inner_neg_right, real_inner_comm]
    dsimp [gap] at hsupport ⊢
    nlinarith
  have hdist_anti : AntitoneOn dist2 (Set.Ici s₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici s₀)
    · intro s hs
      exact (hdist_deriv s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hdist_deriv s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Set.Ici s₀ := interior_subset hs
      exact (hdist_bound s hs').trans (by nlinarith [hgap_nonneg s])
  have hhalf_bound (t : ℝ) (ht0 : 0 ≤ t) (ht : 2 * s₀ ≤ t) :
      t * gap t ≤ dist2 (t / 2) - dist2 t := by
    have hhalf : s₀ ≤ t / 2 := by linarith
    have hq_anti : AntitoneOn (fun r : ℝ => dist2 r + 2 * gap t * r) (Set.Icc (t / 2) t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      · intro r hr
        have hr' : r ∈ Set.Ici s₀ := hhalf.trans hr.1
        have hq_deriv : HasDerivAt (fun u : ℝ => dist2 u + 2 * gap t * u)
            (2 * inner ℝ (y r - xstar) (dy r) + 2 * gap t) r := by
          convert (hdist_deriv r hr').add ((hasDerivAt_id r).const_mul (2 * gap t)) using 1
          all_goals ring_nf
        exact hq_deriv.continuousAt.continuousWithinAt
      · intro r hr
        have hrIcc : r ∈ Set.Icc (t / 2) t := interior_subset hr
        have hr' : r ∈ Set.Ici s₀ := hhalf.trans hrIcc.1
        have hq_deriv : HasDerivAt (fun u : ℝ => dist2 u + 2 * gap t * u)
            (2 * inner ℝ (y r - xstar) (dy r) + 2 * gap t) r := by
          convert (hdist_deriv r hr').add ((hasDerivAt_id r).const_mul (2 * gap t)) using 1
          all_goals ring_nf
        exact hq_deriv.differentiableAt.differentiableWithinAt
      · intro r hr
        have hrIcc : r ∈ Set.Icc (t / 2) t := interior_subset hr
        have hr' : r ∈ Set.Ici s₀ := hhalf.trans hrIcc.1
        have ht' : t ∈ Set.Ici s₀ := hhalf.trans (by linarith)
        have hgap_le : gap t ≤ gap r := hgap_anti hr' ht' hrIcc.2
        have hq_deriv : HasDerivAt (fun u : ℝ => dist2 u + 2 * gap t * u)
            (2 * inner ℝ (y r - xstar) (dy r) + 2 * gap t) r := by
          convert (hdist_deriv r hr').add ((hasDerivAt_id r).const_mul (2 * gap t)) using 1
          all_goals ring_nf
        rw [hq_deriv.deriv]
        have hderiv_eq : deriv dist2 r = 2 * inner ℝ (y r - xstar) (dy r) :=
          (hdist_deriv r hr').deriv
        nlinarith [hdist_bound r hr']
    have hleft : t / 2 ∈ Set.Icc (t / 2) t := ⟨le_rfl, by linarith⟩
    have hright : t ∈ Set.Icc (t / 2) t := ⟨by linarith, le_rfl⟩
    have hq := hq_anti hleft hright (by linarith)
    dsimp at hq
    nlinarith
  let D : ℝ → ℝ := fun r => dist2 (max r s₀)
  have hD_nonneg (r : ℝ) : 0 ≤ D r := by
    dsimp [D, dist2]
    exact sq_nonneg _
  have hD_anti : Antitone D := by
    intro a b hab
    apply hdist_anti
    · show s₀ ≤ max a s₀
      exact le_max_right _ _
    · show s₀ ≤ max b s₀
      exact le_max_right _ _
    · exact max_le_max_right s₀ hab
  have hD_bdd : BddBelow (Set.range D) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact hD_nonneg r
  have hD_lim : Filter.Tendsto D Filter.atTop (nhds (sInf (Set.range D))) :=
    tendsto_atTop_ciInf hD_anti hD_bdd
  have hhalf_top : Filter.Tendsto (fun t : ℝ => t / 2) Filter.atTop Filter.atTop := by
    exact (Filter.tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr Filter.tendsto_id
  have hdist_lim : Filter.Tendsto dist2 Filter.atTop (nhds (sInf (Set.range D))) := by
    apply hD_lim.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨s₀, fun t ht => ht⟩] with t ht
    simp [D, max_eq_left ht]
  have hdist_half_lim : Filter.Tendsto (fun t : ℝ => dist2 (t / 2)) Filter.atTop
      (nhds (sInf (Set.range D))) := by
    apply (hD_lim.comp hhalf_top).congr'
    filter_upwards [hhalf_top.eventually (Filter.eventually_atTop.2 ⟨s₀, fun t ht => ht⟩)] with t ht
    simp [D, max_eq_left ht]
  have hdrop_lim : Filter.Tendsto (fun t : ℝ => dist2 (t / 2) - dist2 t) Filter.atTop (nhds 0) := by
    simpa using hdist_half_lim.sub hdist_lim
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_atTop.2 ⟨(0 : ℝ), fun t ht => ht⟩] with t ht
    exact mul_nonneg ht (hgap_nonneg t)
  · filter_upwards [Filter.eventually_atTop.2 ⟨max 0 (2 * s₀), fun t ht => ht⟩] with t ht
    exact hhalf_bound t (le_trans (le_max_left _ _) ht) (le_trans (le_max_right _ _) ht)
  · simpa [gap] using hdrop_lim
```

## Proof explanation
The proof begins by recording how the Fréchet derivative of \(f\) is represented by its gradient. For every \(x \in H\) and \(v \in H\), the proof establishes
\[
\operatorname{fderiv}_{\mathbb R} f(x)(v)
=
\langle \nabla f(x), v\rangle .
\]
This is the standard identification, in a real inner product space, of the derivative of a differentiable real-valued function with the inner product against its gradient. The Lean step uses differentiability of \(f\) at \(x\), obtains the Fréchet derivative from the gradient, and then closes by definitional equality.

Next, the minimization hypothesis is unpacked. The proof obtains an element \(x^\star\) such that
\[
f(x^\star)=f^\star
\qquad\text{and}\qquad
\forall x,\ f^\star \le f(x).
\]
It then defines two real-valued functions along the trajectory:
\[
g(s) = f(y(s)) - f^\star,
\qquad
d(s) = \lVert y(s)-x^\star\rVert^2.
\]
Here \(g(s)\) is the value gap and \(d(s)\) is the squared distance from the trajectory to the minimizer \(x^\star\).

The proof first shows \(g(s) \ge 0\) for every \(s\). Indeed,
\[
g(s)=f(y(s))-f^\star \ge 0
\]
because \(f^\star \le f(x)\) for every \(x\), in particular for \(x=y(s)\). This is the arithmetic step handled by `linarith`.

Next, the derivative of \(g\) is computed. For \(s \in [s_0,\infty)\), the chain rule applied to \(f \circ y\) gives that the derivative of \(f(y(s))\) is the derivative of \(f\) at \(y(s)\) applied to \(dy(s)\). Using the gradient representation above, this becomes
\[
g'(s) = \langle \nabla f(y(s)), dy(s)\rangle .
\]
Subtracting the constant \(f^\star\) does not change the derivative.

This derivative is nonpositive. Indeed, from the flow equation,
\[
dy(s) = -\nabla f(y(s)),
\]
so
\[
g'(s)
=
\langle \nabla f(y(s)), -\nabla f(y(s))\rangle
=
-\lVert \nabla f(y(s))\rVert^2
\le 0.
\]
The proof then invokes the general fact `antitoneOn_of_deriv_nonpos`: on a convex set, if a function is continuous, differentiable on the interior, and has nonpositive derivative on the interior, then it is nonincreasing. Applying this on the convex interval \( [s_0,\infty) \) shows that \(g\) is antitone on \( [s_0,\infty) \). Thus, if \(s_0 \le r \le t\), then
\[
g(t) \le g(r).
\]

The proof then studies the squared distance \(d(s)\). For \(s \in [s_0,\infty)\), differentiating \(\lVert y(s)-x^\star\rVert^2\) gives
\[
d'(s) = 2\langle y(s)-x^\star, dy(s)\rangle .
\]
This is the usual derivative formula for the squared norm of a differentiable vector-valued function.

The crucial estimate for \(d'(s)\) uses the cited result `convex_gradient_support`. In concrete terms, that theorem says that if \(f\) is convex on all of \(H\), differentiable, and \(x^\star\) satisfies \(f(x^\star)=f^\star\), then for every \(x \in H\),
\[
f(x)-f^\star \le
\langle \nabla f(x), x-x^\star\rangle .
\]
This is the first-order support inequality for convex differentiable functions: the tangent plane at \(x\) lies below the graph of \(f\). Specialized to \(x=y(s)\), it gives
\[
g(s) = f(y(s))-f^\star
\le
\langle \nabla f(y(s)), y(s)-x^\star\rangle .
\]
Using \(dy(s)=-\nabla f(y(s))\) and symmetry of the real inner product, the proof obtains
\[
d'(s)
=
2\langle y(s)-x^\star, dy(s)\rangle
=
-2\langle y(s)-x^\star, \nabla f(y(s))\rangle
=
-2\langle \nabla f(y(s)), y(s)-x^\star\rangle
\le
-2g(s).
\]
Since \(g(s)\ge 0\), this also gives \(d'(s)\le 0\). Applying `antitoneOn_of_deriv_nonpos` again, now to \(d\) on \( [s_0,\infty) \), shows that \(d\) is nonincreasing along the flow.

The next major step is the key inequality
\[
t g(t) \le d(t/2)-d(t)
\]
for \(t \ge 0\) and \(2s_0 \le t\). To prove it, the proof fixes such a \(t\) and considers the auxiliary function
\[
q(r)=d(r)+2g(t)r
\]
on the interval \( [t/2,t]\). It computes
\[
q'(r)
=
d'(r)+2g(t)
=
2\langle y(r)-x^\star, dy(r)\rangle+2g(t).
\]
For \(r \in [t/2,t]\), the inequalities \(r \ge s_0\) and \(t \ge s_0\) hold. Also \(r \le t\), and since \(g\) is nonincreasing on \( [s_0,\infty) \), we have
\[
g(t) \le g(r).
\]
Combining this with the earlier bound
\[
d'(r) \le -2g(r)
\]
gives
\[
q'(r) \le -2g(r)+2g(t) \le 0.
\]
Therefore \(q\) is nonincreasing on \( [t/2,t]\), so \(q(t) \le q(t/2)\). Expanding this inequality yields
\[
d(t)+2t g(t) \le d(t/2)+t g(t),
\]
hence
\[
t g(t) \le d(t/2)-d(t).
\]
The arithmetic steps here are handled by `nlinarith`, while `convert` and `ring_nf` are used to identify the derivative of the auxiliary function.

The proof now constructs a globally defined antitone function
\[
D(r)=d(\max(r,s_0)).
\]
For every \(r\), \(D(r)\ge 0\), since it is a squared norm. It is antitone: if \(a \le b\), then \(\max(a,s_0)\le \max(b,s_0)\), and since \(d\) is antitone on \( [s_0,\infty) \), this gives \(D(b)\le D(a)\). Also \(D\) is bounded below by \(0\). By the monotone convergence fact `tendsto_atTop_ciInf`, an antitone function bounded below tends at \(+\infty\) to the infimum of its range. Thus
\[
D(r) \to L
\qquad\text{as } r\to\infty,
\]
where
\[
L=\inf\{\,D(r):r\in\mathbb R\,\}.
\]
For all sufficiently large \(r\), one has \(r\ge s_0\), so \(\max(r,s_0)=r\) and \(D(r)=d(r)\). Hence \(d(s)\to L\) as \(s\to\infty\). Similarly, since \(s\mapsto s/2\to\infty\), one has \(D(s/2)\to L\). For large \(s\), \(s/2\ge s_0\), so \(D(s/2)=d(s/2)\). Therefore
\[
d(s/2)\to L
\qquad\text{and}\qquad
d(s)\to L,
\]
and hence
\[
d(s/2)-d(s) \to L-L=0.
\]
This is the content of the intermediate limit `hdrop_lim`.

Finally, the squeeze argument is applied to the desired function
\[
s \mapsto s\bigl(f(y(s))-f^\star\bigr)=s g(s).
\]
For eventually all \(s\), one has \(s\ge 0\), and since \(g(s)\ge 0\), the product \(s g(s)\) is nonnegative. For eventually all \(s\), namely once \(s\ge \max(0,2s_0)\), the key inequality gives
\[
s g(s)
\le
d(s/2)-d(s).
\]
The upper bound \(d(s/2)-d(s)\) tends to \(0\), as shown above. The squeeze theorem `squeeze_zero'` therefore yields
\[
s g(s) \to 0
\qquad\text{as } s\to\infty.
\]
Since \(g(s)=f(y(s))-f^\star\), this is exactly
\[
s\bigl(f(y(s))-f^\star\bigr) \to 0,
\]
which is the claimed conclusion.

