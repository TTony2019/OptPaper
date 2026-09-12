## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/rem_1.lean`

## Lean statement
```lean
theorem subdifferential_enlargement_remark
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : ERealFunction.IsProper f)
    (hclosed : IsClosed (ERealFunction.epigraph f))
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (ε : ℝ) (hε : 0 ≤ ε) :
    (subdifferential f).IsMaximalMonotone ∧
      ∀ x, epsilonSubdifferential f ε x ⊆ epsilonEnlargement (subdifferential f) ε hε x
```

## Statement explanation
The declaration `subdifferential_enlargement_remark` is a theorem about a complete real Hilbert space \(H\). The hypothesis `[NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]` means that \(H\) is a real inner product space whose norm is complete. The function \(f : H \to \mathrm{EReal}\) takes values in the extended real line, and the hypothesis `hf : ERealFunction.IsProper f` says that \(f\) is proper: for every \(x \in H\), \(f(x) \neq -\infty\), and the effective domain of \(f\) is nonempty. The hypothesis `hclosed : IsClosed (ERealFunction.epigraph f)` says that the epigraph of \(f\) is closed, while `hconvex : Convex ℝ (ERealFunction.epigraph f)` says that this epigraph is convex over \(\mathbb R\). Finally, \(\varepsilon\) is a real number with \(0 \le \varepsilon\).

The conclusion is a conjunction of two statements. First, the set-valued operator \(\partial f\), the subdifferential of \(f\), is maximal monotone. Second, for every \(x \in H\), the \(\varepsilon\)-subdifferential of \(f\) at \(x\) is contained in the \(\varepsilon\)-enlargement of the ordinary subdifferential \(\partial f\) at \(x\):

\[
\partial_\varepsilon f(x) \subseteq \mathcal E_\varepsilon(\partial f)(x).
\]

Here the ordinary subdifferential is the set-valued operator defined by

\[
u \in \partial f(x)
\quad\Longleftrightarrow\quad
\forall y \in H,\quad
\langle y-x,u\rangle_{\mathbb R} + f(x) \le f(y),
\]

with the inequality interpreted in \(\mathrm{EReal}\). Thus the theorem says that for a proper convex lower semicontinuous extended-real-valued function on a complete real Hilbert space, the subdifferential is maximal monotone and its \(\varepsilon\)-subdifferential is contained in the \(\varepsilon\)-enlargement of the subdifferential.

## Lean proof
```lean
by
  constructor
  · apply maximal_monotone_of_minty_surjective (subdifferential_isMonotone f hf)
    intro y
    let g : H → EReal := fun z ↦
      f z + (((1 / 2 : ℝ) * ‖z - y‖ ^ 2 : ℝ) : EReal)
    have h_lsc : LowerSemicontinuous f :=
      (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph f).2 hclosed
    have hg_proper : ERealFunction.IsProper g := by
      constructor
      · intro z
        exact EReal.add_ne_bot_iff.mpr ⟨hf.1 z, EReal.coe_ne_bot _⟩
      · rcases hf.2 with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        change g z < ⊤
        exact EReal.add_lt_top (ne_of_lt hz) (EReal.coe_ne_top _)
    have hres_of_variational_inequality : ∀ (p : H),
        (∀ z, f z ≥ f p + (inner ℝ (y - p) (z - p) : EReal)) →
          ∃ u ∈ subdifferential f p, y = p + u := by
      intro p hp
      refine ⟨y - p, ?_, ?_⟩
      · intro z
        have h := hp z
        rw [real_inner_comm] at h
        simpa [add_comm] using h
      · abel
    have hf_convex : ERealFunction.IsConvex f :=
      ERealFunction.isConvex_of_convex_epigraph hf hconvex
    have hf_gamma : f ∈ ERealFunction.gamma H := ⟨hf_convex, h_lsc⟩
    let fI : H → Set.Ioi (⊥ : EReal) := ERealFunction.properIoi f hf
    have hfI : fI ∈ ERealFunction.gammaZero H := by
      exact ERealFunction.properIoi_mem_gammaZero_of_mem_gamma hf hf_gamma
    obtain ⟨p, hp, _⟩ :=
      ERealFunction.hasUniqueProxPoint_of_mem_gammaZero (f := fI) hfI y
    have hvarI :=
      (ERealFunction.isProxPoint_iff_forall_inner_add_le fI hfI.2 y p).1 hp
    have hvar : ∀ z, f z ≥ f p + (inner ℝ (y - p) (z - p) : EReal) := by
      intro z
      have hz := hvarI z
      simpa [fI, ERealFunction.properIoi_apply, add_comm, real_inner_comm] using hz
    exact ⟨p, hres_of_variational_inequality p hvar⟩
  · exact fun x => epsilonSubdifferential_subset_enlargement f hf ε hε x
```

## Proof explanation
The proof starts with `constructor`, because the goal is a conjunction. This splits the proof into two subgoals: first prove that \(\partial f\) is maximal monotone, and then prove the pointwise inclusion of the \(\varepsilon\)-subdifferential in the \(\varepsilon\)-enlargement.

For the first subgoal, the proof invokes `maximal_monotone_of_minty_surjective`. The content of that cited result is a Minty-type maximal monotonicity criterion: if a set-valued operator \(T\) on \(H\) is monotone and satisfies the surjectivity condition

\[
\forall y \in H,\ \exists x \in H,\ \exists u \in T x,\quad y = x+u,
\]

then \(T\) is maximal monotone. The proof applies this with \(T = \partial f\). The monotonicity hypothesis is supplied by `subdifferential_isMonotone f hf`, which states that the subdifferential of a proper extended-real function is a monotone set-valued operator. It remains to prove the Minty surjectivity condition for \(\partial f\).

The proof therefore fixes an arbitrary \(y \in H\) using `intro y`. It then defines an auxiliary function

\[
g(z) = f(z) + \frac12 \|z-y\|^2,
\]

as an extended-real-valued function. It proves `hg_proper` that \(g\) is proper: the value \(g(z)\) is never \(-\infty\), because \(f(z) \neq -\infty\) and the real quadratic term is not \(-\infty\); and the effective domain is nonempty, because \(f\) has a point \(z\) with \(f(z) < +\infty\), and adding a finite real number keeps the value below \(+\infty\). This auxiliary function \(g\) and the fact `hg_proper` are not used later in the proof; the existence of the needed point is obtained instead from the proximal-point theorem below.

Next, the proof derives lower semicontinuity of \(f\). It uses `lowerSemicontinuous_iff_isClosed_epigraph f`, whose mathematical content is that \(f\) is lower semicontinuous if and only if its epigraph is closed. The `.2` direction applies the closedness hypothesis `hclosed` and yields `h_lsc : LowerSemicontinuous f`.

The proof then establishes a local implication: for any \(p \in H\), if the variational inequality

\[
\forall z \in H,\quad f(z) \ge f(p) + \langle y-p,z-p\rangle_{\mathbb R}
\]

holds, then there exists \(u \in \partial f(p)\) with \(y = p+u\). This is the declaration `hres_of_variational_inequality`. To prove it, the proof fixes such a \(p\) and the inequality `hp`, chooses \(u = y-p\), and must show \(u \in \partial f(p)\). By the definition of the subdifferential, this means

\[
\forall z \in H,\quad
\langle z-p,y-p\rangle_{\mathbb R} + f(p) \le f(z).
\]

The hypothesis `hp z` gives a similar inequality with \(\langle y-p,z-p\rangle_{\mathbb R}\). The proof rewrites this inner product using `real_inner_comm`, the symmetry of the real inner product, and then rearranges the addition using `simpa [add_comm]`. This gives exactly the subgradient inequality for \(u = y-p\). The identity \(y = p+u\) is then proved by `abel`, which handles the additive-group identity \(p + (y-p) = y\).

The proof next converts the closed and convex epigraph hypotheses into convexity and lower semicontinuity of \(f\). It applies `isConvex_of_convex_epigraph hf hconvex`, whose content is that if \(f\) is proper and its epigraph is convex, then \(f\) is convex in the Jensen sense:

\[
f(a x + (1-a)y) \le a f(x) + (1-a)f(y)
\]

for all \(x,y \in H\) and all \(a \in \mathbb R\) with \(0 \le a \le 1\). Thus it obtains `hf_convex : ERealFunction.IsConvex f`. Together with `h_lsc`, this gives `hf_gamma : f ∈ ERealFunction.gamma H`, since \(\Gamma(H)\) is the class of convex lower semicontinuous extended-real functions.

The proof then passes from \(f\) to the function

\[
f_I := \operatorname{properIoi} f hf,
\]

which is the same function viewed as taking values in \((-\infty,+\infty]\). The lemma `properIoi_mem_gammaZero_of_mem_gamma` says that if \(f\) is proper and \(f \in \Gamma(H)\), then \(f_I \in \Gamma_0(H)\). Here \(\Gamma_0(H)\) consists of lower semicontinuous functions into \((-\infty,+\infty]\) that are convex on their effective domain. This gives `hfI : fI ∈ ERealFunction.gammaZero H`.

Now the proof uses the proximal-point theorem `hasUniqueProxPoint_of_mem_gammaZero`. Its hypotheses are that \(H\) is complete and \(f_I \in \Gamma_0(H)\). Applied to the fixed point \(y\), it supplies a point \(p\) such that `IsProxPoint fI y p`, and also a uniqueness component which is discarded in the pattern `obtain ⟨p, hp, _⟩`. The exact formal definition of `HasUniqueProxPoint` is not included in the supplied context, but the proof uses precisely the existence part: for the fixed \(y\), there is a proximal point \(p\).

The proof then converts the proximal-point property into a variational inequality. It uses `isProxPoint_iff_forall_inner_add_le fI hfI.2 y p`. The cited result says that for a function \(f : H \to (-\infty,+\infty]\) that is convex on its effective domain, a point \(p\) is a proximal point relative to \(x\) if and only if

\[
\forall z \in H,\quad
\langle z-p,x-p\rangle_{\mathbb R} + f(p) \le f(z).
\]

Here it is applied with \(x=y\), so the proof obtains

\[
\forall z \in H,\quad
\langle z-p,y-p\rangle_{\mathbb R} + f_I(p) \le f_I(z).
\]

The subsequent step rewrites this inequality for \(f_I\) back into an inequality for \(f\). Using `properIoi_apply`, the coercions \(f_I(p)\) and \(f_I(z)\) become \(f(p)\) and \(f(z)\). Using `real_inner_comm` and `add_comm`, the inequality is rearranged into

\[
\forall z \in H,\quad
f(z) \ge f(p) + \langle y-p,z-p\rangle_{\mathbb R}.
\]

This is exactly the hypothesis required by `hres_of_variational_inequality`. Applying that implication to \(p\) gives an element \(u \in \partial f(p)\) with \(y = p+u\). Since \(y\) was arbitrary, this proves the Minty surjectivity condition for \(\partial f\). Together with monotonicity, `maximal_monotone_of_minty_surjective` yields that \(\partial f\) is maximal monotone.

For the second subgoal, the proof uses `epsilonSubdifferential_subset_enlargement f hf ε hε x`. The cited theorem states that for a proper extended-real function on a real inner product space and for \(\varepsilon \ge 0\), the \(\varepsilon\)-subdifferential at \(x\) is contained in the \(\varepsilon\)-enlargement of the ordinary subdifferential at \(x\):

\[
\partial_\varepsilon f(x)
\subseteq
\mathcal E_\varepsilon(\partial f)(x).
\]

The proof provides the properness hypothesis `hf`, the nonnegativity hypothesis `hε`, and the point \(x\), exactly matching the cited theorem. The final `exact fun x => ...` supplies this inclusion for every \(x \in H\), completing the second conjunct. No `linarith` step occurs in the proof; the arithmetic and algebraic rearrangements are handled by `simpa`, `rw`, and `abel`.

