## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/lem_2.lean`

## Lean statement
```lean
theorem lemma_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} (hyp : H41toH45 H f g β μ) (xbar ybar : H) :
    IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar ↔
    (∀ ξ η : H, L_beta_mu f g β μ xbar ybar ≤ L_beta_mu f g β μ ξ η)
```

## Statement explanation
Let \(H\) be a real inner product space, let \(f,g:H\to\mathbb R\), let \(\beta,\mu\in\mathbb R\), and let \(xbar,ybar\in H\). The theorem is stated under a bundled hypothesis `hyp : H41toH45 H f g β μ`. The supplied source does not define this bundle. In the proof, the only parts of it that are used are \(\beta>0\), \(\mu>0\), and the convexity of \(f\) and \(g\) on all of \(H\), the latter being passed to `subgrad_of_convex_min` as hypotheses of the form \(f\) and \(g\) are convex on \(H\).

The definition `L_beta_mu` used in the statement is

\[
L_{\beta,\mu}(f,g)(\xi,\eta)
=
\mu f(\xi)+\beta g(\eta)+\frac{\beta\mu}{2}\|\xi-\eta\|^2.
\]

The theorem compares the predicate `IsINE` applied to \(f,g\), the three copies of the same cost function

\[
c(\xi,\eta)=\frac{\|\xi-\eta\|^2}{2},
\]

the indicated zero parameters, the parameters \(\beta,\mu\), and the points \(xbar,ybar\), with the condition that \((xbar,ybar)\) globally minimizes \(L_{\beta,\mu}\). In the proof, the left side is unfolded as the conjunction of the following two minimization properties:

\[
\forall \xi\in H,\qquad
f(xbar)+\frac{\beta}{2}\|xbar-ybar\|^2
\le
f(\xi)+\frac{\beta}{2}\|\xi-ybar\|^2,
\]

meaning that \(xbar\) minimizes

\[
\xi\mapsto f(\xi)+\frac{\beta}{2}\|\xi-ybar\|^2,
\]

and

\[
\forall \eta\in H,\qquad
g(ybar)+\frac{\mu}{2}\|xbar-ybar\|^2
\le
g(\eta)+\frac{\mu}{2}\|xbar-\eta\|^2,
\]

meaning that \(ybar\) minimizes

\[
\eta\mapsto g(\eta)+\frac{\mu}{2}\|xbar-\eta\|^2.
\]

Thus the theorem says: under the positivity and convexity hypotheses used in the proof, \((xbar,ybar)\) is a pair of exact proximal minimizers in this alternating sense if and only if it is a global minimizer of the coupled function

\[
(\xi,\eta)\mapsto
\mu f(\xi)+\beta g(\eta)+\frac{\beta\mu}{2}\|\xi-\eta\|^2.
\]

## Lean proof
```lean
by
  have hβpos : β > 0 := hyp.beta_pos
  have hμpos : μ > 0 := hyp.mu_pos
  constructor
  · -- Direction (→) : INE → minimizer of L
    rintro ⟨hx_opt, hy_opt⟩ ξ η
    -- Simplify hx_opt and hy_opt
    have hx_simp : ∀ ξ' : H, f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤
        f ξ' + β * (‖ξ' - ybar‖ ^ 2 / 2) := by
      intro ξ'
      simpa using hx_opt ξ'
    have hy_simp : ∀ η' : H, g ybar + μ * (‖xbar - ybar‖ ^ 2 / 2) ≤
        g η' + μ * (‖xbar - η'‖ ^ 2 / 2) := by
      intro η'
      simpa using hy_opt η'
    -- Swap norm order for subgrad_of_convex_min
    have hy_simp' : ∀ η' : H, g ybar + μ * (‖ybar - xbar‖ ^ 2 / 2) ≤
        g η' + μ * (‖η' - xbar‖ ^ 2 / 2) := by
      intro η'
      simpa [norm_sub_rev] using hy_simp η'
    -- Subgradient inequalities
    have hf_sub : f ξ ≥ f xbar + inner ℝ (β • (ybar - xbar)) (ξ - xbar) :=
      subgrad_of_convex_min hyp.h42_f_conv hβpos hx_simp ξ
    have hg_sub : g η ≥ g ybar + inner ℝ (μ • (xbar - ybar)) (η - ybar) :=
      subgrad_of_convex_min hyp.h42_g_conv hμpos hy_simp' η
    set p := ξ - xbar with hp_def
    set q := η - ybar with hq_def
    set d := xbar - ybar with hd_def
    -- Combine the subgradient inequalities
    have hsum : μ * f ξ + β * g η ≥ μ * f xbar + β * g ybar +
        (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) := by
      have h1 : μ * f ξ ≥ μ * f xbar + μ * inner ℝ (β • (ybar - xbar)) (ξ - xbar) := by nlinarith
      have h2 : β * g η ≥ β * g ybar + β * inner ℝ (μ • (xbar - ybar)) (η - ybar) := by nlinarith
      have h_inner1 : μ * inner ℝ (β • (ybar - xbar)) (ξ - xbar) =
          (β * μ) * inner ℝ (ybar - xbar) p := by
        rw [inner_smul_left]
        simp [hp_def]
        ring
      have h_inner2 : β * inner ℝ (μ • (xbar - ybar)) (η - ybar) =
          (β * μ) * inner ℝ d q := by
        rw [inner_smul_left]
        simp [hd_def, hq_def]
        ring
      nlinarith
    -- Expand ‖ξ-η‖²
    have h_decomp : ‖ξ - η‖ ^ 2 = ‖d‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 +
        2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
      calc
        ‖ξ - η‖ ^ 2 = ‖(p + d) - q‖ ^ 2 := by
          dsimp [p, d, q]
          abel
        _ = ‖p + d‖ ^ 2 - 2 * inner ℝ (p + d) q + ‖q‖ ^ 2 :=
          norm_sub_sq_real (p + d) q
        _ = (‖p‖ ^ 2 + 2 * inner ℝ p d + ‖d‖ ^ 2) - 2 * (inner ℝ p q + inner ℝ d q) + ‖q‖ ^ 2 := by
          rw [norm_add_sq_real p d, inner_add_left]
        _ = ‖d‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
          rw [real_inner_comm p d]
          ring
    -- L inequality with norm differences
    have hLpre : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
        (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
        (β * μ / 2) * (‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
      dsimp [L_beta_mu]
      nlinarith
    -- Norm difference = the expansion from h_decomp
    have h_norm_diff : ‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2 =
        ‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
      rw [h_decomp]
      nlinarith
    -- Substitute into hLpre
    have hLmid : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
        (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
        (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) := by
      calc
        L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
            (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
            (β * μ / 2) * (‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := hLpre
        _ = L_beta_mu f g β μ xbar ybar +
            (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
            (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) := by
          rw [h_norm_diff]
    -- Simplify: inner(ybar-xbar, p) = -inner(d, p)
    have h_inner_yp : inner ℝ (ybar - xbar) p = -inner ℝ d p := by
      calc
        inner ℝ (ybar - xbar) p = inner ℝ (-(xbar - ybar)) p := by simp
        _ = -inner ℝ (xbar - ybar) p := by rw [inner_neg_left]
        _ = -inner ℝ d p := by simp [hd_def]
    rw [h_inner_yp] at hLmid
    -- The cross + norm terms simplify to (βμ/2)*‖p-q‖²
    have h_key : (β * μ) * (-inner ℝ d p + inner ℝ d q) +
        (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) =
        (β * μ / 2) * ‖p - q‖ ^ 2 := by
      calc
        (β * μ) * (-inner ℝ d p + inner ℝ d q) +
            (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q)
            = (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 - 2 * inner ℝ p q) := by
          ring
        _ = (β * μ / 2) * ‖p - q‖ ^ 2 := by
          rw [norm_sub_sq_real p q]
          ring
    -- Final simplification
    have hLfinal : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
        (β * μ / 2) * ‖p - q‖ ^ 2 := by
      linarith
    have h_nonneg : (β * μ / 2) * ‖p - q‖ ^ 2 ≥ 0 := by
      have h_coeff : 0 ≤ β * μ / 2 := by nlinarith
      nlinarith [sq_nonneg ‖p - q‖]
    nlinarith
  · -- Direction (←) : minimizer of L → INE
    intro hmin
    constructor
    · intro ξ
      have h := hmin ξ ybar
      dsimp [L_beta_mu] at h
      have h_simp : f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤ f ξ + β * (‖ξ - ybar‖ ^ 2 / 2) := by
        nlinarith
      simpa
    · intro η
      have h := hmin xbar η
      dsimp [L_beta_mu] at h
      have h_simp : g ybar + μ * (‖xbar - ybar‖ ^ 2 / 2) ≤ g η + μ * (‖xbar - η‖ ^ 2 / 2) := by
        nlinarith
      simpa
```

## Proof explanation
The proof begins by extracting the positivity assumptions:

\[
\beta>0,\qquad \mu>0.
\]

These are used throughout to justify multiplying or dividing inequalities by positive scalars. The proof then splits the equivalence into two implications using `constructor`.

For the forward implication, assume the left-hand side, namely the `IsINE` predicate. The pattern `rintro ⟨hx_opt, hy_opt⟩ ξ η` destructs this predicate into its two minimizer inequalities and introduces arbitrary \(\xi,\eta\in H\). The first inequality is rewritten by `simpa` as

\[
\forall \xi',\qquad
f(xbar)+\beta\frac{\|xbar-ybar\|^2}{2}
\le
f(\xi')+\beta\frac{\|\xi'-ybar\|^2}{2}.
\]

The second one is first rewritten as

\[
\forall \eta',\qquad
g(ybar)+\mu\frac{\|xbar-ybar\|^2}{2}
\le
g(\eta')+\mu\frac{\|xbar-\eta'\|^2}{2}.
\]

Then `norm_sub_rev`, which says \(\|a-b\|=\|b-a\|\), is used to replace the norms by their reversed versions, producing

\[
\forall \eta',\qquad
g(ybar)+\mu\frac{\|ybar-xbar\|^2}{2}
\le
g(\eta')+\mu\frac{\|\eta'-xbar\|^2}{2}.
\]

This is the form needed to apply `subgrad_of_convex_min` with \(g\) in place of \(f\), \(ybar\) in place of \(xbar\), \(xbar\) in place of \(ybar\), and \(\mu\) in place of \(\beta\).

The lemma `subgrad_of_convex_min` says the following. If \(f\) is convex on all of \(H\), if \(\beta>0\), and if \(xbar\) minimizes

\[
\xi\mapsto f(\xi)+\frac{\beta}{2}\|\xi-ybar\|^2,
\]

so that

\[
f(xbar)+\beta\frac{\|xbar-ybar\|^2}{2}
\le
f(\xi)+\beta\frac{\|\xi-ybar\|^2}{2}
\]

for every \(\xi\), then for every \(z\in H\),

\[
f(z)
\ge
f(xbar)+\left\langle \beta(ybar-xbar),\,z-xbar\right\rangle.
\]

Applying this to \(f\) with \(z=\xi\) gives

\[
f(\xi)
\ge
f(xbar)+\left\langle \beta(ybar-xbar),\,\xi-xbar\right\rangle.
\]

Applying it to \(g\) with \(z=\eta\), \(\mu\) in place of \(\beta\), and the swapped roles of \(xbar\) and \(ybar\), gives

\[
g(\eta)
\ge
g(ybar)+\left\langle \mu(xbar-ybar),\,\eta-ybar\right\rangle.
\]

These are the two subgradient inequalities.

Next the proof introduces abbreviations

\[
p=\xi-xbar,\qquad q=\eta-ybar,\qquad d=xbar-ybar.
\]

Multiplying the first subgradient inequality by \(\mu>0\) and the second by \(\beta>0\), and using `inner_smul_left`, which says

\[
\langle r u,v\rangle=r\langle u,v\rangle
\]

for real scalars \(r\), gives

\[
\mu f(\xi)
\ge
\mu f(xbar)+\beta\mu\langle ybar-xbar,p\rangle
\]

and

\[
\beta g(\eta)
\ge
\beta g(ybar)+\beta\mu\langle d,q\rangle.
\]

Adding these yields

\[
\mu f(\xi)+\beta g(\eta)
\ge
\mu f(xbar)+\beta g(ybar)
+\beta\mu\bigl(\langle ybar-xbar,p\rangle+\langle d,q\rangle\bigr).
\]

The tactic `nlinarith` performs this nonlinear arithmetic after the scalar identities have been established.

The next step is to expand the squared norm. Since

\[
\xi-\eta=(p+d)-q,
\]

the proof uses `norm_sub_sq_real`, which says

\[
\|a-b\|^2=\|a\|^2-2\langle a,b\rangle+\|b\|^2,
\]

with \(a=p+d\) and \(b=q\), then `norm_add_sq_real`, which says

\[
\|a+b\|^2=\|a\|^2+2\langle a,b\rangle+\|b\|^2,
\]

and `inner_add_left`, which says

\[
\langle a+b,c\rangle=\langle a,c\rangle+\langle b,c\rangle.
\]

Using also `real_inner_comm`, which says \(\langle a,b\rangle=\langle b,a\rangle\) in a real inner product space, the proof obtains

\[
\|\xi-\eta\|^2
=
\|d\|^2+\|p\|^2+\|q\|^2
+2\langle d,p\rangle
-2\langle p,q\rangle
-2\langle d,q\rangle.
\]

Combining this expansion with the earlier inequality and the definition of \(L_{\beta,\mu}\) gives

\[
L_{\beta,\mu}(\xi,\eta)
\ge
L_{\beta,\mu}(xbar,ybar)
+\beta\mu\bigl(\langle ybar-xbar,p\rangle+\langle d,q\rangle\bigr)
+\frac{\beta\mu}{2}
\bigl(\|\xi-\eta\|^2-\|xbar-ybar\|^2\bigr).
\]

Since \(xbar-ybar=d\), subtracting \(\|d\|^2\) from the expansion of \(\|\xi-\eta\|^2\) gives

\[
\|\xi-\eta\|^2-\|xbar-ybar\|^2
=
\|p\|^2+\|q\|^2
+2\langle d,p\rangle
-2\langle p,q\rangle
-2\langle d,q\rangle.
\]

Substituting this into the previous inequality yields

\[
L_{\beta,\mu}(\xi,\eta)
\ge
L_{\beta,\mu}(xbar,ybar)
+\beta\mu\bigl(\langle ybar-xbar,p\rangle+\langle d,q\rangle\bigr)
+\frac{\beta\mu}{2}
\bigl(
\|p\|^2+\|q\|^2
+2\langle d,p\rangle
-2\langle p,q\rangle
-2\langle d,q\rangle
\bigr).
\]

Now \(ybar-xbar=-(xbar-ybar)=-d\), so `inner_neg_left`, which says

\[
\langle -u,v\rangle=-\langle u,v\rangle,
\]

gives

\[
\langle ybar-xbar,p\rangle=-\langle d,p\rangle.
\]

After rewriting with this identity, the cross terms cancel algebraically. The relevant identity is

\[
\beta\mu\bigl(-\langle d,p\rangle+\langle d,q\rangle\bigr)
+
\frac{\beta\mu}{2}
\bigl(
\|p\|^2+\|q\|^2
+2\langle d,p\rangle
-2\langle p,q\rangle
-2\langle d,q\rangle
\bigr)
=
\frac{\beta\mu}{2}\|p-q\|^2.
\]

The proof first uses `ring` to reduce the left side to

\[
\frac{\beta\mu}{2}\bigl(\|p\|^2+\|q\|^2-2\langle p,q\rangle\bigr),
\]

and then uses `norm_sub_sq_real` again, now for \(p-q\), to identify this with

\[
\frac{\beta\mu}{2}\|p-q\|^2.
\]

Therefore

\[
L_{\beta,\mu}(\xi,\eta)
\ge
L_{\beta,\mu}(xbar,ybar)
+\frac{\beta\mu}{2}\|p-q\|^2.
\]

Since \(\beta>0\) and \(\mu>0\), the coefficient \(\frac{\beta\mu}{2}\) is nonnegative. Also `sq_nonneg` gives \(\|p-q\|^2\ge 0\). Hence the added term is nonnegative, and `nlinarith` concludes

\[
L_{\beta,\mu}(xbar,ybar)\le L_{\beta,\mu}(\xi,\eta).
\]

Because \(\xi,\eta\) were arbitrary, this proves the forward implication.

For the reverse implication, assume

\[
\forall \xi,\eta,\qquad
L_{\beta,\mu}(xbar,ybar)\le L_{\beta,\mu}(\xi,\eta).
\]

The proof uses `constructor` twice to rebuild the two components of `IsINE`.

For the first component, take an arbitrary \(\xi\). Applying the assumed minimizing property to \((\xi,ybar)\) gives

\[
L_{\beta,\mu}(xbar,ybar)\le L_{\beta,\mu}(\xi,ybar).
\]

After unfolding `L_beta_mu`, this is

\[
\mu f(xbar)+\beta g(ybar)+\frac{\beta\mu}{2}\|xbar-ybar\|^2
\le
\mu f(\xi)+\beta g(ybar)+\frac{\beta\mu}{2}\|\xi-ybar\|^2.
\]

The common term \(\beta g(ybar)\) cancels. Since \(\mu>0\), dividing by \(\mu\) gives

\[
f(xbar)+\frac{\beta}{2}\|xbar-ybar\|^2
\le
f(\xi)+\frac{\beta}{2}\|\xi-ybar\|^2.
\]

This is exactly the first minimizer property. The arithmetic is performed by `nlinarith`, and `simpa` matches the target form.

For the second component, take an arbitrary \(\eta\). Applying the assumed minimizing property to \((xbar,\eta)\) gives

\[
L_{\beta,\mu}(xbar,ybar)\le L_{\beta,\mu}(xbar,\eta).
\]

After unfolding `L_beta_mu`, this is

\[
\mu f(xbar)+\beta g(ybar)+\frac{\beta\mu}{2}\|xbar-ybar\|^2
\le
\mu f(xbar)+\beta g(\eta)+\frac{\beta\mu}{2}\|xbar-\eta\|^2.
\]

The common term \(\mu f(xbar)\) cancels. Since \(\beta>0\), dividing by \(\beta\) gives

\[
g(ybar)+\frac{\mu}{2}\|xbar-ybar\|^2
\le
g(\eta)+\frac{\mu}{2}\|xbar-\eta\|^2.
\]

This is the second minimizer property. Again `nlinarith` handles the rearrangement and `simpa` closes the goal.

Thus both components of `IsINE` hold, completing the reverse implication and therefore the equivalence.

