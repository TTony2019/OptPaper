## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/ext_thm_2.lean`

## Lean statement
```lean
theorem exists_minimizer_of_proper_lsc_coercive {m : Nat}
    (g : EuclideanSpace m -> EReal)
    (hproper : ERealFunction.IsProper g)
    (hlsc : LowerSemicontinuous g)
    (hcoercive : CoerciveEReal g) :
    (∃ r : Real, sInf (Set.range g) = (r : EReal)) ∧
      ∃ x : EuclideanSpace m, IsMinOn g Set.univ x ∧ g x = sInf (Set.range g)
```

## Statement explanation
The declaration concerns a function $g$ on the finite-dimensional Euclidean space $\mathbb R^m$, written in Lean as `EuclideanSpace m`, whose values lie in the extended real line $`\mathrm{EReal} = \mathbb R \cup \{-\infty,+\infty\}`$. The theorem has three hypotheses.

First, `ERealFunction.IsProper g` is unpacked in the proof as two facts: $g$ never takes the value $-\infty$, so $g(x)\neq \bot$ for every $x$, and there exists at least one point $x_0$ with $g(x_0)\lt +\infty$, i.e. $g$ is not identically $+\infty$.

Second, `LowerSemicontinuous g` says that $g$ is lower semicontinuous. The proof uses the standard characterization that this is equivalent to every real lower level set being closed: for every real $\xi$, the set

```math
\{x \mid g(x)\le (\xi:\mathrm{EReal})\}
```

is closed.

Third, `CoerciveEReal g` is a coercivity hypothesis. In the proof it is used only by applying it to the real number $c_0$, obtaining that the real lower level set

```math
C=\{x \mid g(x)\le (c_0:\mathrm{EReal})\}
```

is bounded in the metric sense.

The conclusion is the conjunction of two statements. First, the infimum of the range of $g$,

$$
\mathrm{sInf}(\mathrm{range} g),
$$

is a finite real extended value: there exists $r\in\mathbb R$ such that

$$
\mathrm{sInf}(\mathrm{range} g)=(r:\mathrm{EReal}).
$$

Second, there exists $x\in\mathbb R^m$ such that $x$ is a global minimizer of $g$, meaning

$$
\forall y,\quad g(x)\le g(y),
$$

and moreover

$$
g(x)=\mathrm{sInf}(\mathrm{range} g).
$$

Thus the theorem says that a proper, lower semicontinuous, coercive extended-real-valued function on Euclidean space attains its infimum, and that the infimum is a finite real number.

## Lean proof
```lean
by
  rcases hproper with ⟨hg_ne_bot, x0, hx0_dom⟩
  have hx0_lt_top : g x0 < ⊤ := hx0_dom
  have hx0_ne_top : g x0 ≠ ⊤ := ne_of_lt hx0_lt_top
  have hx0_eff : x0 ∈ ERealFunction.effectiveDom g := by
    rw [ERealFunction.mem_effectiveDom_iff]
    exact ⟨hx0_ne_top, hg_ne_bot x0⟩
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real g x0).mp hx0_eff with ⟨c0, hc0⟩
  let C : Set (EuclideanSpace m) := ERealFunction.lowerLevelSet g c0
  have hx0C : x0 ∈ C := by
    simp [C, ERealFunction.lowerLevelSet, hc0]
  have hC_bounded : Bornology.IsBounded C := hcoercive c0
  have hC_closed : IsClosed C := by
    have hclosed :=
      (ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet g).mp hlsc c0
    simpa [C, ERealFunction.lowerLevelSet] using hclosed
  have hC_compact : IsCompact C := by
    exact (Metric.isCompact_iff_isClosed_bounded).2 ⟨hC_closed, hC_bounded⟩
  have hC_dom : (C ∩ {x | g x < ⊤}).Nonempty := by
    exact ⟨x0, hx0C, hx0_lt_top⟩
  rcases ERealFunction.lowerSemicontinuous_exists_isMinOn_of_isCompact hlsc hC_compact hC_dom with
    ⟨xmin, hxminC, hxmin_minC⟩
  have hxmin_le_c0 : g xmin ≤ (c0 : EReal) := hxminC
  have hxmin_min_univ : IsMinOn g Set.univ xmin := by
    intro y hy
    by_cases hyC : y ∈ C
    · exact hxmin_minC hyC
    · have hnot_le : ¬ g y ≤ (c0 : EReal) := by
        simpa [C, ERealFunction.lowerLevelSet] using hyC
      exact le_trans hxmin_le_c0 (le_of_lt (lt_of_not_ge hnot_le))
  have hxmin_ne_top : g xmin ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hxmin_le_c0
  have hxmin_eff : xmin ∈ ERealFunction.effectiveDom g := by
    rw [ERealFunction.mem_effectiveDom_iff]
    exact ⟨hxmin_ne_top, hg_ne_bot xmin⟩
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real g xmin).mp hxmin_eff with
    ⟨cmin, hcmin⟩
  have hxmin_eq_inf : g xmin = sInf (Set.range g) := by
    simpa using
      (ERealFunction.eq_sInf_image_of_isMinOn (f := g) (C := Set.univ)
        (x := xmin) trivial hxmin_min_univ)
  constructor
  · exact ⟨cmin, by rw [← hxmin_eq_inf, hcmin]⟩
  · exact ⟨xmin, hxmin_min_univ, hxmin_eq_inf⟩
```

## Proof explanation
The proof begins by unpacking properness. The tactic `rcases hproper with ⟨hg_ne_bot, x0, hx0_dom⟩` extracts the fact that $g$ is never $-\infty$, a point $x_0$, and the inequality $g(x_0)\lt +\infty$. From $g(x_0)\lt +\infty$ the proof derives $g(x_0)\neq+\infty$ using `ne_of_lt`. Since properness also gives $g(x_0)\neq-\infty$, the lemma `ERealFunction.mem_effectiveDom_iff` shows

$$
x_0\in \mathrm{effectiveDom} g.
$$

The effective domain consists exactly of the points where the value is finite, neither $+\infty$ nor $-\infty$.

The proof then applies `ERealFunction.mem_effectiveDom_iff_exists_real`, which says that membership in the effective domain is equivalent to the value being a real number coerced into $\mathrm{EReal}$. Hence there exists $c_0\in\mathbb R$ with

$$
g(x_0)=(c_0:\mathrm{EReal}).
$$

Next, the proof defines

```math
C=\mathrm{lowerLevelSet} g c_0=\{x\mid g(x)\le (c_0:\mathrm{EReal})\}.
```

Since $g(x_0)=c_0$, the simplification `simp [C, ERealFunction.lowerLevelSet, hc0]` proves $x_0\in C$.

The coercivity hypothesis is then used in the form `hcoercive c0`, giving that $C$ is bounded:

$$
\mathrm{Bornology.IsBounded} C.
$$

Lower semicontinuity is used through the theorem `ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet`, which states that a function is lower semicontinuous exactly when each real lower level set is closed. Applying it to $c_0$ gives that $C$ is closed. Since $C$ is both closed and bounded in Euclidean space, the metric theorem `Metric.isCompact_iff_isClosed_bounded` yields that $C$ is compact.

The proof also checks that $C$ contains a point where $g$ is not $+\infty$. Namely, $x_0\in C$ and $g(x_0)\lt +\infty$, so

```math
(C\cap\{x\mid g(x)<+\infty\}).\text{Nonempty}
```

holds. This is exactly the extra hypothesis needed for the compact minimization theorem.

The theorem `ERealFunction.lowerSemicontinuous_exists_isMinOn_of_isCompact` is now applied. Its mathematical content is a Weierstrass-type minimum principle for extended-real-valued functions: if $f$ is lower semicontinuous on a compact set $C$ and there is some point of $C$ where $f$ is strictly below $+\infty$, then $f$ attains a minimum on $C$. Applying this to $g$ and $C$ gives a point $x_{\min}\in C$ such that

$$
\forall y\in C,\quad g(x_{\min})\le g(y).
$$

This is the local minimality statement `IsMinOn g C xmin`.

Since $x_{\min}\in C$, the definition of $C$ gives

$$
g(x_{\min})\le (c_0:\mathrm{EReal}).
$$

The proof next upgrades this local minimum to a global minimum. For an arbitrary $y$, it splits into two cases. If $y\in C$, then the local minimality gives $g(x_{\min})\le g(y)$. If $y\notin C$, then $y$ is not in the lower level set at height $c_0$, so

$$
\neg\bigl(g(y)\le (c_0:\mathrm{EReal})\bigr).
$$

Because the extended real line is linearly ordered, this implies

$$
(c_0:\mathrm{EReal})<g(y).
$$

Combining $g(x_{\min})\le c_0$ with $c_0\lt g(y)$ gives $g(x_{\min})\le g(y)$. Thus

$$
\mathrm{IsMinOn} g \mathrm{Set.univ} x_{\min},
$$

meaning $g(x_{\min})\le g(y)$ for every $y\in\mathbb R^m$.

The proof then shows that $g(x_{\min})$ is finite. Since $g(x_{\min})\le c_0$ and $c_0\neq+\infty$, the lemma `ne_top_of_le_ne_top` gives $g(x_{\min})\neq+\infty$. Properness supplies $g(x_{\min})\neq-\infty$. Therefore, by `ERealFunction.mem_effectiveDom_iff`,

$$
x_{\min}\in \mathrm{effectiveDom} g.
$$

Applying `ERealFunction.mem_effectiveDom_iff_exists_real` again, there exists $c_{\min}\in\mathbb R$ such that

$$
g(x_{\min})=(c_{\min}:\mathrm{EReal}).
$$

The key identification with the infimum uses `ERealFunction.eq_sInf_image_of_isMinOn`. That lemma says that if $x\in C$ and $x$ minimizes $f$ over $C$, then

$$
f(x)=\mathrm{sInf}(f''C).
$$

Here it is applied with $f=g$, $C=\mathrm{Set.univ}$, and $x=x_{\min}$. The membership $x_{\min}\in\mathrm{Set.univ}$ is trivial, and the minimization hypothesis is the global minimality just proved. Hence

$$
g(x_{\min})=\mathrm{sInf}(g''\mathrm{Set.univ}).
$$

Since the image of the whole space under $g$ is exactly the range of $g$, the `simpa` step rewrites this as

$$
g(x_{\min})=\mathrm{sInf}(\mathrm{range} g).
$$

Finally, the proof assembles the two conclusions of the conjunction. For the first conclusion, it chooses $r=c_{\min}$. The goal is

$$
\mathrm{sInf}(\mathrm{range} g)=(c_{\min}:\mathrm{EReal}).
$$

Using the equality $g(x_{\min})=\mathrm{sInf}(\mathrm{range} g)$ in reverse and then $g(x_{\min})=(c_{\min}:\mathrm{EReal})$ closes the goal. Thus the infimum of $g$ is a finite real value.

For the second conclusion, the proof chooses $x=x_{\min}$. It has already established both

$$
\mathrm{IsMinOn} g \mathrm{Set.univ} x_{\min}
$$

and

$$
g(x_{\min})=\mathrm{sInf}(\mathrm{range} g).
$$

Therefore $x_{\min}$ is a global minimizer and its value is exactly the infimum of the range of $g$. The proof uses `constructor` to prove the final conjunction and `exact` to provide the witnesses. No `linarith` is used; the only order reasoning is the elementary passage from $\neg(g(y)\le c_0)$ to $c_0\lt g(y)$, followed by transitivity of $\le$.

