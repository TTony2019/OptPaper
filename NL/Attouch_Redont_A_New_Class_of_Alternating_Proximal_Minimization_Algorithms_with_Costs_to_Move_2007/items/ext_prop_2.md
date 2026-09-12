## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/ext_prop_2.lean`

## Lean statement
```lean
theorem convexSubdifferential_weak_strong_closed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (phi : H → EReal)
    (hproper : (∀ x, phi x ≠ ⊥) ∧ ∃ x, phi x ≠ ⊤) (hlsc : LowerSemicontinuous phi)
    (hconvex : ∀ x y : H, ∀ a b : NNReal, a + b = 1 →
      phi ((a : ℝ) • x + (b : ℝ) • y) ≤ (a : EReal) * phi x + (b : EReal) * phi y)
    (x u : ℕ → H) (xbar ubar : H)
    (hx : Tendsto (fun n => toWeakSpace ℝ H (x n)) Filter.atTop
      (nhds (toWeakSpace ℝ H xbar)))
    (hu : Filter.Tendsto u Filter.atTop (nhds ubar))
    (hmem : ∀ n, u n ∈ subdifferential phi (x n)) :
    ubar ∈ subdifferential phi xbar
```

## Statement explanation
The declaration `convexSubdifferential_weak_strong_closed` states a weak-strong closedness property of the graph of the subdifferential of a convex, lower semicontinuous, proper extended-real-valued function.

Let $H$ be a real inner product space which is complete; thus $H$ is a real Hilbert space. Let $\phi : H \to \mathbb R \cup \{-\infty,+\infty\}$ be an extended-real-valued function. The hypotheses on $\phi$ are:

- $\phi$ is proper: for every $x$, $\phi(x)\neq -\infty$, and there exists some $z$ with $\phi(z)\neq +\infty$.
- $\phi$ is lower semicontinuous.
- $\phi$ is convex in the following nonnegative-coefficient sense: for all $x,y\in H$ and all $a,b\in \mathbb R_{\ge 0}$ with $a+b=1$,

  $$
  \phi(a x+b y)\le a\,\phi(x)+b\,\phi(y),
  $$

  where the coefficients are interpreted as real scalars on the left and as extended-real multipliers on the right.

There are also two sequences $x,u:\mathbb N\to H$ and two points $\bar x,\bar u\in H$. The convergence hypotheses are:

- $x_n\rightharpoonup \bar x$ weakly, expressed in Lean by convergence of `toWeakSpace ℝ H (x n)` to `toWeakSpace ℝ H xbar`.
- $u_n\to \bar u$ strongly, in the norm topology.

Finally, for every $n$,

$$
u_n\in \partial\phi(x_n),
$$

where the subdifferential is defined by

$$
\partial\phi(x)=\left\{u\in H:\ \forall y\in H,\ 
\phi(x)+\langle y-x,u\rangle\le \phi(y)\right\}.
$$

The conclusion is

$$
\bar u\in \partial\phi(\bar x).
$$

Unwinding the definition, this means that for every $y\in H$,

$$
\phi(\bar x)+\langle y-\bar x,\bar u\rangle\le \phi(y).
$$

Thus the theorem says that if subgradients $u_n\in \partial\phi(x_n)$ converge strongly to $\bar u$ while the base points $x_n$ converge weakly to $\bar x$, then $\bar u$ is a subgradient of $\phi$ at $\bar x$. In other words, the graph of the convex subdifferential is closed for weak convergence in the primal variable and strong convergence in the dual variable.

## Lean proof
```lean
by
  have hproper' : ERealFunction.IsProper phi := by
    refine ⟨hproper.1, ?_⟩
    rcases hproper.2 with ⟨z, hz⟩
    exact ⟨z, (ERealFunction.mem_dom_iff phi z).2 (lt_top_iff_ne_top.mpr hz)⟩
  let F : H → Set.Ioi (⊥ : EReal) := ERealFunction.properIoi phi hproper'
  have hF_lsc : LowerSemicontinuous (fun z : H => (F z : EReal)) := by
    simpa [F] using hlsc
  have hF_convex : ERealFunction.ConvexOn F (effectiveDomain F) := by
    refine ⟨?_, subset_rfl, ?_⟩
    · rcases hproper.2 with ⟨z, hz⟩
      exact ⟨z, (mem_effectiveDomain_iff).2 (by
        simpa [F] using (lt_top_iff_ne_top.mpr hz))⟩
    · intro p hp q hq a ha0 ha1
      let aNN : NNReal := ⟨a, le_of_lt ha0⟩
      let bNN : NNReal := ⟨1 - a, sub_nonneg.mpr (le_of_lt ha1)⟩
      have hab : aNN + bNN = 1 := by
        apply Subtype.ext
        change a + (1 - a) = 1
        ring
      have h := hconvex p q aNN bNN hab
      simpa [aNN, bNN, F] using h
  have hF_gamma : F ∈ gammaZero H := by
    exact ⟨hF_lsc, hF_convex⟩
  have hmax : SetValuedOperator.IsMaximalMonotone (subdifferential F) :=
    subdifferential_isMaximalMonotone_of_mem_gammaZero hF_gamma
  apply maximal_monotone_graph_weak_strong_closed (subdifferential F) hmax x u xbar ubar
  · simpa [F] using hx
  · exact hu
  · intro n
    simpa [F] using hmem n
```

## Proof explanation
The proof first converts the given properness hypothesis into the bundled predicate `ERealFunction.IsProper phi`. That predicate is

$$
\left(\forall x,\ \phi(x)\neq \bot\right)\ \wedge\ (\mathrm{dom}\phi).\text{Nonempty},
$$

where $\bot$ is $-\infty$. The first conjunct is exactly `hproper.1`. For the second conjunct, the proof uses `hproper.2`, which gives a point $z$ with $\phi(z)\neq \top$, i.e. $\phi(z)\neq +\infty$. The lemma `ERealFunction.mem_dom_iff` says that for an extended-real function $\phi$ and a point $z$,

$$
z\in \mathrm{dom}\phi \iff \phi(z)<\top.
$$

Since $\phi(z)\neq \top$, the order lemma `lt_top_iff_ne_top` gives $\phi(z)<\top$, hence $z\in \mathrm{dom}\phi$. Therefore the domain of $\phi$ is nonempty, so `hproper' : ERealFunction.IsProper phi` is established.

Next the proof defines

$$
F := \mathrm{properIoi}(\phi,\texttt{hproper'}).
$$

In Lean, `properIoi` sends a proper extended-real function $\phi$ to a function

$$
F:H\to \mathrm{Set.Ioi}(\bot:\mathbb EReal),
$$

whose value at $x$ is the subtype element

$$
F(x)=\langle \phi(x),\ \phi(x)>-\infty\rangle.
$$

The proof that $\phi(x)>-\infty$ comes from `hproper'.1`, using `bot_lt_iff_ne_bot`. The coercion of $F(x)$ back to $\mathbb EReal$ is exactly $\phi(x)$. This is the content of the simp lemma `properIoi_apply`:

$$
(F(x):\mathbb EReal)=\phi(x).
$$

Thus $F$ is just $\phi$ with the type adjusted to exclude $-\infty$.

The proof then establishes lower semicontinuity of $F$. The goal is

$$
\mathrm{LowerSemicontinuous}\bigl(x\mapsto (F(x):\mathbb EReal)\bigr).
$$

Since $(F(x):\mathbb EReal)=\phi(x)$, this is definitionally the same as the given lower semicontinuity of $\phi$. The command `simpa [F] using hlsc` performs this rewriting.

Next the proof shows that $F$ is convex on its effective domain:

$$
\mathrm{ConvexOn} F (\mathrm{effectiveDomain} F).
$$

Recall the definition of `ConvexOn`: for $f:H\to \mathrm{Set.Ioi}(\bot:\mathbb EReal)$ and a set $C\subseteq H$, one requires

1. $C$ is nonempty,
2. $C\subseteq \mathrm{effectiveDomain} f$,
3. for all $x,y\in C$ and all $\alpha\in\mathbb R$ with $0<\alpha<1$,

   $$
   f(\alpha x+(1-\alpha)y)\le \alpha f(x)+(1-\alpha)f(y),
   $$

   with the values interpreted in $\mathbb EReal$.

Here $C=\mathrm{effectiveDomain} F$. By the definition of effective domain and `mem_effectiveDomain_iff`,

$$
z\in \mathrm{effectiveDomain} F \iff (F(z):\mathbb EReal)<\top.
$$

Since $(F(z):\mathbb EReal)=\phi(z)$, this is the set of points where $\phi$ is finite.

The proof constructs the three parts of `ConvexOn` using `refine ⟨?_, subset_rfl, ?_⟩`. The middle condition $C\subseteq C$ is proved by `subset_rfl`. For nonemptiness, the proof again uses `hproper.2` to choose $z$ with $\phi(z)\neq \top$. By `mem_effectiveDomain_iff`, it is enough to show $(F(z):\mathbb EReal)<\top$. Since $F(z)=\phi(z)$ and $\phi(z)\neq \top$, this follows from `lt_top_iff_ne_top`. Hence $\mathrm{effectiveDomain} F$ is nonempty.

The Jensen inequality part begins with

$$
\texttt{intro } p\ hp\ q\ hq\ a\ ha0\ ha1,
$$

so $p,q\in \mathrm{effectiveDomain} F$ and $a\in\mathbb R$ satisfies $0<a<1$. The goal is

$$
F(a p+(1-a)q)\le a F(p)+(1-a)F(q)
$$

in $\mathbb EReal$. The given convexity hypothesis `hconvex` is stated with coefficients in `NNReal`, the type of nonnegative reals. The proof therefore defines

$$
aNN :=\langle a,\ a\ge 0\rangle,\qquad
bNN :=\langle 1-a,\ 1-a\ge 0\rangle.
$$

The nonnegativity of $a$ follows from `ha0 : 0 < a`; the nonnegativity of $1-a$ follows from `ha1 : a < 1`, since $a<1$ implies $a\le 1$, hence $1-a\ge 0$. The proof then shows

$$
aNN+bNN=1
$$

by `Subtype.ext`, reducing the equality in `NNReal` to the underlying real equality

$$
a+(1-a)=1,
$$

which is solved by `ring`.

Now `hconvex p q aNN bNN hab` gives

$$
\phi\bigl((aNN:\mathbb R)p+(bNN:\mathbb R)q\bigr)
\le (aNN:\mathbb EReal)\phi(p)+(bNN:\mathbb EReal)\phi(q).
$$

Because the underlying real of $aNN$ is $a$, the underlying real of $bNN$ is $1-a$, and because $(F(z):\mathbb EReal)=\phi(z)$, this inequality is exactly the desired convexity inequality for $F$. The command `simpa [aNN, bNN, F] using h` performs these unfoldings and rewrites.

The proof now forms

$$
F\in \Gamma_0(H).
$$

By definition of `gammaZero`, membership $F\in\Gamma_0(H)$ means precisely

$$
\mathrm{LowerSemicontinuous}\bigl(x\mapsto (F(x):\mathbb EReal)\bigr)
\quad\wedge\quad
\mathrm{ConvexOn} F (\mathrm{effectiveDomain} F).
$$

The two previously proved facts `hF_lsc` and `hF_convex` therefore combine to give `hF_gamma : F ∈ gammaZero H`.

Next the proof applies `subdifferential_isMaximalMonotone_of_mem_gammaZero`. The mathematical content of that theorem is: if a function $f:H\to \mathrm{Set.Ioi}(\bot:\mathbb EReal)$ belongs to $\Gamma_0(H)$, then its subdifferential $\partial f$ is a maximal monotone set-valued operator. Applying it to $F$ and `hF_gamma` gives

$$
\mathrm{IsMaximalMonotone}(\partial F).
$$

The definition of `IsMaximalMonotone` says that the set-valued operator is monotone and is maximal among monotone operators under graph inclusion: if a monotone operator $A'$ has graph containing the graph of $A$, then the graph of $A'$ is contained in the graph of $A$.

The proof then applies the theorem `maximal_monotone_graph_weak_strong_closed` to the operator $T=\partial F$, the maximal monotonicity proof `hmax`, the sequences $x$ and $u$, and the limits $\bar x,\bar u$. That theorem says that for a complete real inner product space $H$, if $T$ is maximal monotone, $x_n$ converges weakly to $x_0$, $v_n$ converges strongly to $v_0$, and $v_n\in T(x_n)$ for all $n$, then $v_0\in T(x_0)$. This is exactly the weak-strong closedness of the graph of a maximal monotone operator.

The remaining goals are the three hypotheses of that theorem:

1. The weak convergence of $x_n$ to $\bar x$. This is supplied by `hx`, and `simpa [F] using hx` discharges it.
2. The strong convergence of $u_n$ to $\bar u$. This is exactly `hu`, so `exact hu` closes the goal.
3. For every $n$, the membership $u_n\in\partial F(x_n)$. The hypothesis `hmem n` gives $u_n\in\partial\phi(x_n)$. Since $F$ and $\phi$ have the same $\mathbb EReal$ values, the defining inequality for $u\in\partial F(x_n)$,

   $$
   (F(x_n):\mathbb EReal)+\langle y-x_n,u\rangle\le (F(y):\mathbb EReal),
   $$

   is identical to the defining inequality for $u\in\partial\phi(x_n)$,

   $$
   \phi(x_n)+\langle y-x_n,u\rangle\le \phi(y).
   $$

   Thus after `intro n`, the command `simpa [F] using hmem n` proves the required membership.

Applying `maximal_monotone_graph_weak_strong_closed` therefore yields

$$
\bar u\in\partial F(\bar x).
$$

Since $F$ has the same $\mathbb EReal$ values as $\phi$, the subdifferential sets $\partial F(\bar x)$ and $\partial\phi(\bar x)$ have exactly the same membership condition. Hence

$$
\bar u\in\partial\phi(\bar x),
$$

which is the conclusion of the theorem. The proof uses `ring` for the coefficient identity $a+(1-a)=1$; it does not use `rw` or `linarith`.

