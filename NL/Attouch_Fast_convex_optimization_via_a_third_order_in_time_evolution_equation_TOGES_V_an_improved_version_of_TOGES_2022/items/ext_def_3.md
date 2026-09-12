## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/ext_def_3.lean`

## Lean statement
```lean
theorem mem_subdifferential_dom_of_mem_subdifferential {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → EReal) (hProper : ERealFunction.IsProper f)
    {x v : H} (hv : v ∈ subdifferential f x) : x ∈ ERealFunction.dom f
```

## Statement explanation
The theorem is set in a real inner product space $H$, with $H$ also carrying the structure of a normed additive commutative group. It considers an extended-real-valued function $f:H\to \mathrm{EReal}$, a properness hypothesis $hProper:\mathrm{IsProper} f$, and two points $x,v\in H$. The assumption is that $v$ is a subgradient of $f$ at $x$, written $v\in \partial f(x)$. According to the cited definition of the subdifferential, this means

$$
v\in \partial f(x)
\quad\Longleftrightarrow\quad
\forall y\in H,\;
\bigl(\langle y-x,v\rangle_{\mathbb R}:\mathrm{EReal}\bigr)+f(x)\le f(y).
$$

Thus, for every $y$, the extended-real number obtained from the real inner product $\langle y-x,v\rangle_{\mathbb R}$ plus $f(x)$ is at most $f(y)$. The theorem concludes that $x$ lies in the effective domain of $f$, written $x\in \mathrm{dom} f$. In the proof this membership is handled as the inequality $f(x)<\top$, where $\top$ denotes $+\infty$ in $\mathrm{EReal}$. Mathematically, the statement says that if a proper extended-real-valued function has a subgradient at $x$, then $x$ cannot be a point where $f$ is $+\infty$; such a point must belong to the domain of $f$.

## Lean proof
```lean
by
  rw [subdifferential] at hv
  rcases hProper.2 with ⟨z, hz⟩
  by_contra hx
  have hx_top : f x = ⊤ := le_antisymm le_top (not_lt.mp hx)
  have hz' := hv z
  rw [hx_top] at hz'
  exact (not_le_of_gt hz) (by simpa [EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] using hz')
```

## Proof explanation
The proof proceeds by contradiction and uses the definition of the subdifferential together with one point from the properness hypothesis.

First, the proof unfolds the definition of the subdifferential at $v$. After this rewrite, the hypothesis $hv$ becomes the statement that for every $y\in H$,

$$
\bigl(\langle y-x,v\rangle_{\mathbb R}:\mathrm{EReal}\bigr)+f(x)\le f(y).
$$

Next, the proof extracts a point from the properness hypothesis. The command `rcases hProper.2 with ⟨z, hz⟩` uses the second component of the properness assumption to obtain a point $z\in H$ and a fact $hz$. The later use of `not_le_of_gt hz` shows that $hz$ is the assertion $f(z)<\top$, equivalently $\top>f(z)$. In other words, properness supplies at least one point $z$ at which $f$ is strictly below $+\infty$.

The proof then assumes for contradiction that $x\notin \mathrm{dom} f$. Since membership in $\mathrm{dom} f$ is treated here as $f(x)<\top$, the negation gives $\neg(f(x)<\top)$. In a linear order, this implies $\top\le f(x)$, because the only way not to be strictly below $\top$ is to be at least $\top$. The command `not_lt.mp hx` performs exactly this conversion. Since $\top$ is the top element, we also always have $f(x)\le\top$. Therefore `le_antisymm le_top (not_lt.mp hx)` proves

$$
f(x)=\top.
$$

So under the contradiction assumption, $f$ takes the value $+\infty$ at $x$.

Now the proof specializes the subgradient inequality to the point $z$ supplied by properness. The line `have hz' := hv z` gives

$$
\bigl(\langle z-x,v\rangle_{\mathbb R}:\mathrm{EReal}\bigr)+f(x)\le f(z).
$$

Using the already established equality $f(x)=\top$, the proof rewrites this as

$$
\bigl(\langle z-x,v\rangle_{\mathbb R}:\mathrm{EReal}\bigr)+\top\le f(z).
$$

The simplification step uses the lemma `EReal.add_top_of_ne_bot`. That lemma says that for any extended real number $a$, if $a\ne\bot$, then $a+\top=\top$. Here $a$ is the real inner product $\langle z-x,v\rangle_{\mathbb R}$, coerced into $\mathrm{EReal}$. The fact `EReal.coe_ne_bot` says that a real number embedded into $\mathrm{EReal}$ is not the bottom element $\bot$. Hence

$$
\bigl(\langle z-x,v\rangle_{\mathbb R}:\mathrm{EReal}\bigr)+\top=\top.
$$

After this simplification, the inequality becomes

$$
\top\le f(z).
$$

But $hz$ says $f(z)<\top$, i.e. $\top>f(z)$. The lemma `not_le_of_gt` converts this into the negation

$$
\neg(\top\le f(z)).
$$

Applying this negation to the previously derived inequality $\top\le f(z)$ gives a contradiction. The command `exact` closes the goal by this contradiction. Therefore the assumption $x\notin \mathrm{dom} f$ was false, and the proof concludes

$$
x\in \mathrm{dom} f.
$$

There is no use of `intro` or `linarith` in this proof. The main Lean commands are `rw`, which unfolds the subdifferential and rewrites $f(x)$ as $\top$; `rcases`, which extracts the point $z$ from properness; `by_contra`, which starts the contradiction argument; `simpa`, which simplifies the inequality using `EReal.add_top_of_ne_bot` and `EReal.coe_ne_bot`; and `exact`, which applies the contradiction to finish the proof.

