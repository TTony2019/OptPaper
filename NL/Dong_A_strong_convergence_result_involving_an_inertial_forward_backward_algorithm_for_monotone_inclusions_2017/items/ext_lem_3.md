## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/ext_lem_3.lean`

## Lean statement
```lean
theorem browder_demiclosedness_lemma
    {C : Set H} (_hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {T : H → H} (_hT_maps : MapsTo T C C)
    (hT : ∀ a ∈ C, ∀ b ∈ C, ‖T a - T b‖ ≤ ‖a - b‖)
    (_hfixed : (fixedPointSetOn C T).Nonempty) {xSeq : ℕ → H} (hxSeq : ∀ n, xSeq n ∈ C)
    {x y : H}
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (xSeq n)) atTop (nhds (toWeakSpace ℝ H x)))
    (hy : Tendsto (fun n ↦ xSeq n - T (xSeq n)) atTop (nhds y)) :
    x - T x = y ∧ (y = 0 → x ∈ fixedPointSetOn C T)
```

## Statement explanation
The declaration `browder_demiclosedness_lemma` is a theorem about a subset $C$ of an ambient space $H$, a map $T : H \to H$, and a sequence $x_n$ in $H$. The notation $\|T a - T b\|$ indicates that $H$ carries a norm, and the map to the weak space over $\mathbb R$ is used to express weak convergence. The fixed-point set $\mathrm{fixedPointSetOn} C T$ is the set of points of $C$ that are fixed by $T$.

The hypotheses are as follows. First, $C$ is assumed nonempty, closed, and convex over $\mathbb R$. The map $T$ is assumed to send $C$ into itself: $T(C) \subseteq C$. It is also assumed to be nonexpansive on $C$, meaning that for all $a,b \in C$,

$$
\|T a - T b\| \le \|a-b\|.
$$

There is an additional assumption that $T$ has at least one fixed point in $C$, i.e. $\mathrm{fixedPointSetOn} C T$ is nonempty. The sequence $x_n$ satisfies $x_n \in C$ for every $n$. It is assumed to converge weakly to $x$, encoded by convergence of the image of $x_n$ under the weak-space map to the image of $x$. Finally, the residuals $x_n - T x_n$ are assumed to converge in the ordinary topology to $y$.

The conclusion is the conjunction

$$
x - T x = y
$$

and

$$
y = 0 \implies x \in \mathrm{fixedPointSetOn} C T.
$$

Since $\mathrm{fixedPointSetOn} C T$ consists exactly of the points $z \in C$ with $T z = z$, the second conclusion says that if the residual limit is zero, then the weak limit $x$ is a fixed point of $T$ lying in $C$. The hypotheses that $C$ is nonempty, that $T$ maps $C$ into itself, and that $T$ has a fixed point in $C$ are present in the statement, but the proof does not use them.

## Lean proof
```lean
by
  have hweak_closed : IsSeqClosed ((toWeakSpace ℝ H) '' C) :=
    ((isClosed_iff_weak_image_isClosed_of_convex hC_convex).mp hC_closed).isSeqClosed
  have hT_lipschitz : LipschitzOnWith 1 T C :=
    isNonexpansiveOn_restrict_iff_lipschitzOnWith_one.mp hT
  have hresidual : x - T x = y :=
    browder_demiclosedness_principle hweak_closed hT_lipschitz hxSeq hx hy
  constructor
  · exact hresidual
  · intro hy_zero
    rw [mem_fixedPointSetOn_iff]
    refine ⟨mem_of_tendsto_weakly_of_isClosed_convex hC_closed hC_convex hxSeq hx, ?_⟩
    exact (sub_eq_zero.mp (hresidual.trans hy_zero)).symm
```

## Proof explanation
The proof begins by establishing a sequential-closedness property for the weak image of $C$. Since $C$ is convex over $\mathbb R$, the cited theorem `isClosed_iff_weak_image_isClosed_of_convex` states that $C$ is closed if and only if its image under the weak-space map is closed. Applying the forward direction to the hypothesis that $C$ is closed gives that this weak image is closed. Then `.isSeqClosed` extracts from closedness the fact that the weak image is sequentially closed: any sequence in that image that converges in the weak topology has its limit again in the image. This produces `hweak_closed`, which is exactly the sequential-closedness hypothesis needed later by Browder’s demiclosedness principle.

Next, the proof converts the pointwise nonexpansiveness hypothesis into a bundled Lipschitz condition. The hypothesis `hT` says that for all $a,b \in C$,

$$
\|T a - T b\| \le \|a-b\|.
$$

The cited result `isNonexpansiveOn_restrict_iff_lipschitzOnWith_one` supplies the direction from this pointwise inequality to the statement that $T$ is Lipschitz on $C$ with constant $1$. Thus `hT_lipschitz` states that $T$ satisfies `LipschitzOnWith 1 T C`, i.e. the same inequality with Lipschitz constant $1$ on the set $C$. This is the Lipschitz hypothesis required by Browder’s principle.

The main step is the application of `browder_demiclosedness_principle`. That cited theorem takes a set $D$ whose weak image is sequentially closed, a map $T$ that is $1$-Lipschitz on $D$, a sequence $x_n \in D$, weak convergence of $x_n$ to some $x$, and strong convergence of $x_n - T x_n$ to some $u$. Its conclusion is

$$
x - T x = u.
$$

In the present proof one specializes $D$ to $C$ and $u$ to $y$. The hypotheses supplied are precisely the weak sequential closedness of the image of $C$, the Lipschitz-on- $C$ condition for $T$, the fact that each $x_n$ lies in $C$, the weak convergence of $x_n$ to $x$, and the strong convergence of the residuals to $y$. The resulting equality `hresidual` is

$$
x - T x = y.
$$

This is the demiclosedness content: the strong limit of the residuals determines the residual at the weak limit.

The proof then proves the conjunction. The tactic `constructor` splits the goal into the two conjuncts. The first conjunct is $x - T x = y$, and it is closed immediately by `exact hresidual`.

For the second conjunct, the tactic `intro hy_zero` assumes $y = 0$. The goal is then to show $x \in \mathrm{fixedPointSetOn} C T$. The rewrite `rw [mem_fixedPointSetOn_iff]` replaces this membership with the equivalent condition given by the cited lemma `mem_fixedPointSetOn_iff`:

$$
x \in \mathrm{fixedPointSetOn} C T
\iff
x \in C \land T x = x.
$$

So it remains to prove $x \in C$ and $T x = x$.

The `refine` command supplies the first part, $x \in C$, using the cited theorem `mem_of_tendsto_weakly_of_isClosed_convex`. That theorem says that if $C$ is closed and convex, each $x_n$ lies in $C$, and $x_n$ converges weakly to $x$, then $x \in C$. Its hypotheses are exactly `hC_closed`, `hC_convex`, `hxSeq`, and `hx`, so it yields $x \in C$. The remaining goal is $T x = x$.

Finally, from `hresidual`, which says $x - T x = y$, and `hy_zero`, which says $y = 0$, transitivity of equality gives

$$
x - T x = 0.
$$

The lemma used by `sub_eq_zero.mp` states that $a - b = 0$ implies $a = b$. Applying it here gives $x = T x$, and taking symmetry with `.symm` changes this to $T x = x$. This proves the second component of the fixed-point membership. Combining $x \in C$ and $T x = x$ gives $x \in \mathrm{fixedPointSetOn} C T$, so the implication $y = 0 \implies x \in \mathrm{fixedPointSetOn} C T$ is proved, and hence the whole conjunction is proved.

