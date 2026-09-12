## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/def_1.lean`

## Lean statement
```lean
theorem epsilonEnlargement_properties (T : SetValuedOperator H H)
    (hT : T.IsMaximalMonotone) :
    epsilonEnlargement T 0 (by positivity) = T ∧
      (∀ x ε₁ ε₂ (hε₁ : 0 ≤ ε₁) (hε₁₂ : ε₁ ≤ ε₂),
        epsilonEnlargement T ε₁ hε₁ x ⊆
          epsilonEnlargement T ε₂ (le_trans hε₁ hε₁₂) x) ∧
      ∀ ε (hε : 0 ≤ ε) x, T x ⊆ epsilonEnlargement T ε hε x
```

## Statement explanation
The declaration `epsilonEnlargement_properties` is a theorem about a set-valued operator $T$ on an ambient type $H$ equipped with a real inner product $\langle\cdot,\cdot\rangle$, written in Lean as `inner ℝ`. The operator is written $`T:\mathrm{SetValuedOperator}\,H\,H`$, meaning that for each$x\in H$, the value$T x$is a subset of$H$. The hypothesis$h_T:T.IsMaximalMonotone$says that$T$ is maximal monotone.

For $\varepsilon\ge 0$, the definition `epsilonEnlargement T ε hε` gives the set-valued operator $E_\varepsilon(T)$ defined by

```math
E_\varepsilon(T)(x)
=\{v\in H:\forall z,w,\ w\in Tz \implies
\langle w-v,z-x\rangle\ge -\varepsilon\}.
```

The argument $h_\varepsilon$ is a proof that $0\le \varepsilon$; it is part of the definition, although the set itself depends only on the numerical value of $\varepsilon$.

The theorem concludes a conjunction of three statements:

1. The zero enlargement is exactly $T$:

$$
E_0(T)=T.
$$

   Here the proof of $0\le 0$ required by `epsilonEnlargement T 0` is supplied by the tactic `positivity`.

2. The enlargements are monotone in $\varepsilon$: for every $x$, every $\varepsilon_1,\varepsilon_2$, every proof $h_{\varepsilon_1}:0\le\varepsilon_1$, and every proof $h_{\varepsilon_1\varepsilon_2}:\varepsilon_1\le\varepsilon_2$,

$$
E_{\varepsilon_1}(T)(x)\subseteq E_{\varepsilon_2}(T)(x).
$$

   The proof of $0\le\varepsilon_2$ used in the right-hand enlargement is obtained by transitivity from $0\le\varepsilon_1$ and $\varepsilon_1\le\varepsilon_2$.

3. Every value of $T$ lies in every nonnegative enlargement:

$$
\forall \varepsilon\ge 0,\ \forall x,\quad T x\subseteq E_\varepsilon(T)(x).
$$

Thus the theorem says that for a maximal monotone operator $T$, the zero enlargement recovers $T$, increasing the enlargement parameter only enlarges the sets, and $T x$ is always contained in any nonnegative enlargement of $T x$.

## Lean proof
```lean
by
  refine ⟨?_, ?_, ?_⟩
  · funext x
    ext v
    constructor
    · intro hv
      apply mem_of_monotonically_related_to_graph hT
      intro z w hw
      have hzero : 0 ≤ inner ℝ (w - v) (z - x) := by
        simpa [epsilonEnlargement] using hv z w hw
      calc
        0 ≤ inner ℝ (w - v) (z - x) := hzero
        _ = inner ℝ (v - w) (x - z) := by
          rw [show w - v = -(v - w) by abel, show z - x = -(x - z) by abel,
            inner_neg_neg]
    · intro hv
      change ∀ z w, w ∈ T z → -(0 : ℝ) ≤ inner ℝ (w - v) (z - x)
      intro z w hw
      simpa using hT.1 w hw v hv
  · intro x ε₁ ε₂ hε₁ hε₁₂ v hv
    change ∀ z w, w ∈ T z → -ε₂ ≤ inner ℝ (w - v) (z - x)
    intro z w hw
    have hsource : -ε₁ ≤ inner ℝ (w - v) (z - x) := by
      simpa [epsilonEnlargement] using hv z w hw
    linarith
  · intro ε hε x v hv
    change ∀ z w, w ∈ T z → -ε ≤ inner ℝ (w - v) (z - x)
    intro z w hw
    exact le_trans (neg_nonpos.mpr hε) (hT.1 w hw v hv)
```

## Proof explanation
The proof begins with `by`, and then `refine ⟨?_, ?_, ?_⟩`. Since the goal is a threefold conjunction, this splits the proof into exactly the three parts matching the three statements above.

For the first part, the goal is $E_0(T)=T$. The command `funext x` proves equality of the two set-valued operators by proving equality at each input $x$. Then `ext v` proves equality of the two sets $E_0(T)(x)$ and $T x$ by proving that an arbitrary $v$ belongs to one exactly when it belongs to the other. The command `constructor` splits this set equality into the two implications.

In the forward direction, `intro hv` assumes $v\in E_0(T)(x)$. The goal is $v\in T x$. The proof applies `mem_of_monotonically_related_to_graph hT`. That cited theorem says that if $T$ is maximal monotone, and a pair $(x,u)$ is monotonically related to the graph of $T$, meaning

$$
\forall y,v,\quad v\in T y \implies 0\le \langle u-v,x-y\rangle,
$$

then $u\in T x$. Here the theorem is invoked with the current $x$ and with $u$ equal to the current element $v$. Therefore it remains to prove

$$
\forall z,w,\quad w\in T z \implies 0\le \langle v-w,x-z\rangle.
$$

The proof introduces arbitrary $z,w$ with $w\in T z$ by `intro z w hw`. From `hv`, which says $v\in E_0(T)(x)$, unfolding `epsilonEnlargement` gives

$$
0\le \langle w-v,z-x\rangle,
$$

because the condition is $\langle w-v,z-x\rangle\ge -0$ and $-0=0$. The `have hzero` step records this. Then the `calc` block proves

$$
0\le \langle w-v,z-x\rangle
=\langle v-w,x-z\rangle.
$$

The equality is justified by rewriting

$$
w-v=-(v-w),\qquad z-x=-(x-z)
$$

using `abel`, and then applying `inner_neg_neg`, the fact that the inner product of two negated vectors equals the inner product of the original vectors:

$$
\langle -a,-b\rangle=\langle a,b\rangle.
$$

This gives the monotone-relatedness condition required by `mem_of_monotonically_related_to_graph`, so maximality yields $v\in T x$.

In the reverse direction, `intro hv` assumes $v\in T x$. The goal is $v\in E_0(T)(x)$. The `change` command unfolds the membership condition to

$$
\forall z,w,\quad w\in T z \implies -0\le \langle w-v,z-x\rangle.
$$

After `intro z w hw`, the proof uses `simpa using hT.1 w hw v hv`. The expression `hT.1` is the monotonicity component of the maximal-monotonicity hypothesis: from $w\in T z$ and $v\in T x$, it gives

$$
0\le \langle w-v,z-x\rangle.
$$

Since $-0=0$, `simpa` closes the required inequality. This proves the reverse inclusion.

For the second part, the proof introduces $x,\varepsilon_1,\varepsilon_2,h_{\varepsilon_1},h_{\varepsilon_1\varepsilon_2},v,hv$, where $hv$ says

$$
v\in E_{\varepsilon_1}(T)(x).
$$

The goal is $v\in E_{\varepsilon_2}(T)(x)$. The `change` command rewrites this goal as

$$
\forall z,w,\quad w\in T z \implies -\varepsilon_2\le \langle w-v,z-x\rangle.
$$

After `intro z w hw`, the proof extracts from $hv$, using `simpa [epsilonEnlargement]`, the inequality

$$
-\varepsilon_1\le \langle w-v,z-x\rangle.
$$

Since $h_{\varepsilon_1\varepsilon_2}$ says $\varepsilon_1\le\varepsilon_2$, we have

$$
-\varepsilon_2\le -\varepsilon_1.
$$

Combining this with the previous inequality gives

$$
-\varepsilon_2\le \langle w-v,z-x\rangle.
$$

The tactic `linarith` performs exactly this linear inequality reasoning. Hence $v\in E_{\varepsilon_2}(T)(x)$, proving the inclusion.

For the third part, the proof introduces $\varepsilon,h_\varepsilon,x,v,hv$, where $hv$ says $v\in T x$. The goal is $v\in E_\varepsilon(T)(x)$. The `change` command rewrites the goal as

$$
\forall z,w,\quad w\in T z \implies -\varepsilon\le \langle w-v,z-x\rangle.
$$

After `intro z w hw`, the proof uses two inequalities. From $h_\varepsilon:0\le\varepsilon$, the lemma `neg_nonpos.mpr` gives

$$
-\varepsilon\le 0.
$$

From the monotonicity component `hT.1 w hw v hv`, applied to $w\in T z$ and $v\in T x$, we get

$$
0\le \langle w-v,z-x\rangle.
$$

The command `le_trans` composes these two inequalities to obtain

$$
-\varepsilon\le \langle w-v,z-x\rangle.
$$

Therefore $v\in E_\varepsilon(T)(x)$, which proves the final inclusion.

