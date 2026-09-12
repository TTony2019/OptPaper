## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/ext_thm_1.lean`

## Lean statement
```lean
theorem weak_strong_closedness_maximal_monotone_graph
    (A : SetValuedOperator H H) (hA : SetValuedOperator.IsMaximalMonotone A)
    {x v : H} {xs vs : ℕ → H}
    (hxs : Tendsto (fun i : ℕ ↦ toWeakSpace ℝ H (xs i)) atTop
      (𝓝 (toWeakSpace ℝ H x)))
    (hvs : Tendsto vs atTop (𝓝 v))
    (hmem : ∀ i : ℕ, vs i ∈ A (xs i)) :
    v ∈ A x
```

## Statement explanation
The declaration `weak_strong_closedness_maximal_monotone_graph` concerns a set-valued operator $A:H\rightrightarrows H$ on a real Hilbert space $H$, with real inner product $\langle\cdot,\cdot\rangle$. The hypothesis $hA$ says that $A$ is maximal monotone. The fixed points are $x,v\in H$, and the sequences are $xs:\mathbb N\to H$ and $vs:\mathbb N\to H$. The hypotheses on the sequences are:

- $hxs$: the sequence $xs$ converges weakly to $x$, i.e.

$$
\mathrm{toWeakSpace}_{\mathbb R,H}(xs_i)\to \mathrm{toWeakSpace}_{\mathbb R,H}(x)
$$

  as $i\to\infty$. Equivalently, $xs_i\rightharpoonup x$.
- $hvs$: the sequence $vs$ converges strongly to $v$, i.e. $vs_i\to v$ in norm.
- $hmem$: for every $i$, the pair $(xs_i,vs_i)$ lies in the graph of $A$, i.e. $vs_i\in A(xs_i)$.

The conclusion is $v\in A x$. Thus the theorem says that the graph of a maximal monotone operator is sequentially closed when the first coordinate converges weakly and the second coordinate converges strongly: if $(xs_i,vs_i)\in \mathrm{graph}(A)$, $xs_i\rightharpoonup x$, and $vs_i\to v$, then $(x,v)\in \mathrm{graph}(A)$.

## Lean proof
```lean
by
  classical
  apply alvarez2004_mem_of_monotonically_related_to_graph hA
  intro y w hw
  have hmono_i : ∀ i : ℕ, 0 ≤ inner ℝ (vs i - w) (xs i - y) := by
    intro i
    exact hA.1 (vs i) (hmem i) w hw
  have hxs_bdd : Bornology.IsBounded (Set.range xs) :=
    bounded_range_of_tendsto_weakly hxs
  rcases (isBounded_iff_forall_norm_le (s := Set.range xs)).mp hxs_bdd with ⟨C, hC⟩
  have hxs_norm_le (i : ℕ) : ‖xs i‖ ≤ C := hC (xs i) ⟨i, rfl⟩
  let M : ℝ := max C 0
  have hxs_norm_le' (i : ℕ) : ‖xs i‖ ≤ M :=
    le_trans (hxs_norm_le i) (le_max_left _ _)
  have hxs_inner : ∀ u : H, Tendsto (fun i : ℕ ↦ inner ℝ (xs i) u) atTop
      (𝓝 (inner ℝ x u)) :=
    ((weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) xs x).mp hxs)
  have hvs_norm_sub_zero : Tendsto (fun i : ℕ ↦ ‖vs i - v‖) atTop (𝓝 0) := by
    simpa [sub_self] using (hvs.sub (tendsto_const_nhds (x := v))).norm
  have h_cross_inner_tendsto :
      Tendsto (fun i : ℕ ↦ inner ℝ (vs i - v) (xs i)) atTop (𝓝 0) := by
    have h_bound (i : ℕ) :
        |inner ℝ (vs i - v) (xs i)| ≤ ‖vs i - v‖ * M := by
      calc
        |inner ℝ (vs i - v) (xs i)| ≤ ‖vs i - v‖ * ‖xs i‖ := by
          simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (vs i - v) (xs i)
        _ ≤ ‖vs i - v‖ * M :=
          mul_le_mul_of_nonneg_left (hxs_norm_le' i) (norm_nonneg _)
    have h_prod_zero : Tendsto (fun i : ℕ ↦ ‖vs i - v‖ * M) atTop (𝓝 0) := by
      simpa [zero_mul] using Filter.Tendsto.mul hvs_norm_sub_zero tendsto_const_nhds
    have h_abs_tendsto : Tendsto (fun i : ℕ ↦ |inner ℝ (vs i - v) (xs i)|)
        atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ abs_nonneg _) h_bound h_prod_zero
    have h_neg_tendsto : Tendsto (fun i : ℕ ↦ -|inner ℝ (vs i - v) (xs i)|)
        atTop (𝓝 0) := by
      simpa using h_abs_tendsto.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_neg_tendsto h_abs_tendsto
    · intro i
      exact neg_abs_le _
    · intro i
      exact le_abs_self _
  have hvsxs_tendsto : Tendsto (fun i : ℕ ↦ inner ℝ (vs i) (xs i)) atTop
      (𝓝 (inner ℝ v x)) := by
    have h_weak_part : Tendsto (fun i : ℕ ↦ inner ℝ v (xs i)) atTop
        (𝓝 (inner ℝ v x)) := by
      simpa [real_inner_comm] using hxs_inner v
    have h_sum : Tendsto
        (fun i : ℕ ↦ inner ℝ (vs i - v) (xs i) + inner ℝ v (xs i)) atTop
        (𝓝 (0 + inner ℝ v x)) :=
      Filter.Tendsto.add h_cross_inner_tendsto h_weak_part
    simpa [← inner_add_left, sub_add_cancel] using h_sum
  have hvsy_tendsto : Tendsto (fun i : ℕ ↦ inner ℝ (vs i) y) atTop
      (𝓝 (inner ℝ v y)) :=
    hvs.inner tendsto_const_nhds
  have hwxs_tendsto : Tendsto (fun i : ℕ ↦ inner ℝ w (xs i)) atTop
      (𝓝 (inner ℝ w x)) := by
    simpa [real_inner_comm] using hxs_inner w
  have h_const : Tendsto (fun _ : ℕ ↦ inner ℝ w y) atTop (𝓝 (inner ℝ w y)) :=
    tendsto_const_nhds
  have h_total : Tendsto (fun i : ℕ ↦ inner ℝ (vs i - w) (xs i - y)) atTop
      (𝓝 (inner ℝ (v - w) (x - y))) := by
    have h := ((hvsxs_tendsto.sub hvsy_tendsto).sub hwxs_tendsto).add h_const
    convert h using 1
    · ext i
      simp [inner_sub_left, inner_sub_right]
      ring
    · simp [inner_sub_left, inner_sub_right]
      ring
  exact ge_of_tendsto h_total (Filter.Eventually.of_forall hmono_i)
```

## Proof explanation
The proof begins with `classical`, which only enables classical logic and has no mathematical content. It then applies the cited result `alvarez2004_mem_of_monotonically_related_to_graph`. That lemma says that if $T$ is maximal monotone and a point $u$ is monotonically related to every point of the graph of $T$, in the sense that

```math
\forall y\,w,\quad w\in T y \implies 0\le \langle u-w,x-y\rangle,
```

then $u\in T x$. In the present application, $T=A$, the lemma’s $u$ is the target point $v$, and the lemma’s $x$ is the target point $x$. Therefore the goal $v\in A x$ reduces to proving

```math
\forall y\,w,\quad w\in A y \implies 0\le \langle v-w,x-y\rangle.
```

The command `intro y w hw` fixes an arbitrary $y\in H$ and an arbitrary $w\in A y$.

Next, the proof establishes the pointwise monotonicity inequalities. For each $i$, since $vs_i\in A(xs_i)$ by `hmem i`, and $w\in A y$ by `hw`, the monotonicity part of the maximal-monotonicity hypothesis, used as `hA.1`, gives

$$
0\le \langle vs_i-w,xs_i-y\rangle.
$$

This is the statement of `hmono_i`. Mathematically, it says that the pairs $(xs_i,vs_i)$ and $(y,w)$ satisfy the monotonicity inequality for the operator $A$.

The proof then needs to pass this inequality to the limit. To do so, it first obtains boundedness of the weakly convergent sequence $xs$. The cited lemma `bounded_range_of_tendsto_weakly` says that if a sequence converges weakly, then its range is bounded. Applied to $hxs$, it gives `hxs_bdd : Bornology.IsBounded (Set.range xs)`. Using `isBounded_iff_forall_norm_le`, this boundedness is unpacked as the existence of a real constant $C$ such that

```math
\|xs_i\|\le C
```

for every $i$. The proof then defines $M=\max(C,0)$, so that $M$ is a nonnegative upper bound and

```math
\|xs_i\|\le M
```

for all $i$.

The proof also converts weak convergence of $xs$ into convergence of all inner products. The cited theorem `weakConvergence_iff_forall_tendsto_inner_right` states that, in the complete Hilbert-space setting, weak convergence of a sequence to $x$ is equivalent to convergence of the real inner products against every fixed vector:

$$
xs_i\rightharpoonup x
\quad\Longleftrightarrow\quad
\forall u,\quad \langle xs_i,u\rangle\to \langle x,u\rangle.
$$

Applying this to `hxs` gives `hxs_inner`: for every $u\in H$,

$$
\langle xs_i,u\rangle\to \langle x,u\rangle.
$$

This will be used with $u=v$ and with $u=w$.

From the strong convergence $hvs$, the proof obtains

```math
\|vs_i-v\|\to 0.
```

Indeed, $vs_i-v\to 0$ by subtracting the constant sequence $v$, and the norm is continuous, so its norm tends to $`\|0\|=0`$. This is `hvs_norm_sub_zero`.

The key cross term is

$$
\langle vs_i-v,xs_i\rangle.
$$

The proof shows that this tends to $0$. By Cauchy–Schwarz, implemented by `norm_inner_le_norm`,

```math
|\langle vs_i-v,xs_i\rangle|
\le \|vs_i-v\|\,\|xs_i\|.
```

Since $`\|xs_i\|\le M`$, this is bounded above by

```math
\|vs_i-v\|\,M,
```

and the latter tends to $0\cdot M=0$. The proof uses `squeeze_zero` to conclude that

$$
|\langle vs_i-v,xs_i\rangle|\to 0.
$$

Then it squeezes the signed inner product between

$$
-|\langle vs_i-v,xs_i\rangle|
\quad\text{and}\quad
|\langle vs_i-v,xs_i\rangle|,
$$

both of which tend to $0$, using `tendsto_of_tendsto_of_tendsto_of_le_of_le`. Hence

$$
\langle vs_i-v,xs_i\rangle\to 0.
$$

This is `h_cross_inner_tendsto`. Mathematically, it is the standard fact that a strongly convergent sequence paired with a weakly bounded sequence has vanishing cross inner product.

The proof then computes the limit of $\langle vs_i,xs_i\rangle$. It writes

$$
\langle vs_i,xs_i\rangle
=\langle vs_i-v,xs_i\rangle+\langle v,xs_i\rangle.
$$

The first summand tends to $0$ by `h_cross_inner_tendsto`. The second summand tends to $\langle v,x\rangle$ because $xs_i\rightharpoonup x$ and, using symmetry of the real inner product via `real_inner_comm`, the inner products $\langle v,xs_i\rangle$ converge to $\langle v,x\rangle$. Therefore

$$
\langle vs_i,xs_i\rangle\to \langle v,x\rangle.
$$

This is `hvsxs_tendsto`.

Similarly, the proof establishes

$$
\langle vs_i,y\rangle\to \langle v,y\rangle
$$

from strong convergence $vs_i\to v$, using continuity of the inner product. It also establishes

$$
\langle w,xs_i\rangle\to \langle w,x\rangle
$$

from weak convergence of $xs$, again using symmetry of the real inner product. Finally, the constant term $\langle w,y\rangle$ converges to itself.

Combining these limits, the proof obtains

$$
\langle vs_i-w,xs_i-y\rangle\to \langle v-w,x-y\rangle.
$$

Indeed, bilinearity gives the pointwise identity

$$
\langle vs_i-w,xs_i-y\rangle
=\langle vs_i,xs_i\rangle-\langle vs_i,y\rangle
-\langle w,xs_i\rangle+\langle w,y\rangle,
$$

and the limit of the right-hand side is

$$
\langle v,x\rangle-\langle v,y\rangle-\langle w,x\rangle+\langle w,y\rangle
=\langle v-w,x-y\rangle.
$$

The `convert` command reduces the desired limit statement to the equality of these expressions, `ext i` proves the pointwise sequence identity, and `simp` with the inner-product linearity lemmas together with `ring` verifies the algebraic rearrangements.

At this point, every term

$$
\langle vs_i-w,xs_i-y\rangle
$$

is nonnegative by `hmono_i`. Since the sequence converges to $\langle v-w,x-y\rangle$, the limit is also nonnegative:

$$
0\le \langle v-w,x-y\rangle.
$$

This is obtained by `ge_of_tendsto` applied to `h_total` and the eventual nonnegativity supplied by `Filter.Eventually.of_forall hmono_i`. Thus $v$ is monotonically related to the arbitrary graph point $(y,w)$. Since $y$ and $w\in A y$ were arbitrary, the Alvarez maximality criterion applies and concludes $v\in A x$.

The proof does not use `rw` or `linarith`; the algebraic identities are handled by `simp` and `ring`, while the limiting arguments are handled by the cited weak-convergence, boundedness, and maximal-monotonicity facts.

