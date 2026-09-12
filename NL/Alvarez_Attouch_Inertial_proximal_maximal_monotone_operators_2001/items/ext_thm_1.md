## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/ext_thm_1.lean`

## Lean statement
```lean
theorem weak_strong_closedness_maximal_monotone_graph
    (A : SetValuedOperator H H) (hA : A.IsMaximalMonotone)
    {x u : H} {xs us : ℕ → H}
    (hxs : Tendsto (fun n => toWeakSpace ℝ H (xs n)) atTop
      (𝓝 (toWeakSpace ℝ H x)))
    (hus : Tendsto us atTop (𝓝 u))
    (hmem : ∀ n : ℕ, us n ∈ A (xs n)) :
    u ∈ A x
```

## Statement explanation
The theorem `weak_strong_closedness_maximal_monotone_graph` says that the graph of a maximal monotone set-valued operator on a real Hilbert space is closed under weak convergence in the first coordinate and strong convergence in the second coordinate.

In the statement, $H$ is the ambient real Hilbert space, and $A : H \to \mathcal P(H)$ is a set-valued operator from $H$ to subsets of $H$. The hypothesis $hA$ says that $A$ is maximal monotone. The points $x$ and $u$ lie in $H$, and the sequences $xs, us : \mathbb N \to H$ are indexed by natural numbers. The hypothesis $hxs$ says that $xs_n$ converges weakly to $x$, expressed in Lean as convergence of `toWeakSpace ℝ H (xs n)` to `toWeakSpace ℝ H x`. The hypothesis $hus$ says that $us_n$ converges strongly, i.e. in norm, to $u$. The hypothesis $hmem$ says that for every $n$, $us_n \in A(xs_n)$. Thus the pairs $(xs_n,us_n)$ all lie in the graph of $A$. The conclusion is $u \in A(x)$, i.e. $(x,u)$ also lies in the graph of $A$.

In ordinary mathematical language, the theorem states: if $(xs_n,us_n)$ are points in the graph of a maximal monotone operator $A$, and if $xs_n \rightharpoonup x$ weakly while $us_n \to u$ strongly, then $(x,u)$ is still in the graph of $A$. This is exactly weak-strong closedness of the maximal monotone graph.

## Lean proof
```lean
by
  classical
  apply mem_of_monotonically_related_to_graph hA
  intro y v hv
  have hmono_n : ∀ n : ℕ, 0 ≤ inner ℝ (us n - v) (xs n - y) := by
    intro n
    exact hA.1 (us n) (hmem n) v hv
  have hxs_bdd : Bornology.IsBounded (Set.range xs) :=
    bounded_range_of_tendsto_weakly hxs
  rcases (isBounded_iff_forall_norm_le (s := Set.range xs)).mp hxs_bdd with ⟨C, hC⟩
  let M : ℝ := max C 0
  have hxs_norm_le' (n : ℕ) : ‖xs n‖ ≤ M :=
    le_trans (hC (xs n) ⟨n, rfl⟩) (le_max_left _ _)
  have hxs_inner : ∀ z : H, Tendsto (fun n : ℕ ↦ inner ℝ (xs n) z) atTop
      (𝓝 (inner ℝ x z)) :=
    ((weakConvergence_iff_forall_tendsto_inner_right (𝓗 := H) xs x).mp hxs)
  have hus_norm_sub_zero : Tendsto (fun n : ℕ ↦ ‖us n - u‖) atTop (𝓝 0) := by
    simpa [sub_self] using (hus.sub (tendsto_const_nhds (x := u))).norm
  have h_cross_inner_tendsto :
      Tendsto (fun n : ℕ ↦ inner ℝ (us n - u) (xs n)) atTop (𝓝 0) := by
    have h_bound (n : ℕ) :
        |inner ℝ (us n - u) (xs n)| ≤ ‖us n - u‖ * M := by
      calc
        |inner ℝ (us n - u) (xs n)| ≤ ‖us n - u‖ * ‖xs n‖ := by
          simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (us n - u) (xs n)
        _ ≤ ‖us n - u‖ * M :=
          mul_le_mul_of_nonneg_left (hxs_norm_le' n) (norm_nonneg _)
    have h_prod_zero : Tendsto (fun n : ℕ ↦ ‖us n - u‖ * M) atTop (𝓝 0) := by
      simpa [zero_mul] using Filter.Tendsto.mul hus_norm_sub_zero tendsto_const_nhds
    have h_abs_tendsto : Tendsto (fun n : ℕ ↦ |inner ℝ (us n - u) (xs n)|)
        atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ abs_nonneg _) h_bound h_prod_zero
    have h_neg_tendsto : Tendsto (fun n : ℕ ↦ -|inner ℝ (us n - u) (xs n)|)
        atTop (𝓝 0) := by
      simpa using h_abs_tendsto.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_neg_tendsto h_abs_tendsto
    · intro n
      exact neg_abs_le _
    · intro n
      exact le_abs_self _
  have husxs_tendsto : Tendsto (fun n : ℕ ↦ inner ℝ (us n) (xs n)) atTop
      (𝓝 (inner ℝ u x)) := by
    have h_weak_part : Tendsto (fun n : ℕ ↦ inner ℝ u (xs n)) atTop
        (𝓝 (inner ℝ u x)) := by
      simpa [real_inner_comm] using hxs_inner u
    have h_sum : Tendsto
        (fun n : ℕ ↦ inner ℝ (us n - u) (xs n) + inner ℝ u (xs n)) atTop
        (𝓝 (0 + inner ℝ u x)) :=
      Filter.Tendsto.add h_cross_inner_tendsto h_weak_part
    simpa [← inner_add_left, sub_add_cancel] using h_sum
  have husy_tendsto : Tendsto (fun n : ℕ ↦ inner ℝ (us n) y) atTop
      (𝓝 (inner ℝ u y)) :=
    hus.inner tendsto_const_nhds
  have hvxs_tendsto : Tendsto (fun n : ℕ ↦ inner ℝ v (xs n)) atTop
      (𝓝 (inner ℝ v x)) := by
    simpa [real_inner_comm] using hxs_inner v
  have h_const : Tendsto (fun _ : ℕ ↦ inner ℝ v y) atTop (𝓝 (inner ℝ v y)) :=
    tendsto_const_nhds
  have h_total : Tendsto (fun n : ℕ ↦ inner ℝ (us n - v) (xs n - y)) atTop
      (𝓝 (inner ℝ (u - v) (x - y))) := by
    have h := ((husxs_tendsto.sub husy_tendsto).sub hvxs_tendsto).add h_const
    convert h using 1
    · ext n
      simp [inner_sub_left, inner_sub_right]
      ring
    · simp [inner_sub_left, inner_sub_right]
      ring
  exact ge_of_tendsto h_total (Filter.Eventually.of_forall hmono_n)
```

## Proof explanation
The proof begins with `classical`, which only permits classical logic and has no mathematical content. The main reduction is the command `apply mem_of_monotonically_related_to_graph hA`. The cited lemma `mem_of_monotonically_related_to_graph` says that if $T$ is maximal monotone and a pair $(x,u)$ satisfies

$$
0 \le \langle u-v, x-y\rangle
$$

for every $y,v$ with $v \in T(y)$, then $u \in T(x)$. This is the standard maximality characterization of maximal monotone operators: a pair that is monotonically related to every point of the graph must already lie in the graph. Thus, to prove $u \in A(x)$, it is enough to prove the monotone relation

$$
0 \le \langle u-v, x-y\rangle
$$

for every $y,v$ with $v \in A(y)$.

The proof then performs `intro y v hv`, fixing arbitrary $y,v$ and assuming $v \in A(y)$. The goal is now

$$
0 \le \langle u-v, x-y\rangle.
$$

Next, the proof establishes `hmono_n`, namely

$$
\forall n,\quad 0 \le \langle us_n-v, xs_n-y\rangle.
$$

This uses `hA.1`, the monotonicity part of the maximal monotonicity hypothesis. Since $us_n \in A(xs_n)$ by `hmem n` and $v \in A(y)$ by `hv`, monotonicity gives exactly

$$
0 \le \langle us_n-v, xs_n-y\rangle.
$$

The proof then needs a uniform bound on $xs_n$. It invokes `bounded_range_of_tendsto_weakly hxs`. That cited lemma says that if $xs_n$ converges weakly to $x$, then the ordinary set of values $`\{xs_n : n \in \mathbb N\}`$ is bounded in norm. Hence `hxs_bdd` is the assertion that the range of $xs$ is bounded. Using `isBounded_iff_forall_norm_le`, the proof extracts a constant $C$ such that

```math
\|xs_n\| \le C
```

for every $n$. It then defines

$$
M = \max(C,0).
$$

Since $C \le \max(C,0)$, the estimate

```math
\|xs_n\| \le M
```

holds for every $n$. This uniform bound will be used to control the cross term $\langle us_n-u, xs_n\rangle$.

To pass from weak convergence of $xs_n$ to convergence of inner products, the proof uses `weakConvergence_iff_forall_tendsto_inner_right`. That theorem says that in a complete real Hilbert space, weak convergence $xs_n \rightharpoonup x$ is equivalent to

$$
\forall z,\quad \langle xs_n,z\rangle \to \langle x,z\rangle.
$$

Applying the forward direction to `hxs` gives `hxs_inner`:

$$
\forall z,\quad \langle xs_n,z\rangle \to \langle x,z\rangle.
$$

In particular, using real symmetry of the inner product via `real_inner_comm`, this also yields

$$
\langle u,xs_n\rangle \to \langle u,x\rangle
$$

and

$$
\langle v,xs_n\rangle \to \langle v,x\rangle.
$$

The strong convergence hypothesis `hus` is used to show

```math
\|us_n-u\| \to 0.
```

Indeed, $us_n-u \to u-u=0$, and taking norms gives $`\|us_n-u\| \to 0`$. The proof records this as `hus_norm_sub_zero`.

Next, the proof shows that the cross term $\langle us_n-u, xs_n\rangle$ tends to $0$. For each $n$, Cauchy-Schwarz gives

```math
|\langle us_n-u, xs_n\rangle|
\le \|us_n-u\|\,\|xs_n\|.
```

Using $`\|xs_n\| \le M`$, this becomes

```math
|\langle us_n-u, xs_n\rangle|
\le \|us_n-u\|\,M.
```

Since $`\|us_n-u\| \to 0`$, the product$`\|us_n-u\|M`$tends to$0$. By the squeeze theorem, implemented by `squeeze_zero`, the absolute value $|\langle us_n-u, xs_n\rangle|$ tends to $0$. Then, using

$$
-|\langle us_n-u, xs_n\rangle|
\le \langle us_n-u, xs_n\rangle
\le |\langle us_n-u, xs_n\rangle|,
$$

the proof concludes that

$$
\langle us_n-u, xs_n\rangle \to 0.
$$

With this cross term controlled, the proof shows

$$
\langle us_n,xs_n\rangle \to \langle u,x\rangle.
$$

It writes

$$
us_n = (us_n-u)+u,
$$

so

$$
\langle us_n,xs_n\rangle
=\langle us_n-u,xs_n\rangle + \langle u,xs_n\rangle.
$$

The first term tends to $0$, and the second term tends to $\langle u,x\rangle$ by the weak-convergence inner-product characterization. Adding limits gives the claimed convergence.

The remaining terms are then handled:

- $\langle us_n,y\rangle \to \langle u,y\rangle$, using strong convergence $us_n \to u$ and continuity of the inner product.
- $\langle v,xs_n\rangle \to \langle v,x\rangle$, again from the weak-convergence inner-product characterization and real symmetry.
- The constant sequence $\langle v,y\rangle$ tends to $\langle v,y\rangle$.

Combining these limits, the proof obtains convergence of the full expression:

$$
\langle us_n,xs_n\rangle
-\langle us_n,y\rangle
-\langle v,xs_n\rangle
+\langle v,y\rangle
\to
\langle u,x\rangle
-\langle u,y\rangle
-\langle v,x\rangle
+\langle v,y\rangle.
$$

Using bilinearity of the inner product, specifically `inner_sub_left` and `inner_sub_right`, this expression is equal to

$$
\langle us_n-v, xs_n-y\rangle,
$$

and its limit is equal to

$$
\langle u-v, x-y\rangle.
$$

The tactics `convert`, `ext n`, `simp`, and `ring` verify these algebraic identities.

Finally, the proof has shown that

$$
\langle us_n-v, xs_n-y\rangle \to \langle u-v, x-y\rangle
$$

and that every term $\langle us_n-v, xs_n-y\rangle$ is nonnegative. The command `Filter.Eventually.of_forall hmono_n` turns the pointwise nonnegativity into eventual nonnegativity. Then `ge_of_tendsto` applies the standard limit inequality: if a sequence tends to a limit and is eventually nonnegative, then its limit is nonnegative. Hence

$$
0 \le \langle u-v, x-y\rangle.
$$

This is exactly the condition required by `mem_of_monotonically_related_to_graph`. Therefore maximality of $A$ gives $u \in A(x)$, completing the proof.

