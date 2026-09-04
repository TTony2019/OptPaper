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
The theorem proves a weak-strong closedness property of the graph of a maximal monotone operator. In the ambient real Hilbert space \(H\), let \(A\) be a set-valued operator from \(H\) to \(H\), so that \(A(x)\) is a set in \(H\) for each \(x\). The hypothesis \(hA\) says that \(A\) is maximal monotone. Given points \(x,u\in H\) and sequences \(xs,us:\mathbb{N}\to H\), assume that:

- \(hxs\): the sequence \(xs_n\) converges weakly to \(x\), expressed as
  \[
  \operatorname{toWeakSpace}_{\mathbb R,H}(xs_n)\to \operatorname{toWeakSpace}_{\mathbb R,H}(x)
  \]
  along \(n\to\infty\);
- \(hus\): the sequence \(us_n\) converges to \(u\) in the ordinary norm topology of \(H\);
- \(hmem\): for every \(n\in\mathbb N\), \(us_n\in A(xs_n)\).

The conclusion is that the limit point lies in the graph:
\[
u\in A(x).
\]
Thus, if the first coordinates \(xs_n\) converge weakly to \(x\), the second coordinates \(us_n\) converge strongly to \(u\), and each pair \((xs_n,us_n)\) is in the graph of \(A\), then \((x,u)\) is also in the graph of \(A\).

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
The proof uses the maximal monotonicity of \(A\) to reduce the goal to checking that the candidate point \((x,u)\) is monotonically related to the graph of \(A\). The first step is

\[
\verb|apply mem_of_monotonically_related_to_graph hA|
\]

This lemma says that if \(A\) is maximal monotone and for every \((y,v)\) in the graph of \(A\) one has
\[
0\le \langle u-v,\ x-y\rangle,
\]
then \(u\in A(x)\). After this, the proof introduces arbitrary \(y,v\in H\) with \(v\in A(y)\), and the remaining goal is exactly that inequality.

First, the proof records the monotonicity of \(A\) on the given graph points:

\[
\verb|hmono_n|:\quad 0\le \langle us_n-v,\ xs_n-y\rangle
\]

for every \(n\). This follows from \(hA.1\), the monotonicity part of maximal monotonicity, using \(us_n\in A(xs_n)\) and \(v\in A(y)\).

Next, the proof needs to pass this inequality to the limit. To do so, it shows that the sequence
\[
\langle us_n-v,\ xs_n-y\rangle
\]
tends to
\[
\langle u-v,\ x-y\rangle.
\]

A key intermediate fact is that the weakly convergent sequence \(xs\) is bounded. The proof obtains this with

\[
\verb|bounded_range_of_tendsto_weakly hxs|,
\]

then chooses a constant \(C\) bounding the norms of the range of \(xs\), and sets \(M=\max(C,0)\) so that \(M\ge 0\) and
\[
\|xs_n\|\le M
\]
for all \(n\).

The proof also uses the characterization of weak convergence in terms of inner products:

\[
\verb|weakConvergence_iff_forall_tendsto_inner_right|
\]

This gives that for every fixed \(z\in H\),
\[
\langle xs_n,z\rangle \to \langle x,z\rangle.
\]

Since \(us_n\to u\) strongly, one has
\[
\|us_n-u\|\to 0.
\]

The proof then shows that the mixed term
\[
\langle us_n-u,\ xs_n\rangle
\]
tends to \(0\). This is done by the Cauchy-Schwarz inequality:
\[
|\langle us_n-u,\ xs_n\rangle|
\le \|us_n-u\|\,\|xs_n\|
\le \|us_n-u\|\,M.
\]
Because \(\|us_n-u\|\to 0\) and \(M\) is constant, the right side tends to \(0\). The squeeze theorem, implemented with `squeeze_zero`, forces the absolute value, and therefore the mixed inner product, to tend to \(0\).

Using this, the proof computes the limit of
\[
\langle us_n,\ xs_n\rangle.
\]
It writes
\[
us_n=(us_n-u)+u
\]
and obtains
\[
\langle us_n,\ xs_n\rangle
=
\langle us_n-u,\ xs_n\rangle
+
\langle u,\ xs_n\rangle.
\]
The first term tends to \(0\), and the second term tends to \(\langle u,x\rangle\) by weak convergence. Hence
\[
\langle us_n,xs_n\rangle \to \langle u,x\rangle.
\]

Similarly, the proof obtains the limits:
\[
\langle us_n,y\rangle \to \langle u,y\rangle
\]
by strong convergence of \(us_n\), and
\[
\langle v,xs_n\rangle \to \langle v,x\rangle
\]
by weak convergence of \(xs_n\). The term \(\langle v,y\rangle\) is constant.

Combining these limits linearly, the proof shows that
\[
\langle us_n-v,\ xs_n-y\rangle
\to
\langle u-v,\ x-y\rangle.
\]
The algebraic rewriting is handled with `convert` and `ring`, using the bilinearity of the inner product.

Finally, because for every \(n\)
\[
0\le \langle us_n-v,\ xs_n-y\rangle,
\]
the limit inequality follows:
\[
0\le \langle u-v,\ x-y\rangle.
\]
This is obtained by `ge_of_tendsto`, which passes a pointwise inequality through a limit. Since \(y\) and \(v\) were arbitrary graph elements, the maximal monotonicity criterion gives \(u\in A(x)\).

