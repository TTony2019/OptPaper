## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/ext_thm_1.lean`

## Lean statement
```lean
theorem epsilon_enlargement_demiclosed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (y v : ℕ → H) (ε : ℕ → ℝ) (yLimit vLimit : H)
    (hy : Tendsto (fun j ↦ toWeakSpace ℝ H (y j)) Filter.atTop
      (nhds (toWeakSpace ℝ H yLimit)))
    (hv : Tendsto v Filter.atTop (nhds vLimit))
    (hε : Tendsto ε Filter.atTop (nhds 0))
    (hε_nonneg : ∀ j, 0 ≤ ε j)
    (hm : ∀ j, v j ∈ epsilonEnlargement T (ε j) (hε_nonneg j) (y j)) :
    vLimit ∈ T yLimit
```

## Statement explanation
The declaration states a demiclosedness property of the epsilon-enlargement of a maximal monotone operator on a real Hilbert space. The space \(H\) is assumed to be a complete real inner product space, so it is a Hilbert space. The operator \(T\colon H\rightrightarrows H\) is a set-valued operator from \(H\) to subsets of \(H\), and it is assumed to be maximal monotone. There are sequences \(y\colon\mathbb N\to H\), \(v\colon\mathbb N\to H\), and \(\epsilon\colon\mathbb N\to\mathbb R\), together with limit points \(y_\infty,v_\infty\in H\). The hypotheses are:

1. \(y_j\) converges weakly to \(y_\infty\). Formally this is expressed by convergence in the weak space of the images of \(y_j\) to the image of \(y_\infty\).
2. \(v_j\) converges strongly, i.e. in norm, to \(v_\infty\).
3. \(\epsilon_j\to0\).
4. \(\epsilon_j\ge0\) for every \(j\).
5. For every \(j\),
   \[
   v_j\in T^{\epsilon_j}(y_j),
   \]
   where \(T^\epsilon\) is the epsilon-enlargement of \(T\), defined by
   \[
   T^\epsilon(x)
   =
   \{\,v\in H:\forall z,w,\ w\in T(z)\Rightarrow
   \langle w-v,z-x\rangle\ge-\epsilon\,\}.
   \]
   Equivalently,
   \[
   \langle w-v_j,z-y_j\rangle\ge-\epsilon_j
   \]
   for every \(z\) and every \(w\in T(z)\).

The conclusion is that the limit point \(v_\infty\) belongs to the original operator at the weak limit point:
\[
v_\infty\in T(y_\infty).
\]
Thus, if points \(v_j\) are approximately in \(T(y_j)\) with nonnegative enlargement parameters tending to \(0\), and if \(y_j\) converges weakly while \(v_j\) converges strongly, then the strong limit \(v_\infty\) is exactly in \(T(y_\infty)\). This is precisely the statement that the graph of the epsilon-enlargement is demiclosed with respect to weak convergence in the first variable and strong convergence in the second variable.

## Lean proof
```lean
by
  apply mem_of_monotonically_related_to_graph hT
  intro z w hw
  have h_eps_le : ∀ j, -ε j ≤ inner ℝ (y j - z) (v j - w) := by
    intro j
    have hj := hm j
    have h_eq : inner ℝ (w - v j) (z - y j) = inner ℝ (y j - z) (v j - w) := by
      simp [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    simpa [epsilonEnlargement, h_eq] using hj z w hw
  have hy_bdd : Bornology.IsBounded (Set.range y) :=
    bounded_range_of_tendsto_weakly hy
  rcases isBounded_iff_forall_norm_le.mp hy_bdd with ⟨M, hM⟩
  have hM_sub : ∀ j, ‖y j - yLimit‖ ≤ M + ‖yLimit‖ := by
    intro j
    calc
      ‖y j - yLimit‖ ≤ ‖y j‖ + ‖yLimit‖ := norm_sub_le _ _
      _ ≤ M + ‖yLimit‖ := by
        gcongr
        exact hM (y j) (Set.mem_range_self j)
  have hv_norm_tendsto : Tendsto (fun j => ‖v j - vLimit‖) atTop (nhds 0) := by
    have hv_sub : Tendsto (fun j => v j - vLimit) atTop (nhds 0) := by
      simpa using hv.sub_const vLimit
    simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hv_sub)
  have hlim1 : Tendsto (fun j => inner ℝ (y j - yLimit) (v j - vLimit)) atTop
      (nhds (0 : ℝ)) := by
    have hbound : ∀ j, ‖inner ℝ (y j - yLimit) (v j - vLimit)‖ ≤
        (M + ‖yLimit‖) * ‖v j - vLimit‖ := by
      intro j
      calc
        ‖inner ℝ (y j - yLimit) (v j - vLimit)‖ =
            |inner ℝ (y j - yLimit) (v j - vLimit)| := by rw [Real.norm_eq_abs]
        _ ≤ ‖y j - yLimit‖ * ‖v j - vLimit‖ := abs_real_inner_le_norm _ _
        _ ≤ (M + ‖yLimit‖) * ‖v j - vLimit‖ := by
          gcongr
          exact hM_sub j
    have hprod : Tendsto (fun j => (M + ‖yLimit‖) * ‖v j - vLimit‖) atTop
        (nhds (0 : ℝ)) := by
      simpa using hv_norm_tendsto.const_mul (M + ‖yLimit‖)
    exact squeeze_zero_norm hbound hprod
  have hlim2 : Tendsto (fun j => inner ℝ (yLimit - z) (v j - vLimit)) atTop
      (nhds (0 : ℝ)) := by
    have hsub : Tendsto (fun j => v j - vLimit) atTop (nhds 0) := by
      simpa using hv.sub_const vLimit
    simpa using Filter.Tendsto.inner (tendsto_const_nhds (x := yLimit - z)) hsub
  have hlim3 : Tendsto (fun j => inner ℝ (y j - z) (vLimit - w)) atTop
      (nhds (inner ℝ (yLimit - z) (vLimit - w))) := by
    have hcoord : Tendsto (fun j => inner ℝ (y j) (vLimit - w)) atTop
        (nhds (inner ℝ yLimit (vLimit - w))) := by
      simpa using (weakSpace_continuous_inner_right (vLimit - w)).tendsto
        (toWeakSpace ℝ H yLimit) |>.comp hy
    simpa [inner_sub_left] using hcoord.sub_const (inner ℝ z (vLimit - w))
  have hdecomp : ∀ j, inner ℝ (y j - z) (v j - w) =
      inner ℝ (y j - yLimit) (v j - vLimit) +
        inner ℝ (yLimit - z) (v j - vLimit) +
          inner ℝ (y j - z) (vLimit - w) := by
    intro j
    calc
      inner ℝ (y j - z) (v j - w) =
          inner ℝ (y j - z) ((v j - vLimit) + (vLimit - w)) := by
            simp [sub_add_sub_cancel]
      _ = inner ℝ (y j - z) (v j - vLimit) + inner ℝ (y j - z) (vLimit - w) := by
            rw [inner_add_right]
      _ = inner ℝ ((y j - yLimit) + (yLimit - z)) (v j - vLimit) +
          inner ℝ (y j - z) (vLimit - w) := by simp [sub_add_sub_cancel]
      _ = (inner ℝ (y j - yLimit) (v j - vLimit) +
          inner ℝ (yLimit - z) (v j - vLimit)) +
          inner ℝ (y j - z) (vLimit - w) := by rw [inner_add_left]
      _ = inner ℝ (y j - yLimit) (v j - vLimit) +
          inner ℝ (yLimit - z) (v j - vLimit) +
          inner ℝ (y j - z) (vLimit - w) := by ring
  have hlim : Tendsto (fun j => inner ℝ (y j - z) (v j - w)) atTop
      (nhds (inner ℝ (yLimit - z) (vLimit - w))) := by
    have hsum := hlim1.add (hlim2.add hlim3)
    simpa [hdecomp, add_assoc] using hsum
  have hneg_eps : Tendsto (fun j => -ε j) atTop (nhds (0 : ℝ)) := by
    simpa using hε.neg
  have hineq : 0 ≤ inner ℝ (yLimit - z) (vLimit - w) := by
    apply le_of_tendsto_of_tendsto hneg_eps hlim
    exact Filter.Eventually.of_forall h_eps_le
  simpa [real_inner_comm] using hineq
```

## Proof explanation
The proof begins by applying the maximal-monotonicity characterization `mem_of_monotonically_related_to_graph` to the hypothesis that \(T\) is maximal monotone. That result says that if a point \(u\) is monotonically related to every graph pair of \(T\), meaning
\[
\forall z,w,\quad w\in T(z)\Rightarrow
\langle u-w,x-z\rangle\ge0,
\]
then \(u\in T(x)\). Applying this with \(u=v_\infty\) and \(x=y_\infty\) reduces the goal to proving
\[
\forall z,w,\quad w\in T(z)\Rightarrow
\langle v_\infty-w,y_\infty-z\rangle\ge0.
\]
The command `intro z w hw` fixes arbitrary \(z,w\in H\) and assumes \(w\in T(z)\).

For each \(j\), the hypothesis \(v_j\in T^{\epsilon_j}(y_j)\) says, after unfolding the definition of the epsilon-enlargement, that
\[
\langle w-v_j,z-y_j\rangle\ge-\epsilon_j.
\]
The proof rewrites the left-hand side using the identity
\[
\langle w-v_j,z-y_j\rangle
=
\langle y_j-z,v_j-w\rangle.
\]
This identity follows from bilinearity of the inner product and real symmetry \(\langle a,b\rangle=\langle b,a\rangle\). The tactic `simp` applies the subtraction rules for inner products, and `ring` closes the resulting scalar rearrangement. Hence for every \(j\),
\[
-\epsilon_j\le \langle y_j-z,v_j-w\rangle.
\]

Next the proof needs a uniform bound on the weakly convergent sequence \(y_j\). It invokes `bounded_range_of_tendsto_weakly` on the weak convergence hypothesis \(y_j\rightharpoonup y_\infty\). That lemma states that a weakly convergent sequence in a Hilbert space has bounded range. Therefore the set \(\{y_j:j\in\mathbb N\}\) is bounded. Since a set in a normed space is bounded exactly when some \(M\) bounds the norms of all its elements, the proof extracts \(M\) such that
\[
\|y_j\|\le M
\]
for every \(j\). Then it proves
\[
\|y_j-y_\infty\|\le M+\|y_\infty\|,
\]
using the triangle inequality
\[
\|y_j-y_\infty\|\le \|y_j\|+\|y_\infty\|
\]
and monotonicity of addition. The tactic `gcongr` is used for that monotone inequality step.

From the strong convergence \(v_j\to v_\infty\), the proof also obtains
\[
\|v_j-v_\infty\|\to0.
\]
First \(v_j-v_\infty\to0\) by subtracting the constant \(v_\infty\), and then the equivalence between convergence of a sequence to \(0\) and convergence of its norms to \(0\) gives the stated norm convergence.

The next step is the limit
\[
\langle y_j-y_\infty,v_j-v_\infty\rangle\to0.
\]
For each \(j\), Cauchy–Schwarz gives
\[
|\langle y_j-y_\infty,v_j-v_\infty\rangle|
\le
\|y_j-y_\infty\|\,\|v_j-v_\infty\|.
\]
Using the bound \(\|y_j-y_\infty\|\le M+\|y_\infty\|\), this is at most
\[
(M+\|y_\infty\|)\,\|v_j-v_\infty\|.
\]
The right-hand side tends to \(0\) because \(\|v_j-v_\infty\|\to0\) and \(M+\|y_\infty\|\) is a constant. The squeeze theorem for norms, `squeeze_zero_norm`, then yields
\[
\langle y_j-y_\infty,v_j-v_\infty\rangle\to0.
\]

The proof also shows
\[
\langle y_\infty-z,v_j-v_\infty\rangle\to0.
\]
Indeed, for fixed first argument \(y_\infty-z\), the inner product is continuous in its second argument. Since \(v_j-v_\infty\to0\), the values tend to \(\langle y_\infty-z,0\rangle=0\).

To handle the term involving \(y_j\) and the fixed vector \(v_\infty-w\), the proof uses `weakSpace_continuous_inner_right`. That theorem says that for each fixed \(c\in H\), the function
\[
x\mapsto \langle x,c\rangle
\]
is continuous for the weak topology. Taking \(c=v_\infty-w\) and composing with \(y_j\rightharpoonup y_\infty\) gives
\[
\langle y_j,v_\infty-w\rangle\to
\langle y_\infty,v_\infty-w\rangle.
\]
Subtracting the constant \(\langle z,v_\infty-w\rangle\), which is valid by bilinearity, yields
\[
\langle y_j-z,v_\infty-w\rangle\to
\langle y_\infty-z,v_\infty-w\rangle.
\]

The proof then records the algebraic decomposition
\[
\langle y_j-z,v_j-w\rangle
=
\langle y_j-y_\infty,v_j-v_\infty\rangle
+
\langle y_\infty-z,v_j-v_\infty\rangle
+
\langle y_j-z,v_\infty-w\rangle.
\]
This comes from writing
\[
v_j-w=(v_j-v_\infty)+(v_\infty-w),
\qquad
y_j-z=(y_j-y_\infty)+(y_\infty-z)
\]
and expanding the inner product by bilinearity. The rewrites `inner_add_right` and `inner_add_left` perform these additions inside the inner product.

Adding the three established limits gives
\[
\langle y_j-z,v_j-w\rangle
\to
\langle y_\infty-z,v_\infty-w\rangle.
\]
At the same time, \(\epsilon_j\to0\) implies \(-\epsilon_j\to0\). Since for every \(j\),
\[
-\epsilon_j\le \langle y_j-z,v_j-w\rangle,
\]
the order-limit theorem `le_of_tendsto_of_tendsto` implies
\[
0\le \langle y_\infty-z,v_\infty-w\rangle.
\]
Finally, real symmetry of the inner product converts this to
\[
0\le \langle v_\infty-w,y_\infty-z\rangle,
\]
which is exactly the required monotone-relatedness condition for arbitrary \(z,w\) with \(w\in T(z)\). Therefore the characterization `mem_of_monotonically_related_to_graph` applies and gives
\[
v_\infty\in T(y_\infty).
\]
That is the desired demiclosedness conclusion.

