## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/ext_thm_4.lean`

## Lean statement
```lean
theorem maximal_monotone_surjective_of_bounded_domain {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {U : SetValuedOperator H H}
    (hU : U.IsMaximalMonotone) (hdom : Bornology.IsBounded U.dom) :
    U.range = Set.univ ∧ U.zeros.Nonempty
```

## Statement explanation
This declaration states a surjectivity theorem for a maximal monotone set-valued operator $U$ on a real Hilbert space $H$. The space $H$ has an additive normed group structure, a real inner product, and is complete; hence it is a real Hilbert space. The operator $U$ is a set-valued operator from $H$ to $H$, so for each $x\in H$, $U x$ is a subset of $H$. The hypothesis `hU : U.IsMaximalMonotone` says that $U$ is maximal monotone: first, its graph is monotone, meaning that whenever $u\in U x$ and $v\in U y$, one has

$$
0\le \langle u-v,x-y\rangle,
$$

and second, no pair $(x,u)$ outside the graph can be added without violating this inequality. Equivalently, if a pair $(x,u)$ is monotonically related to every point of the graph of $U$, then $u\in U x$.

The hypothesis `hdom : Bornology.IsBounded U.dom` says that the domain of $U$,

$$
U.\operatorname{dom}=\{x\in H: U x\ne \varnothing\},
$$

is bounded in the norm topology of $H$. The conclusion is the conjunction

$$
U.\operatorname{range}=\operatorname{Set.univ}
\quad\text{and}\quad
U.\operatorname{zeros}\ne \varnothing.
$$

Here $U.\operatorname{range}=\bigcup_{x\in H} U x$, so the first part says that every point $p\in H$ belongs to $U x$ for some $x\in H$. The second part says that there exists $x\in H$ such that $0\in U x$; in the proof this is obtained from the first part by specializing to $p=0$, using the characterization that $x\in U.\operatorname{zeros}$ exactly when $0\in U x$. Thus the theorem says that a maximal monotone operator on a real Hilbert space whose domain is bounded is automatically surjective and has nonempty zero set.

## Lean proof
```lean
by
  classical
  let c : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hc : ∀ n, 0 < c n := by
    intro n
    dsimp [c]
    positivity
  have hres : ∀ n : ℕ, ∀ p : H, ∃ x u : H, u ∈ U x ∧ x + c n • u = c n • p := by
    intro n p
    rcases minty_surjective_of_maximal_monotone
        (T := fun x : H => c n • U x) (positive_scaled_maximal_monotone_local hU (hc n)) (c n • p) with
      ⟨x, q, hq, heq⟩
    rcases hq with ⟨u, hu, rfl⟩
    exact ⟨x, u, hu, heq.symm⟩
  have hsurj : ∀ p : H, p ∈ U.range := by
    intro p
    choose x u hu hEq using fun n => hres n p
    have hxbounded : Bornology.IsBounded (Set.range x) := by
      apply Bornology.IsBounded.subset hdom
      rintro _ ⟨n, rfl⟩
      exact SetValuedOperator.mem_dom_iff U (x n) |>.2 ⟨u n, hu n⟩
    have hinv : Tendsto (fun n : ℕ => (c n)⁻¹) atTop (nhds 0) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have hadd : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 hnat
      exact tendsto_inv_atTop_zero.comp (by simpa [c] using hadd)
    have hcorr : Tendsto (fun n => (c n)⁻¹ • x n) atTop (nhds 0) := by
      rcases isBounded_iff_forall_norm_le.mp hxbounded with ⟨M, hM⟩
      have hbound (n : ℕ) : ‖(c n)⁻¹ • x n‖ ≤ (c n)⁻¹ * M := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hc n).le)]
        exact mul_le_mul_of_nonneg_left (hM _ (Set.mem_range_self n)) (inv_nonneg.mpr (hc n).le)
      have hright : Tendsto (fun n : ℕ => (c n)⁻¹ * M) atTop (nhds 0) := by
        simpa using hinv.mul_const M
      exact squeeze_zero_norm hbound hright
    have hu_formula (n : ℕ) : u n = p - (c n)⁻¹ • x n := by
      have hc0 : c n ≠ 0 := (hc n).ne'
      calc
        u n = (c n)⁻¹ • (c n • u n) := by simp [smul_smul, hc0]
        _ = (c n)⁻¹ • (c n • p - x n) := by rw [← hEq n]; abel
        _ = p - (c n)⁻¹ • x n := by
          rw [smul_sub, smul_smul, inv_mul_cancel₀ hc0]
          simp
    have hu0 : Tendsto (fun n => u n - p) atTop (nhds 0) := by
      have : (fun n => u n - p) = fun n => -((c n)⁻¹ • x n) := by
        funext n
        rw [hu_formula]
        abel
      rw [this]
      simpa using hcorr.neg
    rcases bounded_sequence_has_weakly_convergent_subsequence x hxbounded with
      ⟨xbar, phi, hphi, hxweak⟩
    let xs : ℕ → H := fun k => x (phi k)
    let us : ℕ → H := fun k => u (phi k)
    have hus0 : Tendsto (fun k => us k - p) atTop (nhds 0) := by
      simpa [us] using hu0.comp hphi.tendsto_atTop
    have hxsbounded : Bornology.IsBounded (Set.range xs) := by
      apply Bornology.IsBounded.subset hxbounded
      rintro _ ⟨k, rfl⟩
      exact ⟨phi k, rfl⟩
    have hrel : ∀ z w, w ∈ U z → 0 ≤ inner ℝ (p - w) (xbar - z) := by
      intro z w hw
      have h1 : Tendsto (fun k => inner ℝ (us k - p) (xs k)) atTop (nhds 0) :=
        inner_tendsto_zero_of_tendsto_zero_of_bounded hus0 hxsbounded
      have h2 : Tendsto (fun k => inner ℝ (us k - p) z) atTop (nhds 0) := by
        simpa using hus0.inner tendsto_const_nhds
      have h3 : Tendsto (fun k => inner ℝ w (xs k)) atTop (nhds (inner ℝ w xbar)) := by
        have hcont := (weakSpace_continuous_inner_right w).tendsto (toWeakSpace ℝ H xbar)
        simpa [xs, real_inner_comm] using hcont.comp hxweak
      have hp : Tendsto (fun k => inner ℝ p (xs k)) atTop (nhds (inner ℝ p xbar)) := by
        have hcont := (weakSpace_continuous_inner_right p).tendsto (toWeakSpace ℝ H xbar)
        simpa [xs, real_inner_comm] using hcont.comp hxweak
      have hlim : Tendsto (fun k => inner ℝ (us k - w) (xs k - z)) atTop
          (nhds (inner ℝ (p - w) (xbar - z))) := by
        have hpz : Tendsto (fun _ : ℕ => inner ℝ p z) atTop (nhds (inner ℝ p z)) :=
          tendsto_const_nhds
        have hwz : Tendsto (fun _ : ℕ => inner ℝ w z) atTop (nhds (inner ℝ w z)) :=
          tendsto_const_nhds
        have hsum := ((((h1.add hp).sub h2).sub hpz).sub h3).add hwz
        have hexpand : (fun k => inner ℝ (us k - w) (xs k - z)) =
            (fun k => inner ℝ (us k - p) (xs k) + inner ℝ p (xs k) -
              inner ℝ (us k - p) z - inner ℝ p z - inner ℝ w (xs k) + inner ℝ w z) := by
          funext k
          simp [inner_sub_left, inner_sub_right]
          ring
        rw [hexpand]
        convert hsum using 1 <;> simp [inner_sub_left, inner_sub_right] <;> ring
      have hnonneg : ∀ k, 0 ≤ inner ℝ (us k - w) (xs k - z) := by
        intro k
        exact hU.1 (us k) (by simpa [us] using hu (phi k)) w hw
      exact isClosed_Ici.mem_of_tendsto hlim (Filter.Eventually.of_forall hnonneg)
    have hpU : p ∈ U xbar := mem_of_monotonically_related_to_graph (T := U) hU hrel
    exact SetValuedOperator.mem_range_iff U p |>.2 ⟨xbar, hpU⟩
  constructor
  · exact Set.eq_univ_of_forall hsurj
  · rcases SetValuedOperator.mem_range_iff U (0 : H) |>.1 (hsurj 0) with ⟨x, hx⟩
    exact ⟨x, SetValuedOperator.mem_zeros_iff U x |>.2 hx⟩
```

## Proof explanation
The proof begins with `classical`, which allows classical choice and classical logic. It defines a sequence

$$
c_n = n+1
$$

and proves `hc : ∀ n, 0 < c n` by unfolding the definition and using `positivity`. Thus every $c_n$ is a positive real number.

The first main construction is `hres`, which asserts that for every $n\ge 0$ and every $p\in H$, there exist $x,u\in H$ such that

$$
u\in U x
\quad\text{and}\quad
x+c_n u=c_n p.
$$

This is obtained by applying Minty’s surjectivity theorem to the scaled operator

$$
T_n(x)=\{c_n u:u\in U x\}.
$$

The cited lemma `positive_scaled_maximal_monotone_local` states that if $U$ is maximal monotone and $c_n>0$, then the operator $x\mapsto c_n\cdot U x$ is again maximal monotone. Hence `minty_surjective_of_maximal_monotone` applies to $T_n$. That Minty theorem says that for a maximal monotone operator $T$ on $H$, for every $y\in H$ there exist $x$ and $q\in T x$ such that

$$
y=x+q.
$$

Taking $y=c_n p$, one obtains $x$ and $q\in T_n(x)$, so $q=c_n u$ for some $u\in U x$, and therefore

$$
c_n p=x+c_n u.
$$

The proof reverses this equality to obtain the form $x+c_n u=c_n p$.

Next, for a fixed $p$, the proof uses `choose` to select sequences $x_n$ and $u_n$ satisfying

$$
u_n\in U x_n
\quad\text{and}\quad
x_n+c_n u_n=c_n p.
$$

Because $u_n\in U x_n$, the set $U x_n$ is nonempty. The lemma `SetValuedOperator.mem_dom_iff` says that

$$
x\in U.\operatorname{dom}\iff U x\ne\varnothing.
$$

Therefore $x_n\in U.\operatorname{dom}$ for every $n$. Since $U.\operatorname{dom}$ is bounded, the range of the sequence $x_n$ is bounded. The proof records this as `hxbounded`.

The proof then shows that $c_n^{-1}\to 0$. Indeed, $(n:\mathbb R)\to\infty$, hence $(n:\mathbb R)+1\to\infty$, and therefore the reciprocal tends to $0$. This is `hinv`. Using the boundedness of the $x_n$, the proof writes $\|x_n\|\le M$ for all $n$. Then

$$
\|c_n^{-1}x_n\|=c_n^{-1}\|x_n\|\le c_n^{-1}M.
$$

Since $c_n^{-1}M\to 0$, the squeeze theorem for norms, invoked as `squeeze_zero_norm`, gives

$$
c_n^{-1}x_n\to 0
$$

strongly in $H$. This is `hcorr`.

From

$$
x_n+c_n u_n=c_n p
$$

and $c_n\ne 0$, the proof derives the algebraic formula

$$
u_n=p-c_n^{-1}x_n.
$$

Therefore

$$
u_n-p=-c_n^{-1}x_n\to 0.
$$

So the sequence of differences $u_n-p$ also tends strongly to $0$. This is `hu0`.

Now the proof extracts a weakly convergent subsequence of the bounded sequence $x_n$. The cited theorem `bounded_sequence_has_weakly_convergent_subsequence` says that if $x:\mathbb N\to H$ has bounded range, then there exist $\bar x\in H$ and a strictly increasing sequence $\varphi:\mathbb N\to\mathbb N$ such that

$$
x_{\varphi(k)}\rightharpoonup \bar x
$$

weakly, expressed in Lean as convergence of `toWeakSpace ℝ H (x (φ k))` to `toWeakSpace ℝ H xbar`. The proof defines

$$
xs_k=x_{\varphi(k)},\qquad us_k=u_{\varphi(k)}.
$$

Since $u_n-p\to 0$, also

$$
us_k-p\to 0.
$$

Since $xs$ is a subsequence of the bounded sequence $x$, its range is also bounded.

The core argument is to show that the pair $(\bar x,p)$ is monotonically related to the graph of $U$, namely that for every $z\in H$ and every $w\in U z$,

$$
0\le \langle p-w,\bar x-z\rangle.
$$

For each $k$, since $us_k\in U(xs_k)$ and $w\in U z$, monotonicity of $U$ gives

$$
0\le \langle us_k-w,xs_k-z\rangle.
$$

The proof then passes to the limit. It expands

$$
\langle us_k-w,xs_k-z\rangle
$$

as

$$
\langle us_k-p,xs_k\rangle+\langle p,xs_k\rangle
-\langle us_k-p,z\rangle-\langle p,z\rangle
-\langle w,xs_k\rangle+\langle w,z\rangle.
$$

The first term $\langle us_k-p,xs_k\rangle$ tends to $0$ because $us_k-p\to 0$ strongly and $xs_k$ is bounded. This is exactly the content of the cited lemma `inner_tendsto_zero_of_tendsto_zero_of_bounded`: if $a_n\to 0$ and the range of $b_n$ is bounded, then $\langle a_n,b_n\rangle\to 0$. The term $\langle us_k-p,z\rangle$ also tends to $0$, because the first factor tends to $0$ and the second factor is fixed.

The terms involving the weakly convergent subsequence are handled using `weakSpace_continuous_inner_right`. That lemma says that for fixed $y\in H$, the map on the weak space

$$
X\mapsto \left\langle ( \operatorname{toWeakSpace}_{\mathbb R}^H)^{-1}X, y\right\rangle
$$

is continuous. Therefore weak convergence $xs_k\rightharpoonup \bar x$ implies

$$
\langle xs_k,y\rangle\to \langle \bar x,y\rangle.
$$

Using real symmetry of the inner product, the proof obtains

$$
\langle w,xs_k\rangle\to \langle w,\bar x\rangle
\quad\text{and}\quad
\langle p,xs_k\rangle\to \langle p,\bar x\rangle.
$$

The constant terms $\langle p,z\rangle$ and $\langle w,z\rangle$ are fixed. Combining all limits gives

$$
\langle us_k-w,xs_k-z\rangle
\to
\langle p-w,\bar x-z\rangle.
$$

Since every term $\langle us_k-w,xs_k-z\rangle$ is nonnegative by monotonicity, and the set $[0,\infty)$ is closed, the limit is nonnegative. This is the use of `isClosed_Ici.mem_of_tendsto`: a limit of an eventually nonnegative sequence belongs to the closed set of nonnegative reals. Hence

$$
0\le \langle p-w,\bar x-z\rangle
$$

for every $z,w$ with $w\in U z$.

Now the maximality of $U$ is used. The cited lemma `mem_of_monotonically_related_to_graph` says that if $T$ is maximal monotone and a pair $(x,u)$ satisfies

$$
\forall y,v,\quad v\in T y\implies 0\le \langle u-v,x-y\rangle,
$$

then $u\in T x$. Applying this with $T=U$, $x=\bar x$, and $u=p$, the previously established inequality gives

$$
p\in U\bar x.
$$

Therefore $p$ belongs to the range of $U$, because `SetValuedOperator.mem_range_iff` states

$$
p\in U.\operatorname{range}\iff \exists x,\ p\in U x.
$$

Since $p\in H$ was arbitrary, `Set.eq_univ_of_forall` yields

$$
U.\operatorname{range}=\operatorname{Set.univ}.
$$

Finally, the proof establishes that the zero set is nonempty. Applying the already proved surjectivity to $p=0$ gives $0\in U.\operatorname{range}$. By `SetValuedOperator.mem_range_iff`, there exists $x\in H$ such that $0\in U x$. The final step uses `SetValuedOperator.mem_zeros_iff`, whose consequence in this context is that $x\in U.\operatorname{zeros}$ exactly when $0\in U x$. Hence there exists $x$ with $x\in U.\operatorname{zeros}$, so

$$
U.\operatorname{zeros}\ne\varnothing.
$$

This completes the proof of both conclusions. No `linarith` step occurs in this proof; the algebraic rearrangements are handled by `rw`, `simp`, `abel`, and `ring`, while `intro`, `rcases`, `choose`, `exact`, `simpa`, `constructor`, and `convert` manage the logical structure and term construction.

