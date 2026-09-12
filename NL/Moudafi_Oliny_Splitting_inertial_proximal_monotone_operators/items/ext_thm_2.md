## Source file
`Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators/items/ext_thm_2.lean`

## Lean statement
```lean
theorem demiclosed_weak_x_strong_u {T : SetValuedOperator H H}
    (hT_mono : IsMonotone T)
    {x : ℕ → H} {u : ℕ → H} {ε : ℕ → ℝ} {x0 u0 : H} {ε0 : ℝ}
    (hx : Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H x0)))
    (hu : Tendsto u atTop (𝓝 u0))
    (hε : Tendsto ε atTop (𝓝 ε0))
    (h : ∀ k, u k ∈ enlargement T (ε k) (x k)) :
    u0 ∈ enlargement T ε0 x0
```

## Statement explanation
The declaration `demiclosed_weak_x_strong_u` is a closure or demiclosedness statement for the enlargement of a set-valued operator. Let $H$ be the underlying real Hilbert space, with inner product $\langle \cdot,\cdot\rangle_{\mathbb R}$, norm $\|\cdot\|$, and weak topology represented by `WeakSpace ℝ H`. A set-valued operator $T:H\to \mathcal P(H)$ is a function assigning to each $x\in H$ a subset $T(x)\subseteq H$. The hypothesis `hT_mono` says that $T$ is monotone, although this hypothesis is not used in the proof below.

For a real number $\epsilon$ and point $x\in H$, the enlargement $\operatorname{enlargement}(T,\epsilon)(x)$, written here as $T_\epsilon(x)$, is defined by

$$
T_\epsilon(x)
=
\left\{
v\in H
\;\middle|\;
\forall y\in H,\ \forall w\in T(y),\
-\epsilon\le \langle w-v,\,y-x\rangle_{\mathbb R}
\right\}.
$$

Thus $T_\epsilon(x)$ is the set of all $v$ such that the displayed inner-product inequality holds against every pair $y$ and $w\in T(y)$.

The theorem has two sequences $x:\mathbb N\to H$ and $u:\mathbb N\to H$, a real sequence $\epsilon:\mathbb N\to\mathbb R$, and limits $x_0,u_0\in H$ and $\epsilon_0\in\mathbb R$. The hypotheses are:

- `hx`: the sequence $x_k$ converges weakly to $x_0$, formalized as convergence of `toWeakSpace ℝ H (x k)` to `toWeakSpace ℝ H x0` in the weak topology.
- `hu`: the sequence $u_k$ converges strongly, i.e. in norm, to $u_0$.
- `hε`: the real sequence $\epsilon_k$ converges to $\epsilon_0$.
- `h`: for every $k$, $u_k\in T_{\epsilon_k}(x_k)$. Explicitly, for every $k$, every $y\in H$, and every $w\in T(y)$,

$$
-\epsilon_k\le \langle w-u_k,\,y-x_k\rangle_{\mathbb R}.
$$

The conclusion is

$$
u_0\in T_{\epsilon_0}(x_0),
$$

which means that for every $y\in H$ and every $w\in T(y)$,

$$
-\epsilon_0\le \langle w-u_0,\,y-x_0\rangle_{\mathbb R}.
$$

In ordinary language, the theorem says that the enlargement operation is closed under the mixed convergence mode of weak convergence in the $x$-variable, strong convergence in the $u$-variable, and ordinary convergence of the parameters $\epsilon_k$. If each $u_k$ is an $\epsilon_k$-enlarged point at $x_k$, then the strong limit $u_0$ is an $\epsilon_0$-enlarged point at the weak limit $x_0$. The monotonicity assumption `hT_mono` is part of the statement but is never invoked by the supplied proof.

## Lean proof
```lean
by
  rw [enlargement, Set.mem_setOf_eq]
  intro y v hv
  -- From `h`, for each k we have `-ε k ≤ ⟪v - u k, y - x k⟫_ℝ` = `⟪x k - y, u k - v⟫_ℝ`
  have h_eps_le : ∀ k, -ε k ≤ ⟪x k - y, u k - v⟫_ℝ := by
    intro k
    have hk := h k
    rw [enlargement, Set.mem_setOf_eq] at hk
    have hk' := hk y v hv
    -- hk' : -ε k ≤ ⟪v - u k, y - x k⟫_ℝ
    -- Rewrite: ⟪v - u k, y - x k⟫_ℝ = ⟪x k - y, u k - v⟫_ℝ
    have h_eq : ⟪v - u k, y - x k⟫_ℝ = ⟪x k - y, u k - v⟫_ℝ := by
      simp [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    simpa [h_eq] using hk'
  -- Boundedness of {x_k} and {u_k} from convergence
  have hx_bdd : Bornology.IsBounded (Set.range x) :=
    bounded_range_of_tendsto_weakly hx
  have hu_bdd : Bornology.IsBounded (Set.range u) :=
    Metric.isBounded_range_of_tendsto _ hu
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨Mx, hMx⟩
  rcases isBounded_iff_forall_norm_le.mp hu_bdd with ⟨_, hMu⟩
  -- Bound for ‖x k - x0‖
  have hMx_bound : ∀ k, ‖x k - x0‖ ≤ Mx + ‖x0‖ := by
    intro k
    calc
      ‖x k - x0‖ ≤ ‖x k‖ + ‖x0‖ := norm_sub_le _ _
      _ ≤ Mx + ‖x0‖ := by
        gcongr
        exact hMx (x k) (Set.mem_range_self k)
  -- Decompose the inner product as in the paper proof
  have h_decomp : ∀ k, ⟪x k - y, u k - v⟫_ℝ =
      ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by
    intro k
    calc
      ⟪x k - y, u k - v⟫_ℝ
          = ⟪x k - y, (u k - u0) + (u0 - v)⟫_ℝ := by simp [sub_add_sub_cancel]
      _ = ⟪x k - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by rw [inner_add_right]
      _ = ⟪(x k - x0) + (x0 - y), u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by
        simp [sub_add_sub_cancel]
      _ = (⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ) + ⟪x k - y, u0 - v⟫_ℝ := by
        rw [inner_add_left]
      _ = ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by ring
  -- Limit of ⟪x k - x0, u k - u0⟫_ℝ → 0: Cauchy-Schwarz + strong convergence of u_k
  have hlim1 : Tendsto (fun k : ℕ => ⟪x k - x0, u k - u0⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have hu_norm_tendsto : Tendsto (fun k : ℕ => ‖u k - u0‖) atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => u k - u0) atTop (𝓝 0) := by
        simpa using hu.sub_const u0
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mp this)
    have hbound : ∀ k, ‖⟪x k - x0, u k - u0⟫_ℝ‖ ≤ (Mx + ‖x0‖) * ‖u k - u0‖ := by
      intro k
      calc
        ‖⟪x k - x0, u k - u0⟫_ℝ‖ = |⟪x k - x0, u k - u0⟫_ℝ| := by rw [Real.norm_eq_abs]
        _ ≤ ‖x k - x0‖ * ‖u k - u0‖ := abs_real_inner_le_norm _ _
        _ ≤ (Mx + ‖x0‖) * ‖u k - u0‖ := by gcongr; exact hMx_bound k
    have h_prod_tendsto : Tendsto (fun k : ℕ => (Mx + ‖x0‖) * ‖u k - u0‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using hu_norm_tendsto.const_mul (Mx + ‖x0‖)
    refine squeeze_zero_norm hbound h_prod_tendsto
  -- Limit of ⟪x0 - y, u k - u0⟫_ℝ → 0: strong convergence of u_k
  have hlim2 : Tendsto (fun k : ℕ => ⟪x0 - y, u k - u0⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have h_inner : Tendsto (fun k : ℕ => ⟪x0 - y, u k⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0⟫_ℝ) :=
      Filter.Tendsto.inner (tendsto_const_nhds (x := x0 - y)) hu
    have h_eq : (fun k : ℕ => ⟪x0 - y, u k - u0⟫_ℝ) =
        (fun k : ℕ => ⟪x0 - y, u k⟫_ℝ - ⟪x0 - y, u0⟫_ℝ) := by
      ext k; simp [inner_sub_right]
    rw [h_eq]
    simpa using h_inner.sub_const ⟪x0 - y, u0⟫_ℝ
  -- Limit of ⟪x k - y, u0 - v⟫_ℝ → ⟪x0 - y, u0 - v⟫_ℝ: weak convergence of x_k
  have hlim3 : Tendsto (fun k : ℕ => ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
    have h_inner_temp : Tendsto (fun k : ℕ => ⟪x k, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0, u0 - v⟫_ℝ) := by
      simpa using (weakSpace_continuous_inner_right (u0 - v)).tendsto
        (toWeakSpace ℝ H x0) |>.comp hx
    have h_inner : Tendsto (fun k : ℕ => ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
      simpa [inner_sub_left] using h_inner_temp.sub_const ⟪y, u0 - v⟫_ℝ
    exact h_inner
  -- Combine the three limits
  have hlim_sum : Tendsto (fun k : ℕ => ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ +
      ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 (⟪x0 - y, u0 - v⟫_ℝ)) := by
    simpa [add_assoc] using hlim1.add (hlim2.add hlim3)
  have hlim : Tendsto (fun k : ℕ => ⟪x k - y, u k - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
    simpa [h_decomp] using hlim_sum
  have heps_lim : Tendsto (fun k : ℕ => -ε k) atTop (𝓝 (-ε0)) :=
    hε.neg
  -- Pass the inequality -ε k ≤ ⟪x k - y, u k - v⟫_ℝ through the limit
  have h_ineq : -ε0 ≤ ⟪x0 - y, u0 - v⟫_ℝ := by
    have h_eventually : (fun k : ℕ => -ε k) ≤ᶠ[atTop] (fun k : ℕ => ⟪x k - y, u k - v⟫_ℝ) :=
      Filter.Eventually.of_forall h_eps_le
    exact le_of_tendsto_of_tendsto heps_lim hlim h_eventually
  -- Convert back: ⟪x0 - y, u0 - v⟫_ℝ = ⟪v - u0, y - x0⟫_ℝ
  have h_final_eq : ⟪x0 - y, u0 - v⟫_ℝ = ⟪v - u0, y - x0⟫_ℝ := by
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  simpa [h_final_eq] using h_ineq
```

## Proof explanation
The proof is a direct limiting argument. It fixes an arbitrary testing pair $y\in H$ and $w\in T(y)$, extracts the enlargement inequality for each $k$, rewrites it in a convenient algebraic form, shows that the right-hand side converges to the corresponding expression for $x_0,u_0,\epsilon_0$, and then passes the inequality to the limit.

1. Unfolding the target. The proof begins with
```lean
rw [enlargement, Set.mem_setOf_eq]
intro y v hv
```
The rewrite unfolds the definition of `enlargement` and replaces membership in a set-builder by the corresponding predicate. The goal becomes: for every $y\in H$ and every $v\in T(y)$,

$$
-\epsilon_0\le \langle v-u_0,\,y-x_0\rangle_{\mathbb R}.
$$

The command `intro y v hv` fixes arbitrary $y$ and $v\in T(y)$, leaving the inequality above as the goal. Here the proof’s variable `v` plays the role of the arbitrary element $w\in T(y)$ in the definition of enlargement.

2. Extracting the inequalities for each $k$. The proof establishes
```lean
have h_eps_le : ∀ k, -ε k ≤ ⟪x k - y, u k - v⟫_ℝ
```
For a fixed $k$, the hypothesis `h k` says $u_k\in T_{\epsilon_k}(x_k)$. Unfolding `enlargement` and applying it to the fixed $y$ and $v\in T(y)$ gives

$$
-\epsilon_k\le \langle v-u_k,\,y-x_k\rangle_{\mathbb R}.
$$

The proof then rewrites the inner product by the identity

$$
\langle v-u_k,\,y-x_k\rangle_{\mathbb R}
=
\langle x_k-y,\,u_k-v\rangle_{\mathbb R}.
$$

This is purely algebraic: it uses bilinearity of the inner product, the identities `inner_sub_left`, `inner_sub_right`, and real symmetry `real_inner_comm`, followed by `ring`. Thus for every $k$,

$$
-\epsilon_k\le \langle x_k-y,\,u_k-v\rangle_{\mathbb R}.
$$

This is the form that will be compared with the limit.

3. Boundedness of the ranges. The proof then invokes two boundedness facts. First,
```lean
have hx_bdd : Bornology.IsBounded (Set.range x) :=
  bounded_range_of_tendsto_weakly hx
```
The cited lemma `bounded_range_of_tendsto_weakly` says that if a sequence converges weakly, then the set of its values is bounded in norm. Specialized here, weak convergence of $x_k$ to $x_0$ implies that $\{x_k:k\in\mathbb N\}$ is bounded. Second,
```lean
have hu_bdd : Bornology.IsBounded (Set.range u) :=
  Metric.isBounded_range_of_tendsto _ hu
```
The theorem `Metric.isBounded_range_of_tendsto` says that a convergent sequence in a metric space has bounded range. Here strong convergence $u_k\to u_0$ implies that $\{u_k:k\in\mathbb N\}$ is bounded.

The proof then uses `isBounded_iff_forall_norm_le.mp` to extract a real bound $M_x$ such that

$$
\|x_k\|\le M_x
$$

for every $k$, via membership of $x_k$ in `Set.range x`. It also extracts a bound for the $u_k$, but that bound is not used later.

From the bound on $\|x_k\|$, the proof proves
```lean
have hMx_bound : ∀ k, ‖x k - x0‖ ≤ Mx + ‖x0‖
```
Indeed, for each $k$,

$$
\|x_k-x_0\|\le \|x_k\|+\|x_0\|\le M_x+\|x_0\|.
$$

The first inequality is the triangle inequality `norm_sub_le`; the second is obtained from $\|x_k\|\le M_x$ by `gcongr`. This bound will control the term $\langle x_k-x_0,u_k-u_0\rangle$.

4. Decomposing the inner product. The proof establishes

$$
\langle x_k-y,\,u_k-v\rangle_{\mathbb R}
=
\langle x_k-x_0,\,u_k-u_0\rangle_{\mathbb R}
+\langle x_0-y,\,u_k-u_0\rangle_{\mathbb R}
+\langle x_k-y,\,u_0-v\rangle_{\mathbb R}.
$$

This is proved by writing

$$
u_k-v=(u_k-u_0)+(u_0-v),
\qquad
x_k-y=(x_k-x_0)+(x_0-y),
$$

and expanding using additivity of the inner product in each argument. The Lean steps use `inner_add_right`, `inner_add_left`, `simp`, and `ring`. The point of this decomposition is to separate the expression into one term controlled by strong convergence of $u_k$, one term controlled only by strong convergence of $u_k$, and one term controlled by weak convergence of $x_k$.

5. The first term tends to zero. The proof shows

$$
\langle x_k-x_0,\,u_k-u_0\rangle_{\mathbb R}\to 0.
$$

Since $u_k\to u_0$ strongly, the sequence $u_k-u_0$ tends to $0$. The proof converts this to

$$
\|u_k-u_0\|\to 0
$$

using `tendsto_zero_iff_norm_tendsto_zero`. Then Cauchy–Schwarz, named `abs_real_inner_le_norm`, gives

$$
\left|\langle x_k-x_0,u_k-u_0\rangle_{\mathbb R}\right|
\le \|x_k-x_0\|\,\|u_k-u_0\|.
$$

Using the earlier bound $\|x_k-x_0\|\le M_x+\|x_0\|$, the proof obtains

$$
\left|\langle x_k-x_0,u_k-u_0\rangle_{\mathbb R}\right|
\le (M_x+\|x_0\|)\,\|u_k-u_0\|.
$$

The right-hand side tends to $0$. The theorem `squeeze_zero_norm` then gives that the original inner-product sequence tends to $0$. Thus the first summand vanishes in the limit.

6. The second term tends to zero. The proof shows

$$
\langle x_0-y,\,u_k-u_0\rangle_{\mathbb R}\to 0.
$$

This uses continuity of the inner product in its second argument together with strong convergence $u_k\to u_0$. Explicitly, `Filter.Tendsto.inner` gives

$$
\langle x_0-y,u_k\rangle_{\mathbb R}\to \langle x_0-y,u_0\rangle_{\mathbb R}.
$$

Subtracting the constant $\langle x_0-y,u_0\rangle_{\mathbb R}$, and using

$$
\langle x_0-y,u_k-u_0\rangle_{\mathbb R}
=
\langle x_0-y,u_k\rangle_{\mathbb R}
-\langle x_0-y,u_0\rangle_{\mathbb R},
$$

yields convergence to $0$. Hence the second summand also vanishes in the limit.

7. The third term converges to the target value. The proof shows

$$
\langle x_k-y,\,u_0-v\rangle_{\mathbb R}
\to
\langle x_0-y,\,u_0-v\rangle_{\mathbb R}.
$$

This is where weak convergence of $x_k$ is used. The cited theorem `weakSpace_continuous_inner_right` states that for a fixed vector $z\in H$, the map

$$
w\mapsto \left\langle (toWeakSpace\ \mathbb R\ H)^{-1}(w),\,z\right\rangle_{\mathbb R}
$$

is continuous on the weak space. Taking $z=u_0-v$, and composing this continuity with the weak convergence $toWeakSpace(x_k)\to toWeakSpace(x_0)$, gives

$$
\langle x_k,u_0-v\rangle_{\mathbb R}
\to
\langle x_0,u_0-v\rangle_{\mathbb R}.
$$

Then subtracting the constant $\langle y,u_0-v\rangle_{\mathbb R}$ and using bilinearity gives the desired convergence of $\langle x_k-y,u_0-v\rangle_{\mathbb R}$.

8. Combining the three limits. The proof adds the three convergences. Since the first two terms tend to $0$ and the third tends to $\langle x_0-y,u_0-v\rangle_{\mathbb R}$, the sum tends to that value:

$$
\langle x_k-x_0,u_k-u_0\rangle_{\mathbb R}
+\langle x_0-y,u_k-u_0\rangle_{\mathbb R}
+\langle x_k-y,u_0-v\rangle_{\mathbb R}
\to
\langle x_0-y,u_0-v\rangle_{\mathbb R}.
$$

Using the decomposition from step 4, the proof concludes

$$
\langle x_k-y,u_k-v\rangle_{\mathbb R}
\to
\langle x_0-y,u_0-v\rangle_{\mathbb R}.
$$

9. Passing the inequality to the limit. From step 2, for every $k$,

$$
-\epsilon_k\le \langle x_k-y,u_k-v\rangle_{\mathbb R}.
$$

Also, $\epsilon_k\to\epsilon_0$ implies $-\epsilon_k\to-\epsilon_0$. The proof therefore has two convergent sequences, with the first eventually bounded above by the second:

$$
-\epsilon_k\le \langle x_k-y,u_k-v\rangle_{\mathbb R}
\quad\text{for all }k.
$$

The theorem `le_of_tendsto_of_tendsto` then yields

$$
-\epsilon_0\le \langle x_0-y,u_0-v\rangle_{\mathbb R}.
$$

This is the key limiting step that transfers the enlargement inequality from the sequence to its limit.

10. Final algebra and conclusion. The proof rewrites

$$
\langle x_0-y,u_0-v\rangle_{\mathbb R}
=
\langle v-u_0,y-x_0\rangle_{\mathbb R}.
$$

Again this uses bilinearity and real symmetry of the inner product, followed by `ring`. Therefore the previous inequality becomes

$$
-\epsilon_0\le \langle v-u_0,y-x_0\rangle_{\mathbb R}.
$$

Since $y\in H$ and $v\in T(y)$ were arbitrary, this is exactly the defining inequality for

$$
u_0\in T_{\epsilon_0}(x_0).
$$

Thus the theorem is proved.

Throughout the proof, the monotonicity hypothesis `hT_mono` is never used. The argument only uses the definition of the enlargement, boundedness of weakly convergent and strongly convergent sequences, Cauchy–Schwarz, continuity of the inner product, and the fact that weak convergence implies convergence of inner products against fixed vectors.

