## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/rem_1.lean`

## Lean statement
```lean
theorem finiteDimensional_finiteStopping_remark {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] (f phi : H → ℝ)
    (h gamma beta L r : ℝ) (_hdf : DF_r phi r)
    (alg : IPAHDD f phi.toEReal _hdf.toEReal_mem_gammaZero h gamma beta)
    (xInf : H) (hlimit : Filter.Tendsto alg.x Filter.atTop (nhds xInf))
    (hfinite : HasFiniteLength alg.x)
    (_hcritical : IsDryFrictionCritical phi f xInf)
    (_hL : HasLipschitzGradient (gradient f) L) (hf : ContDiff ℝ 1 f)
    (_hbelow : ∃ c : ℝ, ∀ x, c ≤ f x) (hpositive : 0 < h ∧ 0 < gamma ∧ 0 < beta)
    (_hgamma : gamma ≥ L * (h / 2 + beta))
    (hinterior : -gradient f xInf ∈ interior (subdifferential phi 0)) :
    ∃ N, ∀ k ≥ N, alg.x (k + 1) = alg.x k
```

## Statement explanation
`finiteDimensional_finiteStopping_remark` is a finite-stopping statement for an inertial proximal-gradient algorithm with dry friction and Hessian-driven damping. Let $H$ be a finite-dimensional real inner product space, let $f,\phi:H\to\mathbb R$, and let

$$
x_k:=\operatorname{alg.x} k
$$

be the iterates of the algorithm `alg`. The parameters $h,\gamma,\beta,L,r$ are real numbers. The hypothesis `_hdf : DF_r phi r` is a dry-friction condition depending on $r$; the proof uses its field `_hdf.toEReal_mem_gammaZero`, which says that the extended-real-valued function $\phi.toEReal$ belongs to $\Gamma_0(H)$. In the local definition, $\Gamma_0(H)$ consists of functions into `EReal` that are convex and lower semicontinuous. Thus this hypothesis gives the convexity and lower semicontinuity needed by the proximal subdifferential framework.

The subdifferential used here is, at a point $x$,

$$
\partial\phi(x)
=
\left\{u:H\;\middle|\;
\forall y:H,\;
\langle y-x,u\rangle_{\mathbb R}+\phi(x)\le \phi(y)
\right\},
$$

with the inequality interpreted after coercion to `EReal`. The hypothesis `hinterior` says

$$
-\nabla f(x_\infty)\in \operatorname{int}\bigl(\partial\phi(0)\bigr),
$$

so a full neighborhood of $-\nabla f(x_\infty)$ is contained in the subdifferential of $\phi$ at $0$.

The remaining hypotheses and their roles are:

- `hlimit` says $x_k\to x_\infty$ along the filter at infinity.
- `hfinite : HasFiniteLength alg.x` says the sequence of iterates has finite length; the proof uses the consequence that the increments tend to zero.
- `_hcritical : IsDryFrictionCritical phi f xInf` is present in the statement but is not used in the formal proof.
- `_hL : HasLipschitzGradient (gradient f) L` says $\nabla f$ has a Lipschitz-gradient property with constant $L$; it is present but not used in the proof.
- `hf : ContDiff ℝ 1 f` says $f$ is $C^1$. It is used through `continuous_gradient_of_contDiff` to obtain continuity of $\nabla f$.
- `_hbelow` says $f$ is bounded below.
- `hpositive` says $h>0$, $\gamma>0$, and $\beta>0$.
- `_hgamma` says $\gamma\ge L(h/2+\beta)$; it is present but not used in the proof.

The conclusion is that there exists an index $N$ such that for every $k\ge N$,

$$
x_{k+1}=x_k.
$$

In words, under the given finite-length and interior critical-point assumptions, the algorithm eventually becomes stationary in finite time.

## Lean proof
```lean
by
  let d : ℕ → H := fun k ↦ alg.x (k + 1) - alg.x k
  let v : ℕ → H := fun k ↦ (1 / h) • d k
  rcases hpositive with ⟨hh, hg, hb⟩
  have hC1 : Continuous (gradient f) := continuous_gradient_of_contDiff hf
  have hshift (k : ℕ) :
      ∃ q, q ∈ subdifferential phi (v (k + 1)) ∧
        (v (k + 1) - v k + gamma • d (k + 1) + h • q +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)) = 0) := by
    simpa [v, d, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      rem_1_shifted_recurrence f phi _hdf.toEReal_mem_gammaZero h gamma beta alg hh hg k
  have hd_norm : Filter.Tendsto (fun k => ‖d k‖) Filter.atTop (nhds 0) :=
    hfinite.tendsto_atTop_zero
  have hd : Filter.Tendsto d Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hd_norm
  have hd_succ : Filter.Tendsto (fun k => d (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hd.comp (Filter.tendsto_add_atTop_nat 1)
  have hv : Filter.Tendsto v Filter.atTop (nhds 0) := by
    simpa [v] using hd.const_smul (1 / h)
  have hv_succ : Filter.Tendsto (fun k => v (k + 1)) Filter.atTop (nhds 0) := by
    simpa using hv.comp (Filter.tendsto_add_atTop_nat 1)
  have hv_diff : Filter.Tendsto (fun k => v (k + 1) - v k) Filter.atTop (nhds 0) :=
    by simpa using hv_succ.sub hv
  have hx_succ : Filter.Tendsto (fun k => alg.x (k + 1)) Filter.atTop (nhds xInf) := by
    simpa using hlimit.comp (Filter.tendsto_add_atTop_nat 1)
  have hgrad : Filter.Tendsto (fun k => gradient f (alg.x k)) Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hlimit
  have hgrad_succ : Filter.Tendsto (fun k => gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (gradient f xInf)) :=
    (hC1.tendsto xInf).comp hx_succ
  have hgrad_diff : Filter.Tendsto
      (fun k => gradient f (alg.x (k + 1)) - gradient f (alg.x k)) Filter.atTop (nhds 0) :=
    by simpa using hgrad_succ.sub hgrad
  let q : ℕ → H := fun k => Classical.choose (hshift k)
  have hqmem (k : ℕ) : q k ∈ subdifferential phi (v (k + 1)) :=
    (Classical.choose_spec (hshift k)).1
  have hqrec (k : ℕ) :
      v (k + 1) - v k + gamma • d (k + 1) + h • q k +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
        h • gradient f (alg.x (k + 1)) = 0 :=
    (Classical.choose_spec (hshift k)).2
  have hqsolve (k : ℕ) :
      h • q k = -(v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
        h • gradient f (alg.x (k + 1))) := by
    apply eq_neg_of_add_eq_zero_left
    calc
      h • q k + (v (k + 1) - v k + gamma • d (k + 1) +
          beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1))) =
          v (k + 1) - v k + gamma • d (k + 1) + h • q k +
            beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
            h • gradient f (alg.x (k + 1)) := by ac_rfl
      _ = 0 := hqrec k
  have hdamp : Filter.Tendsto (fun k => gamma • d (k + 1)) Filter.atTop (nhds 0) :=
    by simpa using hd_succ.const_smul gamma
  have hbeta : Filter.Tendsto
      (fun k => beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k))) Filter.atTop (nhds 0) :=
    by simpa using hgrad_diff.const_smul beta
  have hgrad_term : Filter.Tendsto (fun k => h • gradient f (alg.x (k + 1)))
      Filter.atTop (nhds (h • gradient f xInf)) := hgrad_succ.const_smul h
  have hright : Filter.Tendsto (fun k =>
      -(v (k + 1) - v k + gamma • d (k + 1) +
        beta • (gradient f (alg.x (k + 1)) - gradient f (alg.x k)) +
          h • gradient f (alg.x (k + 1)))) Filter.atTop (nhds (-(h • gradient f xInf))) := by
    simpa using (((hv_diff.add hdamp).add hbeta).add hgrad_term).neg
  have hq_scaled : Filter.Tendsto (fun k => h • q k) Filter.atTop
      (nhds (h • (-gradient f xInf))) := by
    convert hright using 1
    · ext k
      rw [hqsolve]
    · simp
  have hq : Filter.Tendsto q Filter.atTop (nhds (-gradient f xInf)) := by
    have hq' := hq_scaled.const_smul (1 / h)
    have hqfun : (fun k => (1 / h) • (h • q k)) = q := by
      funext k
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    have hqlim : (1 / h) • (h • (-gradient f xInf)) = -gradient f xInf := by
      rw [smul_smul]
      field_simp [hh.ne']
      simp
    rw [hqfun, hqlim] at hq'
    exact hq'
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinterior) with ⟨ε, hε, hball⟩
  have hε2 : 0 < ε / 2 := by linarith
  have hq_tail : ∀ᶠ k in Filter.atTop, ‖q k - (-gradient f xInf)‖ < ε / 2 := by
    have := hq.eventually (Metric.ball_mem_nhds _ hε2)
    filter_upwards [this] with k hk
    simpa [Metric.mem_ball, dist_eq_norm] using hk
  rcases Filter.eventually_atTop.1 hq_tail with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro k hk
  have hkN : N ≤ k - 1 := Nat.le_sub_of_add_le hk
  have hkpos : 1 ≤ k := by omega
  have hkidx : (k - 1) + 1 = k := Nat.sub_add_cancel hkpos
  have hvzero : v ((k - 1) + 1) = 0 := by
    by_contra hvne
    let u : H := (‖v ((k - 1) + 1)‖)⁻¹ • v ((k - 1) + 1)
    let p : H := q (k - 1) + (ε / 2) • u
    have hvpos : 0 < ‖v ((k - 1) + 1)‖ := norm_pos_iff.mpr hvne
    have hunit : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvpos]
      field_simp [hvpos.ne']
    have hpball : p ∈ Metric.ball (-gradient f xInf) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc
        ‖p - (-gradient f xInf)‖ = ‖(q (k - 1) - (-gradient f xInf)) + (ε / 2) • u‖ := by
          dsimp [p]
          abel_nf
        _ ≤ ‖q (k - 1) - (-gradient f xInf)‖ + ‖(ε / 2) • u‖ := norm_add_le _ _
        _ = ‖q (k - 1) - (-gradient f xInf)‖ + (ε / 2) * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε2]
        _ < ε := by rw [hunit]; linarith [hN (k - 1) hkN]
    have hp : p ∈ subdifferential phi 0 := hball hpball
    have hqineq := hqmem (k - 1) 0
    have hpineq := hp (v ((k - 1) + 1))
    have hmono : 0 ≤ inner ℝ (q (k - 1) - p) (v ((k - 1) + 1)) := by
      change (⟪v ((k - 1) + 1) - 0, p⟫_ℝ : EReal) + (phi 0 : EReal) ≤
        (phi (v ((k - 1) + 1)) : EReal) at hpineq
      change (⟪0 - v ((k - 1) + 1), q (k - 1)⟫_ℝ : EReal) +
          (phi (v ((k - 1) + 1)) : EReal) ≤ (phi 0 : EReal) at hqineq
      norm_cast at hpineq hqineq
      rw [sub_zero, real_inner_comm] at hpineq
      rw [zero_sub, inner_neg_left, real_inner_comm] at hqineq
      rw [inner_sub_left]
      linarith
    have hinner : inner ℝ (q (k - 1) - p) (v ((k - 1) + 1)) =
        -((ε / 2) * ‖v ((k - 1) + 1)‖) := by
      dsimp [p, u]
      have hsub : q (k - 1) -
          (q (k - 1) + (ε / 2) • (‖v ((k - 1) + 1)‖)⁻¹ • v ((k - 1) + 1)) =
          -((ε / 2) • (‖v ((k - 1) + 1)‖)⁻¹ • v ((k - 1) + 1)) := by
        abel
      rw [hsub, inner_neg_left, inner_smul_left, inner_smul_left,
        real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hvpos.ne']
    rw [hinner] at hmono
    nlinarith
  have hvzero' : (1 / h) • (alg.x (k + 1) - alg.x k) = 0 := by
    simpa [v, d, hkidx] using hvzero
  have hdzero : alg.x (k + 1) - alg.x k = 0 :=
    (smul_eq_zero.mp hvzero').resolve_left (one_div_ne_zero hh.ne')
  exact sub_eq_zero.mp hdzero
```

## Proof explanation
The proof proceeds by analyzing the increments and velocities of the iterates.

1. The proof defines

$$
d_k:=x_{k+1}-x_k,\qquad v_k:=\frac1h d_k=\frac1h(x_{k+1}-x_k).
$$

It also destructures `hpositive` into $h>0$, $\gamma>0$, and $\beta>0$. From `hf : ContDiff ℝ 1 f`, the cited result `continuous_gradient_of_contDiff` gives continuity of the gradient:

$$
\nabla f \text{ is continuous}.
$$

2. For each $k$, the proof invokes `rem_1_shifted_recurrence`. That theorem states that if $\phi.toEReal\in\Gamma_0(H)$, $h>0$, $\gamma>0$, and `alg` is the corresponding `IPAHDD`, then for every $k$ there exists $q$ such that

$$
q\in\partial\phi\!\left(\frac1h(x_{k+2}-x_{k+1})\right)
$$

and

$$
\frac1h(x_{k+2}-x_{k+1})
-\frac1h(x_{k+1}-x_k)
+\gamma(x_{k+2}-x_{k+1})
+h q
+\beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
+h\nabla f(x_{k+1})=0.
$$

In the proof this is rewritten using $d_k$ and $v_k$. Since $v_{k+1}=\frac1h(x_{k+2}-x_{k+1})$ and $d_{k+1}=x_{k+2}-x_{k+1}$, the recurrence becomes

$$
v_{k+1}-v_k+\gamma d_{k+1}+h q_k
+\beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
+h\nabla f(x_{k+1})=0.
$$

The proof supplies `_hdf.toEReal_mem_gammaZero` as the required $\Gamma_0$ membership, and uses $h>0$, $\gamma>0$. The `simpa` step only rewrites indices and definitions.

3. From `hfinite.tendsto_atTop_zero`, the finite-length hypothesis gives

$$
\|d_k\|\to0.
$$

Using `tendsto_zero_iff_norm_tendsto_zero.mpr`, the proof converts this into

$$
d_k\to0.
$$

Shifting by one, `Filter.tendsto_add_atTop_nat 1` gives

$$
d_{k+1}\to0.
$$

Since $v_k=(1/h)d_k$, scalar multiplication by $1/h$ gives

$$
v_k\to0,\qquad v_{k+1}\to0,
$$

and subtracting the two limits gives

$$
v_{k+1}-v_k\to0.
$$

4. The hypothesis $x_k\to x_\infty$ and continuity of $\nabla f$ give

$$
\nabla f(x_k)\to \nabla f(x_\infty),
\qquad
\nabla f(x_{k+1})\to \nabla f(x_\infty).
$$

Subtracting yields

$$
\nabla f(x_{k+1})-\nabla f(x_k)\to0.
$$

The terms $\gamma d_{k+1}$ and $\beta(\nabla f(x_{k+1})-\nabla f(x_k))$ therefore also tend to $0$. The term $h\nabla f(x_{k+1})$ tends to $h\nabla f(x_\infty)$.

5. The proof chooses $q_k$ for each $k$ using `Classical.choose` applied to the above recurrence. From the recurrence,

$$
h q_k
=
-\left(
v_{k+1}-v_k+\gamma d_{k+1}
+\beta\bigl(\nabla f(x_{k+1})-\nabla f(x_k)\bigr)
+h\nabla f(x_{k+1})
\right).
$$

This is obtained by `eq_neg_of_add_eq_zero_left`; the auxiliary `ac_rfl` calculation only rearranges the summands to match the recurrence. Passing to the limit in this identity, the right-hand side tends to

$$
-h\nabla f(x_\infty).
$$

Hence

$$
h q_k\to h\bigl(-\nabla f(x_\infty)\bigr).
$$

Because $h>0$, scaling by $1/h$ gives

$$
q_k\to -\nabla f(x_\infty).
$$

6. The interior hypothesis says

$$
-\nabla f(x_\infty)\in\operatorname{int}\bigl(\partial\phi(0)\bigr).
$$

Using `mem_interior_iff_mem_nhds` and `Metric.mem_nhds_iff`, the proof extracts an $\varepsilon>0$ such that the open ball

$$
B\bigl(-\nabla f(x_\infty),\varepsilon\bigr)
$$

is contained in $\partial\phi(0)$. Since $q_k\to -\nabla f(x_\infty)$, eventually

$$
\|q_k-(-\nabla f(x_\infty))\|<\frac\varepsilon2.
$$

The proof chooses $N$ such that this holds for all $k\ge N$.

7. Now fix $k\ge N+1$. The proof argues by contradiction and assumes

$$
v_{k-1+1}=v_k\ne0.
$$

Let

$$
u:=\frac{1}{\|v_k\|}v_k,
$$

so $\|u\|=1$, and define

$$
p:=q_{k-1}+\frac\varepsilon2 u.
$$

Because $k-1\ge N$, the chosen $N$ gives

$$
\|q_{k-1}-(-\nabla f(x_\infty))\|<\frac\varepsilon2.
$$

Therefore

$$
\|p-(-\nabla f(x_\infty))\|
\le
\|q_{k-1}-(-\nabla f(x_\infty))\|+\frac\varepsilon2\|u\|
<
\frac\varepsilon2+\frac\varepsilon2
=\varepsilon.
$$

Thus $p\in B(-\nabla f(x_\infty),\varepsilon)$, and since this ball is contained in $\partial\phi(0)$, we get

$$
p\in\partial\phi(0).
$$

Also, from the construction of $q_{k-1}$,

$$
q_{k-1}\in\partial\phi(v_k).
$$

8. The two subdifferential memberships give two inequalities. Since $q_{k-1}\in\partial\phi(v_k)$, testing against $0$ yields

$$
\langle -v_k,q_{k-1}\rangle+\phi(v_k)\le\phi(0).
$$

Since $p\in\partial\phi(0)$, testing against $v_k$ yields

$$
\langle v_k,p\rangle+\phi(0)\le\phi(v_k).
$$

Combining these inequalities cancels $\phi(v_k)$ and $\phi(0)$, giving the monotonicity-type inequality

$$
0\le \langle q_{k-1}-p,v_k\rangle.
$$

In the proof, `norm_cast`, `real_inner_comm`, `inner_neg_left`, `inner_sub_left`, and `linarith` are used to convert the `EReal` inequalities into this real inner-product inequality.

On the other hand, by definition of $p$,

$$
q_{k-1}-p=-\frac\varepsilon2 u
=-\frac\varepsilon2\frac{1}{\|v_k\|}v_k.
$$

Therefore

$$
\langle q_{k-1}-p,v_k\rangle
=
-\frac\varepsilon2\|v_k\|.
$$

Since $\varepsilon>0$ and $v_k\ne0$, the right-hand side is strictly negative, contradicting

$$
0\le \langle q_{k-1}-p,v_k\rangle.
$$

Thus the assumption $v_k\ne0$ is impossible, so

$$
v_k=0.
$$

In terms of the original increments,

$$
\frac1h(x_{k+1}-x_k)=0.
$$

Since $h\ne0$, `smul_eq_zero.mp` gives

$$
x_{k+1}-x_k=0,
$$

and hence

$$
x_{k+1}=x_k.
$$

9. The index $k\ge N+1$ was arbitrary. Therefore the proof returns the witness $N+1$ and concludes

$$
\exists N,\ \forall k\ge N,\ x_{k+1}=x_k.
$$

This is exactly finite stopping: after some finite index, all successive iterates are equal.

