## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/ext_thm_2.lean`

## Lean statement
```lean
theorem opial_lemma_paper {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (x : ℕ → H) (xLimit z : H)
    (hx : Tendsto (fun j ↦ toWeakSpace ℝ H (x j)) Filter.atTop
      (nhds (toWeakSpace ℝ H xLimit))) (hz : z ≠ xLimit) :
    Filter.liminf (fun j ↦ ‖x j - z‖) Filter.atTop >
      Filter.liminf (fun j ↦ ‖x j - xLimit‖) Filter.atTop
```

## Statement explanation
The theorem `opial_lemma_paper` is stated for a real Hilbert space, encoded as a type $H$ with a real inner product, a normed additive group structure, and completeness. It takes a sequence $x:\mathbb N\to H$, a point $x_{\text{Limit}}\in H$, and another point $z\in H$. The hypothesis $hx$ says that the canonical images of $x_j$ in the weak space converge to the image of $x_{\text{Limit}}$. In ordinary mathematical language this is weak convergence:

$$
x_j \rightharpoonup x_{\text{Limit}}.
$$

The hypothesis $hz$ says $z\neq x_{\text{Limit}}$. The conclusion is the strict liminf inequality

$$
\liminf_{j\to\infty}\|x_j-z\|
>
\liminf_{j\to\infty}\|x_j-x_{\text{Limit}}\|.
$$

Thus, if a sequence converges weakly to $x_{\text{Limit}}$, then every different point $z$ has a strictly larger lower limit of distances to the sequence than the weak limit has. This is exactly the Opial property of Hilbert spaces.

## Lean proof
```lean
by
  let r : ℕ → ℝ := fun j ↦ ‖x j - xLimit‖
  let s : ℕ → ℝ := fun j ↦ ‖x j - z‖
  let q : ℕ → ℝ := fun j ↦ r j ^ 2
  let d : H := xLimit - z
  have hx_bdd : Bornology.IsBounded (Set.range x) :=
    bounded_range_of_tendsto_weakly hx
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨R, hR⟩
  have hr_nonneg : ∀ j, 0 ≤ r j := fun j ↦ norm_nonneg _
  have hs_nonneg : ∀ j, 0 ≤ s j := fun j ↦ norm_nonneg _
  have hr_upper : ∀ j, r j ≤ R + ‖xLimit‖ := by
    intro j
    dsimp [r]
    exact (norm_sub_le _ _).trans (by
      simpa [add_comm] using add_le_add_left (hR _ (Set.mem_range_self j)) ‖xLimit‖)
  have hs_upper : ∀ j, s j ≤ R + ‖z‖ := by
    intro j
    dsimp [s]
    exact (norm_sub_le _ _).trans (by
      simpa [add_comm] using add_le_add_left (hR _ (Set.mem_range_self j)) ‖z‖)
  have hr_bddbelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop r :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hr_nonneg)
  have hs_bddbelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop s :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hs_nonneg)
  have hr_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop r :=
    isCoboundedUnder_ge_of_le Filter.atTop hr_upper
  have hs_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop s :=
    isCoboundedUnder_ge_of_le Filter.atTop hs_upper
  have hlim_r_nonneg : 0 ≤ Filter.liminf r Filter.atTop :=
    Filter.le_liminf_of_le hr_cobdd (Filter.Eventually.of_forall hr_nonneg)
  let g : ℝ → ℝ := fun t ↦ max t 0 ^ 2
  have hg_mono : Monotone g := by
    intro a b hab
    dsimp [g]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ hab) 2
  have hg_cont : ContinuousAt g (Filter.liminf r Filter.atTop) :=
    ((continuousAt_id.max continuousAt_const).pow 2)
  have hq_eq : Filter.liminf q Filter.atTop = (Filter.liminf r Filter.atTop) ^ 2 := by
    have hmap := hg_mono.map_liminf_of_continuousAt r hg_cont hr_cobdd hr_bddbelow
    rw [show g (Filter.liminf r Filter.atTop) = (Filter.liminf r Filter.atTop) ^ 2 by
      simp [g, hlim_r_nonneg], show g ∘ r = q by
      funext j
      simp [g, q, hr_nonneg j]] at hmap
    exact hmap.symm
  have hq_nonneg : ∀ j, 0 ≤ q j := by
    intro j
    dsimp [q]
    positivity
  have hq_bddbelow : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop q :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hq_nonneg)
  have hB_nonneg : 0 ≤ R + ‖xLimit‖ :=
    (hr_nonneg 0).trans (hr_upper 0)
  have hq_upper : ∀ j, q j ≤ (R + ‖xLimit‖) ^ 2 := by
    intro j
    dsimp [q]
    exact pow_le_pow_left₀ (hr_nonneg j) (hr_upper j) 2
  have hq_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop q :=
    isCoboundedUnder_ge_of_le Filter.atTop hq_upper
  obtain ⟨φ, hφs, hφ⟩ :=
    exists_seq_tendsto_liminf (f := Filter.atTop) (u := s) hs_cobdd hs_bddbelow
  have hxφ : Tendsto (fun n ↦ toWeakSpace ℝ H (x (φ n))) Filter.atTop
      (nhds (toWeakSpace ℝ H xLimit)) := hx.comp hφ
  have hinner : Tendsto (fun n ↦ 2 * inner ℝ (x (φ n) - xLimit) d) Filter.atTop
      (nhds 0) := by
    have h := (weakConvergence_iff_forall_tendsto_inner_right (fun n ↦ x (φ n)) xLimit).1 hxφ d
    have hsub := h.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ inner ℝ xLimit d) Filter.atTop
      (nhds (inner ℝ xLimit d)))
    have hzero : Tendsto (fun n ↦ inner ℝ (x (φ n) - xLimit) d) Filter.atTop (nhds 0) := by
      simpa [inner_sub_left] using hsub
    simpa using hzero.const_mul 2
  have hsq (n : ℕ) : s (φ n) ^ 2 = q (φ n) + 2 * inner ℝ (x (φ n) - xLimit) d + ‖d‖ ^ 2 := by
    dsimp [s, q, r, d]
    rw [show x (φ n) - z = (x (φ n) - xLimit) + (xLimit - z) by abel]
    rw [norm_add_sq_real]
  have hs_sq : Tendsto (fun n ↦ s (φ n) ^ 2) Filter.atTop
      (nhds ((Filter.liminf s Filter.atTop) ^ 2)) := by
    simpa [Function.comp_def] using hφs.pow 2
  have hqφ : Tendsto (q ∘ φ) Filter.atTop
      (nhds ((Filter.liminf s Filter.atTop) ^ 2 - ‖d‖ ^ 2)) := by
    have hsub := (hs_sq.sub hinner).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ‖d‖ ^ 2) Filter.atTop (nhds (‖d‖ ^ 2)))
    convert hsub using 1
    · ext n
      change q (φ n) = _
      rw [hsq]
      ring_nf
    · ring_nf
  have hqφ_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop (q ∘ φ) :=
    isCoboundedUnder_ge_of_le Filter.atTop (fun n ↦ hq_upper (φ n))
  have hq_le : Filter.liminf q Filter.atTop ≤ (Filter.liminf s Filter.atTop) ^ 2 - ‖d‖ ^ 2 := by
    calc
      Filter.liminf q Filter.atTop ≤ Filter.liminf (q ∘ φ) Filter.atTop :=
        hφ.liminf_le_liminf_comp hqφ_cobdd hq_bddbelow
      _ = (Filter.liminf s Filter.atTop) ^ 2 - ‖d‖ ^ 2 := hqφ.liminf_eq
  have hd : d ≠ 0 := by
    intro hd
    apply hz
    dsimp [d] at hd
    exact sub_eq_zero.mp hd |>.symm
  have hc_pos : 0 < ‖d‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hs_sq_lt : (Filter.liminf r Filter.atTop) ^ 2 < (Filter.liminf s Filter.atTop) ^ 2 := by
    rw [← hq_eq]
    nlinarith
  have hlim_s_nonneg : 0 ≤ Filter.liminf s Filter.atTop :=
    Filter.le_liminf_of_le hs_cobdd (Filter.Eventually.of_forall hs_nonneg)
  exact (sq_lt_sq₀ hlim_r_nonneg hlim_s_nonneg).mp hs_sq_lt
```

## Proof explanation
The proof begins by introducing abbreviations

$$
r_j=\|x_j-x_{\text{Limit}}\|,\qquad
s_j=\|x_j-z\|,\qquad
q_j=r_j^2,\qquad
d=x_{\text{Limit}}-z.
$$

The `let` commands only name these expressions; they add no new hypotheses.

First, `bounded_range_of_tendsto_weakly hx` is applied. This lemma says that if a sequence converges weakly to a limit, then its range is norm-bounded. Applied to $hx$, it gives

$$
\mathrm{Bornology.IsBounded}(\mathrm{Set.range} x).
$$

Then `isBounded_iff_forall_norm_le.mp` converts this boundedness into an explicit real number $R$ such that

$$
\|x_j\|\le R
$$

for every $j\in\mathbb N$. The `rcases` tactic destructs this existential statement into $R$ and the proof `hR`.

Using the triangle inequality `norm_sub_le`, the proof obtains

$$
r_j=\|x_j-x_{\text{Limit}}\|\le \|x_j\|+\|x_{\text{Limit}}\|\le R+\|x_{\text{Limit}}\|,
$$

and similarly

$$
s_j=\|x_j-z\|\le \|x_j\|+\|z\|\le R+\|z\|.
$$

The `dsimp`, `simpa`, `exact`, and `rw` commands unfold the local definitions, apply `norm_sub_le`, and rearrange the additive inequalities. Since norms are nonnegative, the proof also records

$$
0\le r_j,\qquad 0\le s_j
$$

for all $j$. The lemma `Filter.isBoundedUnder_of_eventually_ge` turns this eventual nonnegativity into the statement that $r$ and $s$ are eventually bounded below with respect to the order relation $(\cdot\ge\cdot)$. The lemma `isCoboundedUnder_ge_of_le` turns the upper bounds for $r$ and $s$ into the coboundedness hypotheses needed by the liminf API. Then `Filter.le_liminf_of_le` gives

$$
0\le \liminf r.
$$

Next, the proof studies the square of $r$. It defines

$$
g(t)=\max(t,0)^2.
$$

The function $g$ is monotone: if $a\le b$, then $\max(a,0)\le \max(b,0)$, and since both are nonnegative, squaring preserves the inequality. The proof of `hg_mono` uses `intro` to introduce $a,b$, then applies monotonicity of `max` and of squaring. The continuity statement `hg_cont` follows because $t\mapsto \max(t,0)$ is continuous and squaring is continuous. Applying `Monotone.map_liminf_of_continuousAt` to $r$ gives an equality between the liminf of $g\circ r$ and $g$ applied to the liminf of $r$. Because $r_j\ge0$ and $\liminf r\ge0$, this simplifies to

$$
\liminf q
=
\left(\liminf r\right)^2.
$$

The `rw` and `simp` steps perform these simplifications. The proof also shows $q_j\ge0$ by `positivity`, so $q$ is bounded below. Since

$$
0\le r_j\le R+\|x_{\text{Limit}}\|,
$$

squaring gives

$$
q_j\le \left(R+\|x_{\text{Limit}}\|\right)^2,
$$

so $q$ is cobounded as well.

The proof then extracts a subsequence along which $s$ attains its liminf. The lemma `exists_seq_tendsto_liminf`, applied to $s$ using its coboundedness and bounded-belowness, produces an index map $\varphi:\mathbb N\to\mathbb N$ with $\varphi(n)\to\infty$ and

$$
s(\varphi(n))\longrightarrow \liminf s.
$$

The properties returned are used as `hφs`, the convergence of $s\circ\varphi$, and `hφ`, the fact that $\varphi$ tends to `atTop`. Since $x_j$ converges weakly to $x_{\text{Limit}}$, composing with the subsequence preserves weak convergence:

$$
x(\varphi(n))\rightharpoonup x_{\text{Limit}}.
$$

This is the result of `hx.comp hφ`.

Now the cited theorem `weakConvergence_iff_forall_tendsto_inner_right` is used. In a complete real inner product space, weak convergence of a sequence $\xi(n)$ to a point $x$ is equivalent to the convergence

$$
\langle \xi(n),u\rangle \longrightarrow \langle x,u\rangle
$$

for every $u$. Here the proof applies it to $\xi(n)=x(\varphi(n))$, $x=x_{\text{Limit}}$, and $u=d$. This gives

$$
\langle x(\varphi(n)),d\rangle
\longrightarrow
\langle x_{\text{Limit}},d\rangle.
$$

Subtracting the constant sequence $\langle x_{\text{Limit}},d\rangle$ and using linearity of the inner product in its first argument, `inner_sub_left`, yields

$$
\langle x(\varphi(n))-x_{\text{Limit}},d\rangle
\longrightarrow 0.
$$

Multiplying by $2$, the proof obtains

$$
2\langle x(\varphi(n))-x_{\text{Limit}},d\rangle
\longrightarrow 0.
$$

The tactics `simpa`, `exact`, and `const_mul` implement these steps.

For each $n$, the proof next uses the identity

$$
x(\varphi(n))-z
=
\bigl(x(\varphi(n))-x_{\text{Limit}}\bigr)+d,
$$

where $d=x_{\text{Limit}}-z$. The `abel` tactic verifies this additive rearrangement. Then the real Hilbert space identity `norm_add_sq_real`,

$$
\|a+b\|^2=\|a\|^2+2\langle a,b\rangle+\|b\|^2,
$$

gives

$$
s(\varphi(n))^2
=
q(\varphi(n))
+
2\langle x(\varphi(n))-x_{\text{Limit}},d\rangle
+
\|d\|^2.
$$

Equivalently,

$$
q(\varphi(n))
=
s(\varphi(n))^2
-
2\langle x(\varphi(n))-x_{\text{Limit}},d\rangle
-
\|d\|^2.
$$

Since $s(\varphi(n))\to \liminf s$, squaring is continuous, so

$$
s(\varphi(n))^2\longrightarrow \left(\liminf s\right)^2.
$$

The inner product term tends to $0$. Therefore

$$
q(\varphi(n))\longrightarrow \left(\liminf s\right)^2-\|d\|^2.
$$

The `convert` and `ring_nf` commands reconcile the algebraic rearrangement with the previous identity.

Because $q\circ\varphi$ is cobounded by the same upper bound as $q$, the subsequence comparison lemma `liminf_le_liminf_comp` gives

$$
\liminf q\le \liminf(q\circ\varphi).
$$

Since $q\circ\varphi$ converges, its liminf equals its limit. Hence

$$
\liminf q\le \left(\liminf s\right)^2-\|d\|^2.
$$

The `calc` block records exactly this chain.

The proof now checks that $d\neq0$. If $d=0$, then $x_{\text{Limit}}-z=0$, so $x_{\text{Limit}}=z$, contradicting $hz:z\neq x_{\text{Limit}}$. Thus $d\neq0$. Therefore $\|d\|>0$, and by positivity of squares,

$$
\|d\|^2>0.
$$

Combining the earlier equality

$$
\liminf q=\left(\liminf r\right)^2
$$

with the inequality

$$
\liminf q\le \left(\liminf s\right)^2-\|d\|^2
$$

gives

$$
\left(\liminf r\right)^2
<
\left(\liminf s\right)^2.
$$

The tactic `nlinarith` closes this nonlinear arithmetic goal using the strict positivity of $\|d\|^2$. The proof also establishes $0\le \liminf s$ from the nonnegativity of $s$ and the coboundedness hypothesis, using `Filter.le_liminf_of_le`. Finally, for nonnegative real numbers $a,b$, the lemma `sq_lt_sq₀` states that $a^2<b^2$ implies $a<b$. Applying it with $a=\liminf r$ and $b=\liminf s$ yields

$$
\liminf r<\liminf s,
$$

which is exactly

$$
\liminf \|x_j-z\| >
\liminf \|x_j-x_{\text{Limit}}\|.
$$

Thus the Opial inequality is proved.

The Lean commands used along the way play the following roles: `intro` introduces variables in subgoals, `dsimp` unfolds local definitions, `rw` rewrites with equalities, `simp` and `simpa` simplify and close goals, `exact` supplies a required proof term, `rcases` and `obtain` destruct existential or conjunctive hypotheses, `calc` chains equalities and inequalities, `convert` changes a goal up to a supplied equality, and `ring_nf`, `abel`, `positivity`, and `nlinarith` perform algebraic normalization, additive rearrangement, nonnegativity proofs, and nonlinear arithmetic. No `linarith` step occurs in this particular proof.

