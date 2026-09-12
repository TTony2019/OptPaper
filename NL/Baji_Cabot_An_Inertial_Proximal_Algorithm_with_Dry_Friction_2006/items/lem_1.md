## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/lem_1.lean`

## Lean statement
```lean
theorem lem_2_1 (A : SetValuedOperator H H) (h_mono : IsMonotone A) (h_dom : A.dom = Set.univ)
    (h_zero : (0 : H) ∈ A (0 : H)) :
    (∀ x,
      PhiA A x ≥ supportFunction (A (0 : H)) x ∧
        supportFunction (A (0 : H)) x ≥ 0) ∧
    ((0 : H) ∈ interior (A (0 : H)) →
      ∃ (α : ℝ), α > 0 ∧ ∀ x, PhiA A x ≥ ((α * ‖x‖ : ℝ) : EReal))
```

## Statement explanation
The declaration `lem_2_1` concerns a set-valued operator $A$ on a real inner-product space $H$. For each point $x\in H$, $A(x)$ is a subset of $H$. The statement uses two extended-real quantities. The first is

$$
\Phi_A(x)=\inf\bigl\{\langle y,x\rangle_{\overline{\mathbb R}} \mid y\in A(x)\bigr\},
$$

where each real inner product $\langle y,x\rangle$ is viewed as an element of the extended real line $\overline{\mathbb R}$. The second is the support function of the particular set $A(0)$:

$$
S(x)=\operatorname{supportFunction}(A(0),x)
=\sup\bigl\{\langle z,x\rangle_{\overline{\mathbb R}} \mid z\in A(0)\bigr\}.
$$

The hypotheses are that $A$ is monotone, that its domain is all of $H$, and that $0\in A(0)$. In the proof, monotonicity is used in the following concrete form: if $y\in A(x)$ and $z\in A(0)$, then

$$
0\le \langle y-z,\,x-0\rangle.
$$

Since $x-0=x$, this says the vector $y-z$ has nonnegative inner product with $x$. The hypothesis $A.\mathrm{dom}=\mathrm{univ}$ is present in the statement but is not invoked in the displayed proof. The hypothesis $0\in A(0)$ is used to show the support function is nonnegative.

The conclusion has two parts. First, for every $x$,

$$
\Phi_A(x)\ge S(x)
\qquad\text{and}\qquad
S(x)\ge 0.
$$

Thus the infimum over $A(x)$ of the inner products $\langle y,x\rangle$ dominates the supremum over $A(0)$ of the inner products $\langle z,x\rangle$, and that supremum is nonnegative. Second, if $0$ lies in the interior of the set $A(0)$, then there exists a positive real number $\alpha$ such that for every $x$,

$$
\Phi_A(x)\ge (\alpha\|x\|)_{\overline{\mathbb R}},
$$

where again the real number $\alpha\|x\|$ is embedded into $\overline{\mathbb R}$. So a local interior-point condition at $0\in A(0)$ forces a global linear lower bound on $\Phi_A$.

## Lean proof
```lean
by
  have hPhi_ge_support : ∀ x, supportFunction (A (0 : H)) x ≤ PhiA A x := by
    intro x
    rw [PhiA, supportFunction]
    refine sSup_le ?_
    rintro _ ⟨z, hz, rfl⟩
    refine le_sInf ?_
    rintro _ ⟨y, hy, rfl⟩
    have hmono' : 0 ≤ inner ℝ (y - z) (x - 0) := h_mono y hy z hz
    have hle : inner ℝ z x ≤ inner ℝ y x := by
      have hmono'' : 0 ≤ inner ℝ y x - inner ℝ z x := by
        simpa [inner_sub_left, sub_zero] using hmono'
      exact sub_nonneg.mp hmono''
    exact EReal.coe_le_coe hle
  have hSupport_nonneg : ∀ x, (0 : EReal) ≤ supportFunction (A (0 : H)) x := by
    intro x
    rw [supportFunction]
    exact le_sSup ⟨0, h_zero, by simp⟩
  constructor
  · intro x
    exact ⟨hPhi_ge_support x, hSupport_nonneg x⟩
  · intro h_int
    have hnhds : A (0 : H) ∈ nhds (0 : H) := mem_interior_iff_mem_nhds.mp h_int
    rcases (Metric.mem_nhds_iff.mp hnhds) with ⟨ε, hε_pos, hε_subset⟩
    let α : ℝ := ε / 2
    have hα_pos : 0 < α := by positivity
    have hα_lt_ε : α < ε := by
      dsimp [α]
      linarith
    refine ⟨α, hα_pos, ?_⟩
    intro x
    have hsupp_lower : ((α * ‖x‖ : ℝ) : EReal) ≤ supportFunction (A (0 : H)) x := by
      by_cases hx : x = 0
      · subst x
        simpa using hSupport_nonneg (0 : H)
      · have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let z : H := (α / ‖x‖) • x
        have hz_norm : ‖z‖ = α := by
          dsimp [z]
          rw [norm_smul]
          have hdiv_nonneg : 0 ≤ α / ‖x‖ :=
            div_nonneg (le_of_lt hα_pos) (le_of_lt hxnorm_pos)
          rw [Real.norm_eq_abs, abs_of_nonneg hdiv_nonneg]
          field_simp [ne_of_gt hxnorm_pos]
        have hz_ball : z ∈ Metric.ball (0 : H) ε := by
          simpa [Metric.mem_ball, dist_zero_right, hz_norm] using hα_lt_ε
        have hzA : z ∈ A (0 : H) := hε_subset hz_ball
        have hinner_z : inner ℝ z x = α * ‖x‖ := by
          dsimp [z]
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
          field_simp [ne_of_gt hxnorm_pos]
        rw [supportFunction]
        have hle_sup : ((inner ℝ z x : ℝ) : EReal) ≤
            sSup ((fun z : H => (inner ℝ z x : EReal)) '' A (0 : H)) := by
          exact le_sSup ⟨z, hzA, rfl⟩
        simpa [hinner_z] using hle_sup
    exact le_trans hsupp_lower (hPhi_ge_support x)
```

## Proof explanation
The proof first establishes the inequality

$$
S(x)\le \Phi_A(x)
$$

for every $x$. It fixes an arbitrary $x$ and unfolds the definitions of `PhiA` and `supportFunction` using `rw`. The goal becomes

$$
\sup_{z\in A(0)}\langle z,x\rangle_{\overline{\mathbb R}}
\le
\inf_{y\in A(x)}\langle y,x\rangle_{\overline{\mathbb R}}.
$$

The tactic `refine sSup_le ?_` reduces a proof that a supremum is at most something to proving that every element of the supremum’s indexing set is at most that something. Thus the proof introduces an arbitrary $z\in A(0)$ and needs to show

$$
\langle z,x\rangle_{\overline{\mathbb R}}
\le
\inf_{y\in A(x)}\langle y,x\rangle_{\overline{\mathbb R}}.
$$

Then `refine le_sInf ?_` reduces a proof that something is at most an infimum to proving that it is at most every element of the infimum’s indexing set. So it introduces an arbitrary $y\in A(x)$ and needs

$$
\langle z,x\rangle_{\overline{\mathbb R}}
\le
\langle y,x\rangle_{\overline{\mathbb R}}.
$$

At this point monotonicity is applied to $y\in A(x)$ and $z\in A(0)$, giving

$$
0\le \langle y-z,x-0\rangle.
$$

The proof rewrites $x-0$ as $x$ and expands the inner product using `inner_sub_left`, obtaining

$$
0\le \langle y,x\rangle-\langle z,x\rangle.
$$

The lemma `sub_nonneg.mp` converts this into

$$
\langle z,x\rangle\le \langle y,x\rangle.
$$

Finally `EReal.coe_le_coe` transfers this real inequality to the corresponding inequality in $\overline{\mathbb R}$. Since $z$ and $y$ were arbitrary, every value in the supremum over $A(0)$ is bounded above by the infimum over $A(x)$, which proves $S(x)\le \Phi_A(x)$.

Next the proof shows

$$
0\le S(x)
$$

for every $x$. It unfolds `supportFunction` and uses `le_sSup`. The element $0$ belongs to the indexing set $A(0)$ by the hypothesis $0\in A(0)$. The inner product $\langle 0,x\rangle$ is $0$, as verified by `simp`. Therefore the value $0$ appears among the numbers whose supremum defines $S(x)$, and hence $0\le S(x)$. Combining this with the preceding inequality gives the first conjunct:

$$
\Phi_A(x)\ge S(x)\ge 0.
$$

For the second part, the proof assumes

$$
0\in \operatorname{interior}(A(0)).
$$

The lemma `mem_interior_iff_mem_nhds.mp` converts this into the statement that $A(0)$ is a neighborhood of $0$. Then `Metric.mem_nhds_iff.mp` produces a radius $\epsilon>0$ such that the open ball

$$
B(0,\epsilon)=\{u\in H\mid \|u\|<\epsilon\}
$$

is contained in $A(0)$. The proof defines

$$
\alpha=\frac{\epsilon}{2}.
$$

The tactic `positivity` proves $\alpha>0$, and `linarith` proves $\alpha<\epsilon$ from $\epsilon>0$.

It remains to prove

$$
(\alpha\|x\|)_{\overline{\mathbb R}}\le \Phi_A(x)
$$

for every $x$. Since already $S(x)\le \Phi_A(x)$, it is enough to prove

$$
(\alpha\|x\|)_{\overline{\mathbb R}}\le S(x).
$$

The proof therefore establishes this auxiliary inequality.

If $x=0$, then $\alpha\|x\|=0$, and the already proved nonnegativity $0\le S(0)$ gives the result. If $x\ne 0$, then $\|x\|>0$ by `norm_pos_iff`. The proof defines

$$
z=\frac{\alpha}{\|x\|}x.
$$

Using `norm_smul`, `Real.norm_eq_abs`, and the fact that $\alpha/\|x\|\ge 0$, it computes

$$
\|z\|=\alpha.
$$

Since $\alpha<\epsilon$, this gives $z\in B(0,\epsilon)$. Because $B(0,\epsilon)\subseteq A(0)$, it follows that $z\in A(0)$.

The proof then computes the inner product:

$$
\langle z,x\rangle
=
\left\langle \frac{\alpha}{\|x\|}x,x\right\rangle
=
\frac{\alpha}{\|x\|}\langle x,x\rangle
=
\frac{\alpha}{\|x\|}\|x\|^2
=
\alpha\|x\|.
$$

The lemmas used here are `real_inner_smul_left`, which pulls the scalar out of the first argument of the real inner product, and `real_inner_self_eq_norm_sq`, which states $\langle x,x\rangle=\|x\|^2$. Since $z\in A(0)$, the number $\langle z,x\rangle=\alpha\|x\|$ is one of the values over which the supremum $S(x)$ is taken. Therefore `le_sSup` yields

$$
(\alpha\|x\|)_{\overline{\mathbb R}}\le S(x).
$$

Finally `le_trans` composes this with $S(x)\le \Phi_A(x)$, giving

$$
(\alpha\|x\|)_{\overline{\mathbb R}}\le \Phi_A(x).
$$

This proves the required existence of $\alpha>0$ and completes the theorem.

