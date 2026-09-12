## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/ext_thm_1.lean`

## Lean statement
```lean
theorem forward_backward_nonexpansive_and_fixedPoints (A : H → H) (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (alpha eps : ℝ) (heps : 0 < eps) (hepsAlpha : eps ≤ 2 * alpha)
    (hA : CocoerciveOn alpha Set.univ (fun x : Set.univ ↦ A x)) (T : H → H)
    (hT : ∀ x, T x ∈ J[(eps • B)] (x - eps • A x)) :
    LipschitzWith 1 T ∧ Function.fixedPoints T = operatorSumZeroSet A B
```

## Statement explanation
We work in a real inner product space \(H\) (all that is used of \(H\) is its real vector-space structure, its inner product \(\langle\cdot,\cdot\rangle_{\mathbb{R}}\), and the induced norm \(\|\cdot\|\)). The declaration concerns the classical forward–backward construction for a monotone inclusion.

The data are the following.

- A single-valued map \(A : H \to H\).
- A set-valued operator \(B\), i.e. a map sending each \(x\) to a subset \(B(x)\subseteq H\) (in Lean, \(B : H \to \mathrm{Set}\,H\), written as `SetValuedOperator H H`).
- The hypothesis \(hB : B.IsMaximalMonotone\), that \(B\) is a maximally monotone operator. The proof uses only the monotonicity part: for \(p,q\in H\) and \(u\in B(p)\), \(v\in B(q)\) one has \(\langle u-v,\,p-q\rangle_{\mathbb{R}}\ge 0\), equivalently \(\langle p-q,\,u-v\rangle_{\mathbb{R}}\ge 0\).
- Reals \(\alpha\) and \(\varepsilon\) with \(0<\varepsilon\) (`heps`) and \(\varepsilon\le 2\alpha\) (`hepsAlpha`). These two hypotheses together force \(\alpha>0\), since \(\alpha\ge \varepsilon/2\).
- The hypothesis \(hA\), that \(A\) is \(\alpha\)-cocoercive on the whole space: for all \(x,y\in H\),
\[
\alpha\,\|Ax-Ay\|^{2}\;\le\;\langle Ax-Ay,\,x-y\rangle_{\mathbb{R}}.
\]
- A single-valued map \(T : H \to H\) satisfying \(hT\): for every \(x\in H\),
\[
T x \in J[\varepsilon B]\bigl(x-\varepsilon Ax\bigr),
\]
where \(J[\varepsilon B]\) denotes the resolvent of the set-valued operator \(\varepsilon B\), i.e. the inverse of \(I+\varepsilon B\). Concretely, using the cited identity,
\[
J[\varepsilon B](a)=\{p : a-p\in \varepsilon B(p)\}=\{p : a\in p+\varepsilon B(p)\}.
\]
Thus \(T\) is a single-valued selection of the forward–backward operator \(J_{\varepsilon B}(I-\varepsilon A)\).

The conclusion is a conjunction:

1. `LipschitzWith 1 T`, i.e. \(T\) is \(1\)-Lipschitz:
\[
\|Tx-Ty\|\le \|x-y\| \quad\text{for all }x,y\in H,
\]
equivalently \(\mathrm{dist}(Tx,Ty)\le \mathrm{dist}(x,y)\).

2. `Function.fixedPoints T = operatorSumZeroSet A B`. Here `operatorSum A B` is the set-valued operator
\[
(\text{operatorSum }A\,B)(x)=\{u : \exists b\in B(x),\;u=Ax+b\},
\]
which represents \(A+B\) at \(x\). The set `operatorSumZeroSet A B` is the zero set of this operator; the proof shows that, for the current \(A,B\), it is precisely
\[
\{x\in H : 0\in (\text{operatorSum }A\,B)(x)\}=\{x\in H : 0\in Ax+B(x)\}.
\]
So the theorem states: whenever \(A\) is \(\alpha\)-cocoercive and \(B\) is maximally monotone with \(\varepsilon\in(0,2\alpha]\), any single-valued selection \(T\) of the forward–backward resolvent \(J_{\varepsilon B}(I-\varepsilon A)\) is nonexpansive, and its fixed points are exactly the solutions of the inclusion \(0\in Ax+Bx\).

## Lean proof
```lean
by
  have resolvent_mem_iff_exists_graph_witness {a p : H} :
      p ∈ J[(eps • B)] a ↔ ∃ b ∈ B p, a = p + eps • b := by
    rw [mem_resolvent_smul_iff]
    dsimp [SetValuedOperator.identityAddScaled]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  have resolvent_nonexpansive {a b p q : H}
      (hp : p ∈ J[(eps • B)] a) (hq : q ∈ J[(eps • B)] b) :
      ‖p - q‖ ≤ ‖a - b‖ := by
    rcases resolvent_mem_iff_exists_graph_witness.mp hp with ⟨u, hu, hpa⟩
    rcases resolvent_mem_iff_exists_graph_witness.mp hq with ⟨v, hv, hqb⟩
    have hab : a - b = (p - q) + eps • (u - v) := by
      rw [hpa, hqb, smul_sub]
      abel
    have hfirm : ‖p - q‖ ^ 2 ≤ inner ℝ (p - q) (a - b) := by
      rw [hab, inner_add_right, real_inner_smul_right]
      have hmono : 0 ≤ inner ℝ (p - q) (u - v) := by
        simpa [real_inner_comm] using hB.1 u hu v hv
      simp only [real_inner_self_eq_norm_sq]
      nlinarith [mul_nonneg heps.le hmono]
    have hcauchy : inner ℝ (p - q) (a - b) ≤ ‖p - q‖ * ‖a - b‖ :=
      real_inner_le_norm _ _
    have hsq : ‖p - q‖ ^ 2 ≤ ‖p - q‖ * ‖a - b‖ := hfirm.trans hcauchy
    by_cases hzero : ‖p - q‖ = 0
    · simp [hzero]
    · have hpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      nlinarith
  have forward_nonexpansive (x y : H) :
      ‖(x - eps • A x) - (y - eps • A y)‖ ≤ ‖x - y‖ := by
    have hvec : (x - eps • A x) - (y - eps • A y) =
        (x - y) - eps • (A x - A y) := by
      module
    have hsquare : ‖(x - eps • A x) - (y - eps • A y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [hvec, norm_sub_sq_real]
      simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg heps.le]
      nlinarith [hA.ineq ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩,
        mul_nonneg heps.le (sub_nonneg.mpr hepsAlpha),
        sq_nonneg ‖A x - A y‖]
    nlinarith [norm_nonneg ((x - eps • A x) - (y - eps • A y)), norm_nonneg (x - y)]
  have hLip : LipschitzWith 1 T := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [dist_eq_norm] using
      (resolvent_nonexpansive (hT x) (hT y)).trans (forward_nonexpansive x y)
  refine ⟨hLip, ?_⟩
  ext x
  constructor
  · intro hx
    have hfix : T x = x := by
      simpa [Function.mem_fixedPoints, Function.IsFixedPt] using hx
    rcases resolvent_mem_iff_exists_graph_witness.mp (hT x) with ⟨b, hb, heq⟩
    have hbneg : b = -A x := by
      have heq' : x - eps • A x = x + eps • b := by simpa [hfix] using heq
      have hsmul : eps • b = eps • (-A x) := by
        calc
          eps • b = (x + eps • b) - x := by abel
          _ = (x - eps • A x) - x := by rw [← heq']
          _ = eps • (-A x) := by module
      exact smul_right_injective H heps.ne' (by simpa using hsmul)
    change (0 : H) ∈ operatorSum A B x
    refine ⟨-A x, ?_, by simp⟩
    simpa [hfix, hbneg] using hb
  · intro hx
    change (0 : H) ∈ operatorSum A B x at hx
    rcases hx with ⟨b, hb, hsum⟩
    have hbneg : b = -A x := by
      apply eq_neg_of_add_eq_zero_right
      simpa using hsum.symm
    have hself : x ∈ J[(eps • B)] (x - eps • A x) := by
      apply resolvent_mem_iff_exists_graph_witness.mpr
      refine ⟨b, hb, ?_⟩
      rw [hbneg]
      module
    have htx : T x = x := by
      have : ‖T x - x‖ = 0 := by simpa using resolvent_nonexpansive (hT x) hself
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    simpa [Function.mem_fixedPoints, Function.IsFixedPt] using htx
```

## Proof explanation
The proof begins by recording a graph-wise description of resolvent membership.

First auxiliary fact (`resolvent_mem_iff_exists_graph_witness`). For \(a,p\in H\),
\[
p\in J[\varepsilon B](a)\quad\Longleftrightarrow\quad \exists b\in B(p),\; a=p+\varepsilon b.
\]
The tactic `rw [mem_resolvent_smul_iff]` applies the cited equivalence \(y\in J[\rho A]\leftrightarrow x\in A.\text{identityAddScaled }\rho\,y\) with \(A:=B\), \(\rho:=\varepsilon\), \(x:=a\), \(y:=p\), turning the left side into \(a\in B.\text{identityAddScaled }\varepsilon\,p\). Using the cited definition, \(B.\text{identityAddScaled }\varepsilon\,p=\{p+\varepsilon b : b\in B(p)\}\), which the tactic `dsimp [SetValuedOperator.identityAddScaled]` unfolds. Membership in that set is exactly the displayed existential; the two `rintro` branches just unpack and repack it, with no further mathematics.

Second auxiliary fact (`resolvent_nonexpansive`). Given \(p\in J[\varepsilon B](a)\) and \(q\in J[\varepsilon B](b)\),
\[
\|p-q\|\le \|a-b\|.
\]
Both hypotheses are first turned into graph witnesses by `resolvent_mem_iff_exists_graph_witness.mp`: there are \(u\in B(p)\) and \(v\in B(q)\) with \(a=p+\varepsilon u\) and \(b=q+\varepsilon v\). Then the tactic `abel`, after `smul_sub`, establishes
\[
a-b=(p-q)+\varepsilon(u-v).
\]
The monotonicity part of `B.IsMaximalMonotone`, invoked as `hB.1 u hu v hv`, gives \(0\le \langle u-v,\,p-q\rangle_{\mathbb{R}}\), and `real_inner_comm` rewrites this as \(0\le \langle p-q,\,u-v\rangle_{\mathbb{R}}\). Expanding with `inner_add_right`, `real_inner_smul_right` and `real_inner_self_eq_norm_sq` (which identifies \(\langle w,w\rangle_{\mathbb{R}}\) with \(\|w\|^{2}\)) yields
\[
\langle p-q,\,a-b\rangle_{\mathbb{R}}=\|p-q\|^{2}+\varepsilon\langle p-q,\,u-v\rangle_{\mathbb{R}},
\]
and since the last term is nonnegative while \(\varepsilon>0\) (used via `mul_nonneg heps.le hmono`), we get the firm-nonexpansiveness inequality
\[
\|p-q\|^{2}\le \langle p-q,\,a-b\rangle_{\mathbb{R}}.
\]
Cauchy–Schwarz (`real_inner_le_norm`) bounds the right side by \(\|p-q\|\,\|a-b\|\), so \(\|p-q\|^{2}\le \|p-q\|\,\|a-b\|\). If \(\|p-q\|=0\) the claimed inequality is immediate; otherwise \(\|p-q\|>0\) and dividing through gives \(\|p-q\|\le \|a-b\|\). The final `nlinarith` combines the nonnegativity of the norm with this case split.

Third auxiliary fact (`forward_nonexpansive`). For all \(x,y\),
\[
\|(x-\varepsilon Ax)-(y-\varepsilon Ay)\|\le \|x-y\|.
\]
The tactic `module` establishes the linear identity
\[
(x-\varepsilon Ax)-(y-\varepsilon Ay)=(x-y)-\varepsilon(Ax-Ay),
\]
giving `hvec`. Squaring and expanding with `norm_sub_sq_real` (which writes \(\|r-s\|^{2}=\|r\|^{2}-2\langle r,s\rangle_{\mathbb{R}}+\|s\|^{2}\)) together with `real_inner_smul_right`, `norm_smul`, `Real.norm_eq_abs` and `abs_of_nonneg heps.le` produces
\[
\|(x-y)-\varepsilon(Ax-Ay)\|^{2}
=\|x-y\|^{2}-2\varepsilon\langle x-y,\,Ax-Ay\rangle_{\mathbb{R}}+\varepsilon^{2}\|Ax-Ay\|^{2}.
\]
The cocoercivity hypothesis, invoked as `hA.ineq ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩`, gives
\[
\alpha\|Ax-Ay\|^{2}\le \langle Ax-Ay,\,x-y\rangle_{\mathbb{R}},
\]
which by symmetry of the real inner product is the same as \(\alpha\|Ax-Ay\|^{2}\le \langle x-y,\,Ax-Ay\rangle_{\mathbb{R}}\). The hypothesis \(\varepsilon\le 2\alpha\) together with \(\varepsilon>0\) yields \(\varepsilon(2\alpha-\varepsilon)\ge 0\) (`mul_nonneg heps.le (sub_nonneg.mpr hepsAlpha)`), and multiplying by the nonnegative quantity \(\|Ax-Ay\|^{2}\) (`sq_nonneg`) gives \(2\varepsilon\alpha\|Ax-Ay\|^{2}\ge \varepsilon^{2}\|Ax-Ay\|^{2}\). Feeding these three inequalities into `nlinarith` yields
\[
\|(x-\varepsilon Ax)-(y-\varepsilon Ay)\|^{2}\le \|x-y\|^{2}.
\]
A final `nlinarith` combines this with the nonnegativity of both norms to conclude the desired inequality of norms.

Fourth step, the Lipschitz property. `refine LipschitzWith.of_dist_le_mul ?_` replaces the goal `LipschitzWith 1 T` by the equivalent pointwise inequality \(\mathrm{dist}(Tx,Ty)\le 1\cdot\mathrm{dist}(x,y)\), and `intro x y` introduces arbitrary \(x,y\). The hypothesis `hT` gives \(Tx\in J[\varepsilon B](x-\varepsilon Ax)\) and \(Ty\in J[\varepsilon B](y-\varepsilon Ay)\). Applying the second auxiliary fact to these two memberships, with \(a=x-\varepsilon Ax\), \(p=Tx\), \(b=y-\varepsilon Ay\), \(q=Ty\), yields
\[
\|Tx-Ty\|\le \|(x-\varepsilon Ax)-(y-\varepsilon Ay)\|,
\]
and the third auxiliary fact yields \(\|(x-\varepsilon Ax)-(y-\varepsilon Ay)\|\le \|x-y\|\). The tactic `.trans` composes the two inequalities to give \(\|Tx-Ty\|\le \|x-y\|\), and `simpa [dist_eq_norm]` rewrites this as \(\mathrm{dist}(Tx,Ty)\le \mathrm{dist}(x,y)\), i.e. the Lipschitz bound.

Fifth step, identifying the fixed points. `refine ⟨hLip, ?_⟩` discharges the first conjunct and leaves the set equality `Function.fixedPoints T = operatorSumZeroSet A B`. The tactic `ext x` reduces this to a pointwise equivalence
\[
x\in \mathrm{Fix}(T)\iff x\in \mathrm{zer}(A+B).
\]

Forward direction. Assume \(x\in\mathrm{Fix}(T)\), so `hfix : T x = x`. Applying `resolvent_mem_iff_exists_graph_witness.mp` to `hT x` produces \(b\in B(Tx)\) with \(x-\varepsilon Ax=Tx+\varepsilon b\); substituting `hfix` (via `simpa [hfix] using heq`) rewrites this as \(b\in B(x)\) and \(x-\varepsilon Ax=x+\varepsilon b\). Subtracting \(x\) and simplifying (the `calc` block using `abel` and `module`) gives \(\varepsilon b=\varepsilon(-Ax)\). Injectivity of multiplication by the nonzero scalar \(\varepsilon\) (`smul_right_injective H heps.ne'`) then yields
\[
b=-Ax.
\]
Since \(b\in B(x)\) and \(Ax+b=0\), the point \(x\) lies in the zero set of the operator sum: after `change (0 : H) ∈ operatorSum A B x`, the term `refine ⟨-A x, ?_, by simp⟩` gives the witness \(-Ax\), the membership \(-Ax\in B(x)\) is obtained by `simpa [hfix, hbneg] using hb`, and `simp` closes the arithmetic equality \(0=Ax+(-Ax)\). So \(x\in\mathrm{zer}(A+B)\).

Reverse direction. Assume \(x\in\mathrm{zer}(A+B)\), i.e. `change`d into \(0\in(\text{operatorSum }A\,B)(x)\). Unpacking the existential with `rcases hx with ⟨b, hb, hsum⟩` gives \(b\in B(x)\) with \(0=Ax+b\). The fact `eq_neg_of_add_eq_zero_right` (applied to `hsum.symm`, i.e. \(Ax+b=0\)) then gives \(b=-Ax\). Consequently \(x-\varepsilon Ax=x+\varepsilon b\), and the first auxiliary fact (`resolvent_mem_iff_exists_graph_witness.mpr`, using `rw [hbneg]` and `module`) yields the membership
\[
x\in J[\varepsilon B]\bigl(x-\varepsilon Ax\bigr).
\]
Now the second auxiliary fact, applied to `hT x` and this membership \(hself\) with the same argument \(x-\varepsilon Ax\), gives
\[
\|Tx-x\|\le \|(x-\varepsilon Ax)-(x-\varepsilon Ax)\|=0,
\]
so \(\|Tx-x\|=0\). The lemma `norm_eq_zero` turns this into \(Tx-x=0\), and `sub_eq_zero` turns this into \(Tx=x\). The final `simpa [Function.mem_fixedPoints, Function.IsFixedPt]` records that \(x\) is a fixed point of \(T\).

This completes both inclusions and hence the equality `Function.fixedPoints T = operatorSumZeroSet A B`, finishing the proof.

