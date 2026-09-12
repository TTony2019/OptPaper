## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/ext_lem_2.lean`

## Lean statement
```lean
theorem forward_backward_fixedPoints_and_residual_bound (A : H → H) (B : SetValuedOperator H H)
    (hB : B.IsMaximalMonotone) (alpha : ℝ)
    (hA : CocoerciveOn alpha Set.univ (fun x : Set.univ ↦ A x))
    (r s : ℝ) (hs : 0 < s) (hsr : s ≤ r) (Tr Ts : H → H)
    (hTr : IsForwardBackwardSelection A B r Tr) (hTs : IsForwardBackwardSelection A B s Ts) :
    Function.fixedPoints Tr = operatorSumZeroSet A B ∧
      ∀ x, ‖x - Ts x‖ ≤ 2 * ‖x - Tr x‖
```

## Statement explanation
Let $H$ be a real inner product space. The declaration concerns a single-valued operator $A:H\to H$, a set-valued operator $B:H\rightrightarrows H$, a real number $\alpha$, two real step sizes $r,s$, and two functions $T_r,T_s:H\to H$. The hypotheses are: $B$ is maximal monotone; $A$ is $\alpha$-cocoercive on the whole space (the hypothesis `hA`); $0<s$ and $s\le r$, hence $r>0$; and $T_r,T_s$ are forward-backward selections for $A,B$ at steps $r,s$. In the proof, the selection hypotheses are used through the concrete consequences

$$
T_r x\in J_{rB}(x-rA x),\qquad T_s x\in J_{sB}(x-sA x)
$$

for every $x$, where $J_{rB}$ is the resolvent of $rB$, i.e. the inverse of $I+rB$.

The conclusion is the conjunction

$$
\operatorname{Fix}(T_r)=Z(A+B)
\quad\text{and}\quad
\forall x\in H,\quad \|x-T_s x\|\le 2\|x-T_r x\|.
$$

Here `operatorSumZeroSet A B` is the zero set

$$
Z(A+B)=\{x\mid 0\in A x+B x\},
$$

equivalently $\{x\mid \exists b\in B x,\ A x+b=0\}$. Thus the first part says that the fixed points of the step- $r$ forward-backward selection are exactly the solutions of the monotone inclusion $0\in A x+B x$. The second part says that the residual at the smaller step $s$ is controlled by twice the residual at the larger step $r$. The hypotheses `hA` and $\alpha$ are not used in the displayed proof; maximal monotonicity of $B$ is used only through its monotonicity.

## Lean proof
```lean
by
  have hr : 0 < r := lt_of_lt_of_le hs hsr
  constructor
  · apply Set.Subset.antisymm
    · intro x hx
      have hfix : Tr x = x := hx
      have hres := hTr x
      rw [mem_resolvent_smul_iff] at hres
      dsimp [SetValuedOperator.identityAddScaled] at hres
      rcases hres with ⟨b, hb, heq⟩
      rw [hfix] at heq
      have hb' : b = -A x := by
        have hscaled : r • b = r • (-A x) := by
          calc
            r • b = (x + r • b) - x := by abel
            _ = (x - r • A x) - x := by rw [heq]
            _ = r • (-A x) := by rw [smul_neg]; abel
        apply sub_eq_zero.mp
        apply (smul_eq_zero.mp ?_).resolve_left hr.ne'
        rw [smul_sub]
        exact sub_eq_zero.mpr hscaled
      rw [operatorSumZeroSet, SetValuedOperator.mem_zeros_iff]
      refine ⟨b, by simpa [hfix] using hb, ?_⟩
      rw [hb']
      abel
    · intro x hx
      rw [operatorSumZeroSet, SetValuedOperator.mem_zeros_iff] at hx
      rcases hx with ⟨b, hb, hzero⟩
      have hbneg : b = -A x := by
        exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hzero.symm)
      have hxres : x ∈ J[(r • B)] (x - r • A x) := by
        rw [mem_resolvent_smul_iff]
        dsimp [SetValuedOperator.identityAddScaled]
        refine ⟨b, hb, ?_⟩
        rw [hbneg, smul_neg]
        abel
      exact _root_.resolvent_unique_of_monotone hB.1 hr (hTr x) hxres
  · intro x
    have hpr := hTr x
    have hqs := hTs x
    rw [mem_resolvent_smul_iff] at hpr hqs
    dsimp [SetValuedOperator.identityAddScaled] at hpr hqs
    rcases hpr with ⟨bp, hbp, hpeq⟩
    rcases hqs with ⟨bq, hbq, hqeq⟩
    let a : H := x - Ts x
    let b : H := x - Tr x
    have hrbp : r • bp = b - r • A x := by
      dsimp [b]
      calc
        r • bp = (Tr x + r • bp) - Tr x := by abel
        _ = (x - r • A x) - Tr x := by rw [hpeq]
        _ = x - Tr x - r • A x := by abel
    have hsbq : s • bq = a - s • A x := by
      dsimp [a]
      calc
        s • bq = (Ts x + s • bq) - Ts x := by abel
        _ = (x - s • A x) - Ts x := by rw [hqeq]
        _ = x - Ts x - s • A x := by abel
    have hpq : Tr x - Ts x = a - b := by
      dsimp [a, b]
      abel
    have hscaled : (r * s) • (bp - bq) = s • b - r • a := by
      calc
        (r * s) • (bp - bq) = s • (r • bp) - r • (s • bq) := by module
        _ = s • (b - r • A x) - r • (a - s • A x) := by rw [hrbp, hsbq]
        _ = s • b - r • a := by module
    have hmono : 0 ≤ inner ℝ (bp - bq) (Tr x - Ts x) := hB.1 bp hbp bq hbq
    have hmul : 0 ≤ (r * s) * inner ℝ (bp - bq) (Tr x - Ts x) :=
      mul_nonneg (mul_nonneg (le_of_lt hr) (le_of_lt hs)) hmono
    have hid : (r * s) * inner ℝ (bp - bq) (Tr x - Ts x) =
        (r + s) * inner ℝ a b - s * ‖b‖ ^ 2 - r * ‖a‖ ^ 2 := by
      rw [← real_inner_smul_left, hscaled, hpq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      rw [real_inner_comm b a]
      ring
    have hquad : r * ‖a‖ ^ 2 + s * ‖b‖ ^ 2 ≤ (r + s) * inner ℝ a b := by
      rw [hid] at hmul
      linarith
    have hcs : inner ℝ a b ≤ ‖a‖ * ‖b‖ := real_inner_le_norm a b
    have hrs : r + s ≤ 2 * r := by linarith
    have hbound : r * ‖a‖ ^ 2 ≤ 2 * r * ‖a‖ * ‖b‖ := by
      have hleft : r * ‖a‖ ^ 2 ≤ (r + s) * inner ℝ a b := by
        nlinarith [mul_nonneg (le_of_lt hs) (sq_nonneg ‖b‖)]
      have hright : (r + s) * inner ℝ a b ≤ 2 * r * ‖a‖ * ‖b‖ := by
        have hcoef : 0 ≤ r + s := by linarith
        have hprod : 0 ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        have hcs' := mul_le_mul_of_nonneg_left hcs hcoef
        have hrs' := mul_le_mul_of_nonneg_right hrs hprod
        nlinarith
      exact hleft.trans hright
    by_cases ha : ‖a‖ = 0
    · rw [ha]
      positivity
    · have hapos : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg a) (Ne.symm ha)
      have hfac : 0 < r * ‖a‖ := mul_pos hr hapos
      have hmul : (r * ‖a‖) * ‖a‖ ≤ (r * ‖a‖) * (2 * ‖b‖) := by
       calc
        (r * ‖a‖) * ‖a‖ = r * ‖a‖ ^ 2 := by ring
        _ ≤ 2 * r * ‖a‖ * ‖b‖ := hbound
        _ = (r * ‖a‖) * (2 * ‖b‖) := by ring
      exact le_of_mul_le_mul_left hmul hfac
```

## Proof explanation
The proof starts with `hr : 0 < r := lt_of_lt_of_le hs hsr`, which combines $0<s$ and $s\le r$ to get $r>0$. The command `constructor` splits the conjunction into the set equality and the universal residual bound.

For the set equality, `Set.Subset.antisymm` reduces it to two inclusions. First let $x\in\operatorname{Fix}(T_r)$, so $T_r x=x$. The selection hypothesis gives $T_r x\in J_{rB}(x-rA x)$. The lemma `mem_resolvent_smul_iff` converts this to

$$
x-rA x\in (I+rB)(T_r x).
$$

Unfolding `identityAddScaled` produces $b\in B(T_r x)$ with

$$
T_r x+r b=x-rA x.
$$

Replacing $T_r x$ by $x$ gives $x+r b=x-rA x$, hence

$$
r b=r(-A x).
$$

Since $r>0$, cancellation of the scalar $r$ (implemented by `sub_eq_zero.mp` and `smul_eq_zero.mp`) gives $b=-A x$. Because $T_r x=x$, this same $b$ lies in $B x$. Now `operatorSumZeroSet` is unfolded and `mem_zeros_iff` is applied; the latter says that $x\in Z(A+B)$ exactly when there is $b\in B x$ with

$$
A x+b=0.
$$

Using $b=-A x$, this zero equation holds, so $x\in Z(A+B)$. The `abel` tactic handles the additive rearrangements.

Conversely, suppose $x\in Z(A+B)$. After unfolding `operatorSumZeroSet` and applying `mem_zeros_iff`, we get $b\in B x$ with $A x+b=0$. Commuting the sum and using the group lemma `eq_neg_of_add_eq_zero_left` gives $b=-A x$. To show $x\in J_{rB}(x-rA x)$, rewrite with `mem_resolvent_smul_iff` and unfold `identityAddScaled`; the same $b$ witnesses

$$
x-rA x=x+r b,
$$

because $b=-A x$. Thus both $T_r x$ and $x$ belong to $J_{rB}(x-rA x)$. The theorem `resolvent_unique_of_monotone` says that if $B$ is monotone, $r>0$, and two points lie in the same resolvent value $J_{rB}(y)$, then those points are equal. Applying it with $y=x-rA x$, `hB.1` (the monotonicity part of `hB`) and `hr` yields $T_r x=x$, i.e. $x\in\operatorname{Fix}(T_r)$. This proves the reverse inclusion and hence the set equality.

For the residual bound, fix an arbitrary $x$. From the selection hypotheses, after the same resolvent rewriting and unfolding, choose $b_p\in B(T_r x)$ and $b_q\in B(T_s x)$ such that

$$
T_r x+r b_p=x-rA x,\qquad T_s x+s b_q=x-sA x.
$$

Define

$$
a=x-T_s x,\qquad b=x-T_r x.
$$

The displayed equalities imply

$$
r b_p=b-rA x,\qquad s b_q=a-sA x,
$$

and also $T_r x-T_s x=a-b$. Combining these scalar identities gives

$$
(rs)(b_p-b_q)=s b-r a.
$$

The `module` tactic performs the scalar-module normalizations in this calculation.

Monotonicity of $B$, applied to $b_p\in B(T_r x)$ and $b_q\in B(T_s x)$, gives

$$
0\le \langle b_p-b_q,\ T_r x-T_s x\rangle.
$$

Since $r,s>0$, multiplication by $rs$ preserves the inequality, so

$$
0\le rs\,\langle b_p-b_q,\ T_r x-T_s x\rangle.
$$

Using the scaled identity and $T_r x-T_s x=a-b$, and expanding the inner product with `real_inner_smul_left`, `inner_sub_left`, `inner_sub_right`, `real_inner_self_eq_norm_sq`, and `real_inner_comm`, the proof computes

$$
rs\,\langle b_p-b_q,\ T_r x-T_s x\rangle
=\langle s b-r a,\ a-b\rangle
=(r+s)\langle a,b\rangle-s\|b\|^2-r\|a\|^2.
$$

The tactic `ring` closes this polynomial identity. Consequently, `linarith` rearranges the nonnegative quantity into

$$
r\|a\|^2+s\|b\|^2\le (r+s)\langle a,b\rangle.
$$

Next, Cauchy-Schwarz (`real_inner_le_norm`) gives

$$
\langle a,b\rangle\le \|a\|\|b\|,
$$

and $s\le r$ gives $r+s\le 2r$. Since $r+s\ge0$ and $\|a\|\|b\|\ge0$, multiplying the two inequalities gives

$$
(r+s)\langle a,b\rangle
\le (r+s)\|a\|\|b\|
\le 2r\|a\|\|b\|.
$$

Also $s\|b\|^2\ge0$, so from the previous quadratic inequality one gets

$$
r\|a\|^2\le (r+s)\langle a,b\rangle.
$$

Combining these inequalities (the nonlinear arithmetic steps are handled by `nlinarith`) yields

$$
r\|a\|^2\le 2r\|a\|\|b\|.
$$

If $\|a\|=0$, then the desired $\|a\|\le 2\|b\|$ is immediate by `positivity`. Otherwise $\|a\|>0$, so $r\|a\|>0$. Rewriting the last inequality as

$$
(r\|a\|)\|a\|\le (r\|a\|)(2\|b\|)
$$

allows cancellation of the positive factor $r\|a\|$ via `le_of_mul_le_mul_left`, yielding

$$
\|a\|\le 2\|b\|.
$$

Since $a=x-T_s x$ and $b=x-T_r x$, this is exactly

$$
\|x-T_s x\|\le 2\|x-T_r x\|.
$$

The proof is complete.

