## Source file
`Burachik_Svaiter_Robustness_HPE_2001/items/lem_3.lean`

## Lean statement
```lean
theorem hpe_unbounded_of_no_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (A : HPEIterates H T) (hzero : T.zeros = ∅) :
    ¬ Bornology.IsBounded (Set.range A.x)
```

## Statement explanation
The declaration is stated for a real Hilbert space $H$, namely a complete real inner product space. The operator $T$ is a set-valued operator from $H$ to subsets of $H$, written $T:H\to \mathcal P(H)$. The hypothesis $h_T$ says that $T$ is maximal monotone: $T$ is monotone, and its graph is maximal among the graphs of monotone operators. The variable $A$ is an HPE iterate object for $T$; in the proof it supplies sequences $x_k,y_k,v_k\in H$ and real sequences $c_k,\varepsilon_k,\alpha_k,\delta_k,\sigma_k$, together with the standard HPE error, residual, summability, and enlargement properties used below. The hypothesis $hzero$ says $T.\operatorname{zeros}=\varnothing$, meaning that there is no $x\in H$ such that $0\in T x$. The conclusion is

$$
\neg \operatorname{Bornology.IsBounded}\bigl(\operatorname{Set.range} A.x\bigr),
$$

which means that the set of iterates $\{x_k:k\in\mathbb N\}$ is not bounded in the norm topology. Equivalently, if the HPE iterates $x_k$ are bounded, then $T$ must have a zero. The proof proves this contrapositive: it assumes boundedness of the iterates and constructs a point $\bar x$ with $0\in T\bar x$, contradicting $T.\operatorname{zeros}=\varnothing$.

## Lean proof
```lean
by
  intro hxb
  rcases isBounded_iff_forall_norm_le.mp hxb with ⟨Bx, hBx⟩
  have hx : ∀ k, ‖A.x k‖ ≤ Bx := by
    intro k
    exact hBx _ (Set.mem_range_self k)
  have hBx0 : 0 ≤ Bx := le_trans (norm_nonneg (A.x 0)) (hx 0)
  rcases nonneg_summable_uniform_bound A.α_nonneg A.summable_alpha with
    ⟨Bα, hBα0, hα⟩
  rcases nonneg_summable_uniform_bound A.δ_nonneg A.summable_delta with
    ⟨Bδ, hBδ0, hδ⟩
  have hcv : ∀ k, ‖A.c k • A.v k‖ ≤ Bx + Bx + Bα := by
    intro k
    let e : H := A.x (k + 1) - (A.x k - A.c k • A.v k)
    have he : ‖e‖ ≤ A.α k := by
      simpa [e] using A.update_error k
    have hrepr : A.c k • A.v k = A.x k - A.x (k + 1) + e := by
      dsimp [e]
      abel
    calc
      ‖A.c k • A.v k‖ = ‖A.x k - A.x (k + 1) + e‖ := by rw [hrepr]
      _ ≤ ‖A.x k - A.x (k + 1)‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖A.x k‖ + ‖A.x (k + 1)‖) + A.α k := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ Bx + Bx + Bα := by
        exact add_le_add (add_le_add (hx k) (hx (k + 1))) (hα k)
  have hcv0 : 0 ≤ Bx + Bx + Bα := by positivity
  rcases A.sigma_bound with ⟨σbar, hσbar0, hσbar1, hσ⟩
  let C : ℝ := Bx + Bx + Bα
  have hC : 0 ≤ C := by simpa [C] using hcv0
  have hquadratic : ∀ k, (1 - σbar ^ 2) * ‖A.y k - A.x k‖ ^ 2 -
      2 * C * ‖A.y k - A.x k‖ ≤ Bδ := by
    intro k
    let q : H := A.c k • A.v k
    let b : H := A.y k - A.x k
    have hrev : (‖b‖ - ‖q‖) ^ 2 ≤ ‖q + b‖ ^ 2 :=
      squared_reverse_triangle_bound (a := q) (b := b)
    have heq : q + b = A.c k • A.v k + A.y k - A.x k := by
      dsimp [q, b]
      abel
    have hres := A.residual_bound k
    have hce : 0 ≤ 2 * A.c k * A.ε k := by
      have := A.c_pos k
      have := A.ε_nonneg k
      positivity
    have hnorm : ‖q + b‖ ^ 2 ≤ A.δ k + (A.σ k) ^ 2 * ‖b‖ ^ 2 := by
      rw [heq]
      linarith
    have hs0 : 0 ≤ A.σ k := A.σ_nonneg k
    have hsle : A.σ k ≤ σbar := (hσ k).2
    have hssq : (A.σ k) ^ 2 ≤ σbar ^ 2 := by nlinarith
    have htb : 0 ≤ ‖b‖ ^ 2 := sq_nonneg _
    have hmult : (A.σ k) ^ 2 * ‖b‖ ^ 2 ≤ σbar ^ 2 * ‖b‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hssq htb
    have hqbound : ‖q‖ ≤ C := by simpa [q, C] using hcv k
    have hqmul : 2 * ‖q‖ * ‖b‖ ≤ 2 * C * ‖b‖ := by
      gcongr
    have hδbound : A.δ k ≤ Bδ := hδ k
    change (1 - σbar ^ 2) * ‖b‖ ^ 2 - 2 * C * ‖b‖ ≤ Bδ
    nlinarith [hrev, hnorm, hmult, hqmul, sq_nonneg ‖q‖]
  have hp : 0 < 1 - σbar ^ 2 := by nlinarith [sq_nonneg σbar]
  let R : ℝ := (C + Real.sqrt (C ^ 2 + (1 - σbar ^ 2) * Bδ)) /
    (1 - σbar ^ 2)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have htbound : ∀ k, ‖A.y k - A.x k‖ ≤ R := by
    intro k
    apply quadratic_nonneg_root_bound hp hC hBδ0 (norm_nonneg _)
    simpa [R] using hquadratic k
  let By : ℝ := R + Bx
  have hBy0 : 0 ≤ By := by dsimp [By]; positivity
  have hy : ∀ k, ‖A.y k‖ ≤ By := by
    intro k
    calc
      ‖A.y k‖ = ‖(A.y k - A.x k) + A.x k‖ := by congr 1 <;> abel
      _ ≤ ‖A.y k - A.x k‖ + ‖A.x k‖ := norm_add_le _ _
      _ ≤ R + Bx := add_le_add (htbound k) (hx k)
      _ = By := rfl
  rcases minty_surjective_of_maximal_monotone hT (0 : H) with
    ⟨z0, u0, hu0, _⟩
  have hz0 : z0 ∈ T.dom := SetValuedOperator.mem_dom_iff T z0 |>.2 ⟨u0, hu0⟩
  let M : ℝ := max ‖z0‖ (max Bx By) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hz0M : ‖z0‖ < M := by
    dsimp [M]
    linarith [le_max_left ‖z0‖ (max Bx By)]
  have hxM : ∀ k, ‖A.x k‖ < M := by
    intro k
    exact lt_of_le_of_lt (le_trans (hx k) (le_trans (le_max_left _ _) (le_max_right _ _)))
      (lt_add_one _)
  have hyM : ∀ k, ‖A.y k‖ < M := by
    intro k
    exact lt_of_le_of_lt (le_trans (hy k) (le_trans (le_max_right _ _) (le_max_right _ _)))
      (lt_add_one _)
  have hBxM : Bx < M := by
    dsimp [M]
    linarith [le_max_left Bx By, le_max_right ‖z0‖ (max Bx By)]
  have hz0int : z0 ∈ interior (relatedBall (H := H) M) := by
    apply Metric.ball_subset_interior_closedBall
    change dist z0 0 < 2 * M
    rw [dist_zero_right]
    linarith
  have hxint : ∀ k, A.x k ∈ interior (relatedBall (H := H) M) := by
    intro k
    apply Metric.ball_subset_interior_closedBall
    change dist (A.x k) 0 < 2 * M
    rw [dist_zero_right]
    linarith [hxM k]
  have hyint : ∀ k, A.y k ∈ interior (relatedBall (H := H) M) := by
    intro k
    apply Metric.ball_subset_interior_closedBall
    change dist (A.y k) 0 < 2 * M
    rw [dist_zero_right]
    linarith [hyM k]
  have hSnonempty : (relatedBall (H := H) M).Nonempty := by
    refine ⟨0, ?_⟩
    simp [relatedBall]
    linarith
  have hSclosed : IsClosed (relatedBall (H := H) M) := by
    simpa [relatedBall] using (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) (2 * M)))
  have hSconvex : Convex ℝ (relatedBall (H := H) M) := by
    simpa [relatedBall] using (convex_closedBall (0 : H) (2 * M))
  let U : SetValuedOperator H H := relatedOperator T M
  have hU : U.IsMaximalMonotone := by
    dsimp [U, relatedOperator]
    apply rockafellar_sum_maximal hT (relatedBall (H := H) M) hSnonempty hSclosed hSconvex
    exact ⟨z0, hz0, hz0int⟩
  have hUdom : Bornology.IsBounded U.dom := by
    apply Bornology.IsBounded.subset (Metric.isBounded_closedBall :
      Bornology.IsBounded (Metric.closedBall (0 : H) (2 * M)))
    intro x hxU
    have hxball : x ∈ relatedBall (H := H) M := by
      simpa [U] using related_operator_dom_subset_ball T M hxU
    simpa [relatedBall] using hxball
  rcases (maximal_monotone_surjective_of_bounded_domain hU hUdom).2 with ⟨xzero, hxzero⟩
  have hUzero : ∃ x : H, (0 : H) ∈ U x := ⟨xzero, hxzero⟩
  have hUmem : ∀ k, A.v k ∈ epsilonEnlargement U (A.ε k) (A.ε_nonneg k) (A.y k) := by
    intro k
    change ∀ z w, w ∈ U z → -A.ε k ≤ inner ℝ (w - A.v k) (z - A.y k)
    intro z w hw
    change w ∈ T z + N[relatedBall (H := H) M] z at hw
    rw [Set.mem_add] at hw
    rcases hw with ⟨u, hu, η, hη, rfl⟩
    have hTmem := A.enlargement_mem k z u hu
    change -A.ε k ≤ inner ℝ (u - A.v k) (z - A.y k) at hTmem
    have hηineq : 0 ≤ inner ℝ η (z - A.y k) := by
      have hle : inner ℝ (A.y k - z) η ≤ 0 :=
        (Set.mem_normalCone_iff_forall.mp hη).2 (A.y k) (interior_subset (hyint k))
      have hle' : inner ℝ η (A.y k - z) ≤ 0 := by simpa [real_inner_comm] using hle
      have hcomm : inner ℝ η (A.y k - z) = -inner ℝ η (z - A.y k) := by
        rw [show A.y k - z = -(z - A.y k) by abel, inner_neg_right]
      linarith
    calc
      -A.ε k = -A.ε k + 0 := by ring
      _ ≤ inner ℝ (u - A.v k) (z - A.y k) + inner ℝ η (z - A.y k) :=
        add_le_add hTmem hηineq
      _ = inner ℝ (u + η - A.v k) (z - A.y k) := by
        rw [show u + η - A.v k = (u - A.v k) + η by abel, inner_add_left]
  let AU : HPEIterates H U := { A with enlargement_mem := hUmem }
  rcases hpe_weakly_converges_to_zero hU AU hUzero with ⟨xbar, hxbarU, hxweak⟩
  have hxbarB : ‖xbar‖ ≤ Bx := by
    have hmem : ∀ k, A.x k ∈ Metric.closedBall (0 : H) Bx := by
      intro k
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx k
    have hlim : xbar ∈ Metric.closedBall (0 : H) Bx := by
      apply mem_of_tendsto_weakly_of_isClosed_convex (C := Metric.closedBall (0 : H) Bx)
        Metric.isClosed_closedBall (convex_closedBall (0 : H) Bx) hmem
      simpa [AU] using hxweak
    simpa [Metric.mem_closedBall, dist_zero_right] using hlim
  have hxbarint : xbar ∈ interior (relatedBall (H := H) M) := by
    apply Metric.ball_subset_interior_closedBall
    change dist xbar 0 < 2 * M
    rw [dist_zero_right]
    linarith [hxbarB, hBxM]
  change (0 : H) ∈ U xbar at hxbarU
  change (0 : H) ∈ T xbar + N[relatedBall (H := H) M] xbar at hxbarU
  rw [Set.mem_add] at hxbarU
  rcases hxbarU with ⟨u, hu, η, hη, hsum⟩
  have hηzero : η = 0 := normalCone_zero_of_interior hxbarint hη
  have huzero : u = 0 := by simpa [hηzero] using hsum
  have hcontr : xbar ∈ T.zeros := by simpa [SetValuedOperator.mem_zeros_iff, huzero] using hu
  simpa [hzero] using hcontr
```

## Proof explanation
The proof begins with `intro hxb`, which assumes for contradiction that the range of $A.x$ is bounded. Using `isBounded_iff_forall_norm_le.mp`, this boundedness is converted into the existence of a real number $B_x$ such that $\|x_k\|\le B_x$ for every $k$. The `rcases` tactic extracts this $B_x$ and the pointwise bound, and then the proof records $0\le B_x$, since $\|x_0\|\ge0$.

Next the proof applies `nonneg_summable_uniform_bound` to the sequence $\alpha_k$. That lemma says that if a real sequence is nonnegative and summable, then it is uniformly bounded above by some nonnegative constant. The HPE hypotheses `A.α_nonneg` and `A.summable_alpha` provide exactly these two assumptions, so the proof obtains $B_\alpha\ge0$ with $\alpha_k\le B_\alpha$ for all $k$. The same lemma is applied to $\delta_k$ using `A.δ_nonneg` and `A.summable_delta`, giving $B_\delta\ge0$ with $\delta_k\le B_\delta$ for all $k$.

The proof then bounds $c_kv_k$. It defines the error

$$
e_k=A.x(k+1)-\bigl(A.x(k)-A.c(k)\cdot A.v(k)\bigr).
$$

The HPE update-error field `A.update_error k` gives $\|e_k\|\le\alpha_k$. Rearranging additively gives

$$
A.c(k)\cdot A.v(k)=A.x(k)-A.x(k+1)+e_k.
$$

Using the triangle inequality, the inequality $\|a-b\|\le\|a\|+\|b\|$, and the bounds on $x_k$, the proof obtains

$$
\|A.c(k)\cdot A.v(k)\|\le 2B_x+B_\alpha.
$$

The constant

$$
C=2B_x+B_\alpha
$$

is therefore nonnegative.

The proof now uses `A.sigma_bound`. This field provides a real number $\bar\sigma$ with $0\le\bar\sigma$, a further inequality on $\bar\sigma$ which, together with $0\le\bar\sigma$, makes $1-\bar\sigma^2>0$, and the bound $\sigma_k\le\bar\sigma$ for every $k$. The proof records $1-\bar\sigma^2>0$ as `hp`.

For each $k$, set

$$
q_k=A.c(k)\cdot A.v(k),\qquad b_k=A.y(k)-A.x(k).
$$

The lemma `squared_reverse_triangle_bound` states that for vectors $a,b$ in a real inner product space,

$$
(\|b\|-\|a\|)^2\le\|a+b\|^2.
$$

Applied with $a=q_k$ and $b=b_k$, it yields

$$
(\|b_k\|-\|q_k\|)^2\le\|q_k+b_k\|^2.
$$

The HPE residual bound `A.residual_bound k`, together with $0\le 2A.c(k)A.\varepsilon(k)$, which follows from $A.c(k)>0$ and $A.\varepsilon(k)\ge0$, gives the consequence

$$
\|q_k+b_k\|^2\le \delta_k+\sigma_k^2\|b_k\|^2.
$$

Since $0\le\sigma_k\le\bar\sigma$, one has $\sigma_k^2\le\bar\sigma^2$, hence

$$
\sigma_k^2\|b_k\|^2\le\bar\sigma^2\|b_k\|^2.
$$

Also $\|q_k\|=\|A.c(k)\cdot A.v(k)\|\le C$, so

$$
2\|q_k\|\|b_k\|\le 2C\|b_k\|.
$$

Combining these inequalities with $\delta_k\le B_\delta$ using `nlinarith`, the proof obtains

$$
(1-\bar\sigma^2)\|A.y(k)-A.x(k)\|^2
-2C\|A.y(k)-A.x(k)\|\le B_\delta.
$$

Now the quadratic estimate `quadratic_nonneg_root_bound` is applied. It says that if $p>0$, $C\ge0$, $D\ge0$, $t\ge0$, and

$$
p t^2-2Ct\le D,
$$

then

$$
t\le \frac{C+\sqrt{C^2+pD}}{p}.
$$

Here $p=1-\bar\sigma^2>0$, $C=2B_x+B_\alpha\ge0$, $D=B_\delta\ge0$, and $t=\|A.y(k)-A.x(k)\|\ge0$. Therefore

$$
\|A.y(k)-A.x(k)\|\le R
$$

for all $k$, where

$$
R=\frac{C+\sqrt{C^2+(1-\bar\sigma^2)B_\delta}}{1-\bar\sigma^2}.
$$

The proof also records $0\le R$. Defining $B_y=R+B_x$, the triangle inequality gives

$$
\|A.y(k)\|=\|(A.y(k)-A.x(k))+A.x(k)\|
\le \|A.y(k)-A.x(k)\|+\|A.x(k)\|
\le R+B_x=B_y.
$$

The proof then uses `minty_surjective_of_maximal_monotone`. That theorem says that if $T$ is maximal monotone, then for every $y\in H$ there exist $x\in H$ and $u\in T x$ such that $y=x+u$. Taking $y=0$, the proof obtains $z_0,u_0$ with $u_0\in T z_0$ and $0=z_0+u_0$. In particular, using `SetValuedOperator.mem_dom_iff`, the point $z_0$ lies in $T.\operatorname{dom}$.

The proof defines

$$
M=\max\bigl(\|z_0\|,\max(B_x,B_y)\bigr)+1.
$$

Then $M>0$, and the inequalities $\|z_0\|<M$, $\|x_k\|<M$, $\|y_k\|<M$, and $B_x<M$ all hold. The definition

$$
\operatorname{relatedBall}(M)=\operatorname{closedBall}(0,2M)
$$

is then used. Since $\|z_0\|<M<2M$, and similarly for $x_k$, $y_k$, and since $B_x<M<2M$, all these points lie in the open ball of radius $2M$. The lemma `Metric.ball_subset_interior_closedBall` converts that into membership in the interior of $\operatorname{relatedBall}(M)$. Also, $\operatorname{relatedBall}(M)$ is nonempty, closed, and convex, using respectively $0\in\operatorname{closedBall}(0,2M)$, `Metric.isClosed_closedBall`, and `convex_closedBall`.

The operator

$$
U=\operatorname{relatedOperator}(T,M)=T+N_{\operatorname{relatedBall}(M)}
$$

is introduced. To prove $U$ is maximal monotone, the proof applies `rockafellar_sum_maximal`. This theorem says that if $T$ is maximal monotone, $C$ is a nonempty closed convex set, and $T.\operatorname{dom}\cap\operatorname{int} C\neq\varnothing$, then $T+N_C$ is maximal monotone. Here $C=\operatorname{relatedBall}(M)$, and the required nonempty intersection holds because $z_0\in T.\operatorname{dom}$ and $z_0\in\operatorname{int}\operatorname{relatedBall}(M)$. Thus $U$ is maximal monotone.

Next the proof shows that $U.\operatorname{dom}$ is bounded. The lemma `related_operator_dom_subset_ball` states that

$$
(\operatorname{relatedOperator}(T,M)).\operatorname{dom}\subseteq \operatorname{relatedBall}(M).
$$

Since $\operatorname{relatedBall}(M)$ is a closed ball, it is bounded, and any subset of a bounded set is bounded. Hence $U.\operatorname{dom}$ is bounded. The theorem `maximal_monotone_surjective_of_bounded_domain` then applies to the maximal monotone operator $U$ with bounded domain. It gives two conclusions: $U.\operatorname{range}=H$ and $U.\operatorname{zeros}\neq\varnothing$. The proof only uses the second part, obtaining some $x_{\text{zero}}$ with $0\in U x_{\text{zero}}$.

The proof then builds HPE iterates for $U$. It must show

$$
A.v(k)\in \operatorname{epsilonEnlargement}(U,A.\varepsilon(k),A.\varepsilon_{\text{nonneg}}(k))(A.y(k)).
$$

By definition of `epsilonEnlargement`, this means that for every $z,w$ with $w\in U z$,

$$
-A.\varepsilon(k)\le \langle w-A.v(k),z-A.y(k)\rangle.
$$

Since $U z=T z+N_{\operatorname{relatedBall}(M)}z$, any $w\in U z$ decomposes as $w=u+\eta$ with $u\in T z$ and $\eta\in N_{\operatorname{relatedBall}(M)}z$. The HPE enlargement property of $A$ for $T$ gives

$$
-A.\varepsilon(k)\le \langle u-A.v(k),z-A.y(k)\rangle.
$$

Because $A.y(k)$ lies in the interior of $\operatorname{relatedBall}(M)$, the normal-cone inequality for $\eta$ gives

$$
\langle A.y(k)-z,\eta\rangle\le0,
$$

hence

$$
\langle \eta,z-A.y(k)\rangle\ge0.
$$

Adding these two inequalities yields

$$
-A.\varepsilon(k)\le \langle u+\eta-A.v(k),z-A.y(k)\rangle
=\langle w-A.v(k),z-A.y(k)\rangle.
$$

Thus $A.v(k)$ belongs to the $\varepsilon_k$-enlargement of $U$ at $A.y(k)$. Therefore the object $A_U$, obtained from $A$ by replacing the enlargement field with this proof, is an HPE iterate for $U$.

Now `hpe_weakly_converges_to_zero` is applied to the maximal monotone operator $U$, the HPE iterates $A_U$, and the already constructed zero $x_{\text{zero}}$ of $U$. This theorem says that a maximal monotone operator with an HPE iteration and at least one zero has an HPE weak limit that is itself a zero. It yields a point $\bar x$ such that

$$
0\in U\bar x
$$

and

$$
A.x(k)\rightharpoonup \bar x
$$

weakly as $k\to\infty$.

The weak limit $\bar x$ is then shown to lie in the closed ball of radius $B_x$. Indeed, each $A.x(k)$ satisfies $\|A.x(k)\|\le B_x$, so each lies in $\operatorname{closedBall}(0,B_x)$. This closed ball is closed and convex. The lemma `mem_of_tendsto_weakly_of_isClosed_convex` states that a weak limit of a sequence in a closed convex set again lies in that set. Hence

$$
\bar x\in\operatorname{closedBall}(0,B_x),
$$

so $\|\bar x\|\le B_x$. Since $B_x<M$, it follows that $\bar x$ lies in the interior of $\operatorname{relatedBall}(M)$.

Finally the proof uses $0\in U\bar x$. Unfolding $U=T+N_{\operatorname{relatedBall}(M)}$, this means

$$
0=u+\eta
$$

for some $u\in T\bar x$ and $\eta\in N_{\operatorname{relatedBall}(M)}\bar x$. Since $\bar x$ lies in the interior of $\operatorname{relatedBall}(M)$, the lemma `normalCone_zero_of_interior` applies: if a point is in the interior of a set and a vector is in the normal cone to that set at the point, then that vector is zero. Thus $\eta=0$. Then $u=0$, so $0\in T\bar x$. By `SetValuedOperator.mem_zeros_iff`, this means $\bar x\in T.\operatorname{zeros}$, contradicting the hypothesis $T.\operatorname{zeros}=\varnothing$. Therefore the original assumption that the range of $A.x$ is bounded was false, which proves

$$
\neg \operatorname{Bornology.IsBounded}\bigl(\operatorname{Set.range} A.x\bigr).
$$

The Lean tactics used along the way reflect the mathematical steps: `intro` begins the contradiction; `rcases` extracts witnesses from existential and conjunctive hypotheses; `have` records intermediate inequalities and membership facts; `let` introduces abbreviations such as $C,R,B_y,U$; `calc` chains equalities and inequalities; `rw`, `simpa`, and `change` unfold definitions such as `relatedOperator`, `relatedBall`, and `epsilonEnlargement`; `apply` and `exact` invoke the cited lemmas; `linarith` and `nlinarith` combine the displayed linear and quadratic inequalities; `positivity` proves nonnegativity of the constants; `gcongr` uses monotonicity of multiplication and addition; `abel` rearranges additive expressions; and `rfl` closes definitional equalities.

