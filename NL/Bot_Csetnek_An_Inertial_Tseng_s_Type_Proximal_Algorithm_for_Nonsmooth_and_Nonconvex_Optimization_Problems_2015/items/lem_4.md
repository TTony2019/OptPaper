## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_4.lean`

## Lean statement
```lean
theorem lemma_3_4_decrease {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hchosen : chosenAsInLemma33 A nu mu)
    (hbounded : ∃ C : Real, ∀ x : EuclideanSpace m, (C : EReal) <= P.objective x) :
    Summable (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) ∧
      Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖ ^ 2) ∧
      ∃ l : EReal,
        Tendsto (fun n : Nat => P.objective (A.p n)) atTop (nhds l)
```

## Statement explanation
The theorem is set in a Euclidean space of dimension $m$. The data $P$ provide the objective function $P.objective : \mathbb R^m \to \overline{\mathbb R}$, where $\overline{\mathbb R}$ is the extended real line. The data $A$ provide two sequences, written here as

$$
x_n = A.x(n), \qquad p_n = A.p(n),
$$

together with the algorithm parameters such as $A.\lambda(n)$, $A.\mathrm{lambdaUpper}$, $A.\mathrm{lambdaLower}$, and the constants $A.M1(\nu,\mu)$, $A.M2(\nu,\mu)$. The real parameters $\nu$ and $\mu$ are assumed to satisfy the hypotheses encoded by `chosenAsInLemma33 A nu mu`. In the proof this hypothesis is unpacked into the components that are visible there: $0<\nu$, $0<\mu$, an additional strict condition which is not used, and the inequality

$$
A.M2(\nu,\mu) < A.M1(\nu,\mu).
$$

The second hypothesis says that the objective is bounded below by some real constant $C$:

$$
(C : \overline{\mathbb R}) \le P.objective(x) \qquad\text{for every }x\in \mathbb R^m.
$$

This is a lower bound in the extended-real sense; no finiteness of $P.objective$ is assumed by the statement itself.

For a real number $M$, the proof uses the auxiliary quadratic perturbation

$$
Q_M(z,w) = P.objective(z) \oplus M\|z-w\|^2,
$$

where $\oplus$ denotes addition in the extended reals. When $z$ lies in the effective domain of $P.objective$, meaning that $P.objective(z)$ is neither $+\infty$ nor $-\infty$, this quantity is finite and satisfies

$$
Q_M(z,w) = \bigl((P.objective(z)).\operatorname{toReal} + M\|z-w\|^2 : \overline{\mathbb R}\bigr),
$$

and consequently

$$
(Q_M(z,w)).\operatorname{toReal}
=
(P.objective(z)).\operatorname{toReal} + M\|z-w\|^2.
$$

These are exactly the contents of the cited lemmas `objectiveWithQuadratic_eq_coe` and `objectiveWithQuadratic_toReal_eq`.

The conclusion of the theorem is the conjunction of three statements:

$$
\sum_{n=0}^{\infty}\|x_n-p_n\|^2 < \infty,
$$

$$
\sum_{n=0}^{\infty}\|x_{n+1}-x_n\|^2 < \infty,
$$

and there exists some extended real $l\in\overline{\mathbb R}$ such that

$$
P.objective(p_n) \longrightarrow l
\qquad\text{in }\overline{\mathbb R}.
$$

Thus the theorem says that, under the parameter choice from Lemma 3.3 and a global real lower bound on the objective, the distances between the two algorithm sequences $x_n$ and $p_n$ are square-summable, the successive differences of the sequence $x_n$ are also square-summable, and the objective values along the auxiliary sequence $p_n$ converge in the extended-real topology.

## Lean proof
```lean
by
  rcases hchosen with ⟨hnu, hmu, _hstrict, hM2ltM1⟩
  let M1 : Real := A.M1 nu mu
  let M2 : Real := A.M2 nu mu
  let D : Real := M1 - M2
  have hDpos : 0 < D := by
    dsimp [D, M1, M2]
    nlinarith [hM2ltM1]
  have hM2_nonneg : 0 <= M2 := by
    dsimp [M2]
    exact m2_nonneg A hnu hmu
  let a : Nat -> Real := fun k =>
    (objectiveWithQuadratic P M2 (A.p (k + 2)) (A.x (k + 2))).toReal
  let b : Nat -> Real := fun k =>
    D * ‖A.x (k + 3) - A.p (k + 3)‖ ^ 2
  have hb_nonneg : ∀ k, 0 <= b k := by
    intro k
    dsimp [b]
    exact mul_nonneg (le_of_lt hDpos) (sq_nonneg _)
  have h32 :
      ∀ n, 2 <= n ->
        objectiveWithQuadratic P M1 (A.p n) (A.x n) <=
          objectiveWithQuadratic P M2 (A.p (n - 1)) (A.x (n - 1)) := by
    intro n hn
    dsimp [M1, M2]
    exact lemma_3_2_descent A nu mu hnu hmu n hn
  have ha_bddBelow : BddBelow (Set.range a) := by
    rcases hbounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨k, rfl⟩
    have hp_eff : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom A (by omega)
    have hobj_coe :
        P.objective (A.p (k + 2)) =
          (((P.objective (A.p (k + 2))).toReal : Real) : EReal) := by
      exact (EReal.coe_toReal
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).1
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).2).symm
    have hobj_lower_real : C <= (P.objective (A.p (k + 2))).toReal := by
      have h := hC (A.p (k + 2))
      rw [hobj_coe] at h
      exact EReal.coe_le_coe_iff.mp h
    have hquad_nonneg : 0 <= M2 * ‖A.p (k + 2) - A.x (k + 2)‖ ^ 2 :=
      mul_nonneg hM2_nonneg (sq_nonneg _)
    dsimp [a]
    rw [objectiveWithQuadratic_toReal_eq hp_eff]
    nlinarith
  have hdesc : ∀ k, a (k + 1) + b k <= a k := by
    intro k
    have hk : 2 <= k + 3 := by omega
    have hd := h32 (k + 3) hk
    have hpred : k + 3 - 1 = k + 2 := by omega
    rw [hpred] at hd
    have hp_eff_new : A.p (k + 3) ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom A (by omega)
    have hp_eff_old : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom A (by omega)
    have hleft_coe :=
      objectiveWithQuadratic_eq_coe (P := P) (M := M1)
        (x := A.p (k + 3)) (y := A.x (k + 3)) hp_eff_new
    have hright_coe :=
      objectiveWithQuadratic_eq_coe (P := P) (M := M2)
        (x := A.p (k + 2)) (y := A.x (k + 2)) hp_eff_old
    rw [hleft_coe, hright_coe] at hd
    have hd_real :
        (P.objective (A.p (k + 3))).toReal +
            M1 * ‖A.p (k + 3) - A.x (k + 3)‖ ^ 2
          <=
          (P.objective (A.p (k + 2))).toReal +
            M2 * ‖A.p (k + 2) - A.x (k + 2)‖ ^ 2 :=
      EReal.coe_le_coe_iff.mp hd
    dsimp [a, b]
    rw [objectiveWithQuadratic_toReal_eq hp_eff_new,
      objectiveWithQuadratic_toReal_eq hp_eff_old]
    rw [norm_sub_rev (A.x (k + 3)) (A.p (k + 3))]
    dsimp [D] at *
    nlinarith [hd_real]
  rcases lemma_2_2_descent_summable a b hb_nonneg ha_bddBelow hdesc with
    ⟨_ha_anti, ⟨la, ha_tendsto⟩, hb_summable⟩
  have htail_xp : Summable (fun k : Nat => ‖A.x (k + 3) - A.p (k + 3)‖ ^ 2) := by
    have hb_div := hb_summable.mul_left D⁻¹
    convert hb_div using 1
    ext k
    dsimp [b]
    field_simp [ne_of_gt hDpos]
  have hxp : Summable (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) :=
    summable_of_tail3_summable htail_xp
  have hinc : Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖ ^ 2) := by
    have hinc_tail :
        Summable (fun k : Nat => ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2) := by
      let Cstep : Real := (1 + A.lambdaUpper * P.Lgrad_h) ^ 2
      have hdom :
          ∀ k : Nat,
            ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2
              <= Cstep * ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2 := by
        intro k
        have hn : 1 <= k + 1 := by omega
        have h14 := relation14_norm_step A (k + 1) hn
        have hlam := A.lambda_bounds (k + 1) hn
        have hLh_nonneg : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
        have hfactor_nonneg :
            0 <= 1 + A.lambda (k + 1) * P.Lgrad_h := by
          have hlam_nonneg : 0 <= A.lambda (k + 1) :=
            le_trans (le_of_lt A.lambdaLower_pos) hlam.1
          nlinarith [mul_nonneg hlam_nonneg hLh_nonneg]
        have hfactor_upper_nonneg :
            0 <= 1 + A.lambdaUpper * P.Lgrad_h := by
          nlinarith [mul_nonneg (le_of_lt A.lambdaUpper_pos) hLh_nonneg]
        have hfactor_le :
            1 + A.lambda (k + 1) * P.Lgrad_h <=
              1 + A.lambdaUpper * P.Lgrad_h := by
          have hmul := mul_le_mul_of_nonneg_right hlam.2 hLh_nonneg
          nlinarith
        have hsquare1 :
            ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2 <=
              ((1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := by
          have hprod_nonneg :
              0 <= (1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖ := by
            nlinarith [h14, norm_nonneg (A.x ((k + 1) + 1) - A.x (k + 1))]
          exact sq_le_sq'
            (le_trans (neg_nonpos.mpr hprod_nonneg)
              (norm_nonneg (A.x ((k + 1) + 1) - A.x (k + 1))))
            h14
        have hsquare2 :
            ((1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 <=
              ((1 + A.lambdaUpper * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := by
          have hmul_le := mul_le_mul_of_nonneg_right hfactor_le
            (norm_nonneg (A.x (k + 1) - A.p (k + 1)))
          have hprod_upper_nonneg :
              0 <= (1 + A.lambdaUpper * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖ :=
            mul_nonneg hfactor_upper_nonneg
              (norm_nonneg (A.x (k + 1) - A.p (k + 1)))
          have hprod_nonneg :
              0 <= (1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖ :=
            mul_nonneg hfactor_nonneg
              (norm_nonneg (A.x (k + 1) - A.p (k + 1)))
          exact sq_le_sq'
            (le_trans (neg_nonpos.mpr hprod_upper_nonneg) hprod_nonneg)
            hmul_le
        calc
          ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2
              <= ((1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := hsquare1
          _ <= ((1 + A.lambdaUpper * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := hsquare2
          _ = Cstep * ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2 := by
                dsimp [Cstep]
                ring
      have hmajor :
          Summable (fun k : Nat => Cstep * ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2) := by
        have hxp_tail : Summable (fun k : Nat => ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2) :=
          (summable_nat_add_iff (G := Real) 1).mpr hxp
        exact hxp_tail.mul_left Cstep
      exact Summable.of_nonneg_of_le
        (fun k => sq_nonneg _)
        hdom
        hmajor
    exact (summable_nat_add_iff (G := Real) 1).mp hinc_tail
  have hobj :
      ∃ l : EReal, Tendsto (fun n : Nat => P.objective (A.p n)) atTop (nhds l) := by
    have hxpto0 :
        Tendsto (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) atTop (nhds 0) :=
      hxp.tendsto_atTop_zero
    have hxpto0_tail :
        Tendsto (fun k : Nat => ‖A.x (k + 2) - A.p (k + 2)‖ ^ 2) atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat 2).mpr hxpto0
    have hquad_to0 :
        Tendsto (fun k : Nat => M2 * ‖A.p (k + 2) - A.x (k + 2)‖ ^ 2) atTop (nhds 0) := by
      have htmp :
          Tendsto (fun k : Nat => M2 * ‖A.x (k + 2) - A.p (k + 2)‖ ^ 2) atTop
            (nhds (M2 * 0)) :=
        tendsto_const_nhds.mul hxpto0_tail
      simpa [norm_sub_rev] using htmp
    have hobjReal_tail :
        Tendsto (fun k : Nat => (P.objective (A.p (k + 2))).toReal) atTop (nhds la) := by
      have hsub := ha_tendsto.sub hquad_to0
      have hsub' :
          Tendsto (fun x => a x - M2 * ‖A.p (x + 2) - A.x (x + 2)‖ ^ 2) atTop
            (nhds la) := by
        simpa using hsub
      convert hsub' using 1
      ext k
      have hp_eff : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
        p_objective_effectiveDom A (by omega)
      dsimp [a]
      rw [objectiveWithQuadratic_toReal_eq hp_eff]
      rw [norm_sub_rev (A.p (k + 2)) (A.x (k + 2))]
      ring
    have hobjEReal_tail :
        Tendsto (fun k : Nat => P.objective (A.p (k + 2))) atTop (nhds (la : EReal)) := by
      have hcoe :
          Tendsto (fun k : Nat => ((P.objective (A.p (k + 2))).toReal : EReal))
            atTop (nhds (la : EReal)) :=
        EReal.tendsto_coe.2 hobjReal_tail
      convert hcoe using 1
      ext k
      have hp_eff : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
        p_objective_effectiveDom A (by omega)
      exact (EReal.coe_toReal
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).1
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).2).symm
    exact ⟨(la : EReal), tendsto_of_tail2_tendsto hobjEReal_tail⟩
  exact ⟨hxp, hinc, hobj⟩
```

## Proof explanation
The proof begins by unpacking the hypothesis `hchosen` with `rcases`. This gives the positivity assumptions $0<\nu$ and $0<\mu$, an unused strict condition, and the inequality

$$
A.M2(\nu,\mu) < A.M1(\nu,\mu).
$$

Then `let` introduces the abbreviations

$$
M_1 = A.M1(\nu,\mu), \qquad M_2 = A.M2(\nu,\mu), \qquad D = M_1-M_2.
$$

From $M_2<M_1$, the tactic `nlinarith` proves

$$
0<D.
$$

The cited result `m2_nonneg A hnu hmu` is then used to obtain

$$
0\le M_2.
$$

This is the concrete content of `m2_nonneg`: for positive $\nu,\mu$, the algorithm constant $M_2$ is nonnegative.

Next the proof defines two real sequences:

$$
a_k = (Q_{M_2}(p_{k+2},x_{k+2})).\operatorname{toReal},
$$

$$
b_k = D\|x_{k+3}-p_{k+3}\|^2.
$$

The nonnegativity of $b$ follows immediately from $D>0$ and the fact that a square is nonnegative. This is the step `hb_nonneg`, where `intro k` introduces an arbitrary index and `nlinarith`/simplification verify the inequality.

The proof then specializes Lemma 3.2, cited as `lemma_3_2_descent`. That lemma gives the descent inequality

$$
Q_{M_1}(p_n,x_n) \le Q_{M_2}(p_{n-1},x_{n-1})
\qquad (n\ge 2).
$$

In the proof this is stored as `h32`. It is the decisive relation that compares the quadratic objective with parameter $M_1$ at the new point to the quadratic objective with parameter $M_2$ at the previous point.

The next step is to show that $a$ is bounded below. The hypothesis `hbounded` supplies a real $C$ such that

$$
(C:\overline{\mathbb R}) \le P.objective(x)
$$

for every $x$. For each $k$, the cited result `p_objective_effectiveDom` gives

$$
p_{k+2} \in \operatorname{effectiveDom}(P.objective),
$$

because $k+2\ge 1$. Membership in the effective domain means, by `ERealFunction.mem_effectiveDom_iff`, that

$$
P.objective(p_{k+2}) \neq \top
\quad\text{and}\quad
P.objective(p_{k+2}) \neq \bot.
$$

The extended-real lemma `EReal.coe_toReal` then yields

$$
P.objective(p_{k+2})
=
\bigl((P.objective(p_{k+2})).\operatorname{toReal} : \overline{\mathbb R}\bigr).
$$

Using the lower bound $C\le P.objective(p_{k+2})$ and the lemma `EReal.coe_le_coe_iff`, the proof extracts the real inequality

$$
C \le (P.objective(p_{k+2})).\operatorname{toReal}.
$$

Since $0\le M_2$ and $\|p_{k+2}-x_{k+2}\|^2\ge 0$, the quadratic term

$$
M_2\|p_{k+2}-x_{k+2}\|^2
$$

is nonnegative. Rewriting $a_k$ using `objectiveWithQuadratic_toReal_eq`, namely

$$
a_k
=
(P.objective(p_{k+2})).\operatorname{toReal}
+
M_2\|p_{k+2}-x_{k+2}\|^2,
$$

the proof concludes

$$
C\le a_k.
$$

Thus the whole range of $a$ is bounded below by $C$, which is the assertion `BddBelow (Set.range a)`.

The proof now establishes the key descent inequality for $a$ and $b$:

$$
a_{k+1}+b_k \le a_k
\qquad\text{for every }k.
$$

For a fixed $k$, it applies the descent inequality `h32` at $n=k+3$:

$$
Q_{M_1}(p_{k+3},x_{k+3})
\le
Q_{M_2}(p_{k+2},x_{k+2}).
$$

Both $p_{k+3}$ and $p_{k+2}$ lie in the effective domain of $P.objective$, again by `p_objective_effectiveDom`. Therefore the cited lemma `objectiveWithQuadratic_eq_coe` rewrites both sides as extended-real coercions of real numbers. The inequality becomes

$$
\bigl((P.objective(p_{k+3})).\operatorname{toReal}
+
M_1\|p_{k+3}-x_{k+3}\|^2 : \overline{\mathbb R}\bigr)
\le
\bigl((P.objective(p_{k+2})).\operatorname{toReal}
+
M_2\|p_{k+2}-x_{k+2}\|^2 : \overline{\mathbb R}\bigr).
$$

Applying `EReal.coe_le_coe_iff` removes the coercions and gives the corresponding real inequality:

$$
(P.objective(p_{k+3})).\operatorname{toReal}
+
M_1\|p_{k+3}-x_{k+3}\|^2
\le
(P.objective(p_{k+2})).\operatorname{toReal}
+
M_2\|p_{k+2}-x_{k+2}\|^2.
$$

Now the proof unfolds the definitions of $a$ and $b$, uses `objectiveWithQuadratic_toReal_eq`, uses the symmetry of the norm $\|x_{k+3}-p_{k+3}\|=\|p_{k+3}-x_{k+3}\|$, and rewrites $D=M_1-M_2$. The left side $a_{k+1}+b_k$ becomes exactly

$$
(P.objective(p_{k+3})).\operatorname{toReal}
+
M_1\|p_{k+3}-x_{k+3}\|^2,
$$

while $a_k$ is

$$
(P.objective(p_{k+2})).\operatorname{toReal}
+
M_2\|p_{k+2}-x_{k+2}\|^2.
$$

Thus `nlinarith` closes the goal $a_{k+1}+b_k\le a_k$.

At this point the abstract descent lemma `lemma_2_2_descent_summable` is applied to $a$ and $b$. Its statement says that if $b_k\ge 0$ for all $k$, if $a$ is bounded below, and if

$$
a_{k+1}+b_k\le a_k
$$

for all $k$, then $a$ is antitone, $a$ converges to some real limit, and $b$ is summable. The proof invokes it and obtains

$$
a_k \longrightarrow l_a
$$

for some real $l_a$, and

$$
\sum_k b_k < \infty.
$$

The antitonicity conclusion is kept only implicitly.

From the summability of $b$, the proof derives the first summability claim. Since

$$
b_k = D\|x_{k+3}-p_{k+3}\|^2
$$

and $D>0$, multiplying the summable series by $D^{-1}$ gives

$$
\sum_k \|x_{k+3}-p_{k+3}\|^2 < \infty.
$$

This is done using `hb_summable.mul_left D⁻¹` and `field_simp`, which uses $D\neq 0$. Then the cited result `summable_of_tail3_summable` removes the three-index shift: if

$$
\sum_k \|x_{k+3}-p_{k+3}\|^2
$$

is finite, then

$$
\sum_n \|x_n-p_n\|^2
$$

is finite. This proves the first conjunct of the theorem.

The proof next establishes the second summability claim,

$$
\sum_n \|x_{n+1}-x_n\|^2 < \infty.
$$

It begins by proving a one-step estimate. Let $L=P.Lgrad_h$ and

$$
C_{\text{step}} = (1+A.\mathrm{lambdaUpper}\cdot L)^2.
$$

For each $k$, the cited relation `relation14_norm_step` at $n=k+1$ gives

$$
\|x_{k+2}-x_{k+1}\|
\le
(1+\lambda_{k+1}L)\|x_{k+1}-p_{k+1}\|.
$$

The proof also uses `A.lambda_bounds (k+1)`, whose visible consequences are that $\lambda_{k+1}$ lies between the algorithm’s lower and upper bounds; in particular the proof uses

$$
\mathrm{lambdaLower} \le \lambda_{k+1},
\qquad
\lambda_{k+1}\le \mathrm{lambdaUpper}.
$$

Since $A.\mathrm{lambdaLower}>0$, $A.\mathrm{lambdaUpper}>0$, and $L\ge 0$ from `P.h_lipschitz_gradient.1`, it follows that

$$
0\le 1+\lambda_{k+1}L
$$

and

$$
0\le 1+\mathrm{lambdaUpper} L.
$$

Moreover, because $\lambda_{k+1}\le \mathrm{lambdaUpper}$ and $L\ge 0$,

$$
1+\lambda_{k+1}L \le 1+\mathrm{lambdaUpper} L.
$$

Squaring the relation (14) inequality and using nonnegativity gives

$$
\|x_{k+2}-x_{k+1}\|^2
\le
\bigl((1+\lambda_{k+1}L)\|x_{k+1}-p_{k+1}\|\bigr)^2.
$$

Then the factor comparison yields

$$
\bigl((1+\lambda_{k+1}L)\|x_{k+1}-p_{k+1}\|\bigr)^2
\le
\bigl((1+\mathrm{lambdaUpper} L)\|x_{k+1}-p_{k+1}\|\bigr)^2.
$$

By `ring`, the right-hand side is

$$
C_{\text{step}}\|x_{k+1}-p_{k+1}\|^2.
$$

Hence for every $k$,

$$
\|x_{k+2}-x_{k+1}\|^2
\le
C_{\text{step}}\|x_{k+1}-p_{k+1}\|^2.
$$

Since the sequence $\|x_n-p_n\|^2$ is summable, its shift $\|x_{k+1}-p_{k+1}\|^2$ is summable by `summable_nat_add_iff`. Multiplying by the constant $C_{\text{step}}$ preserves summability, so

$$
\sum_k C_{\text{step}}\|x_{k+1}-p_{k+1}\|^2 < \infty.
$$

The comparison test `Summable.of_nonneg_of_le` then implies

$$
\sum_k \|x_{k+2}-x_{k+1}\|^2 < \infty.
$$

Finally, `summable_nat_add_iff` once more removes the one-index shift and gives

$$
\sum_n \|x_{n+1}-x_n\|^2 < \infty.
$$

This is the second conjunct.

The last part proves convergence of the objective values along $p_n$. From the summability of

$$
\|x_n-p_n\|^2
$$

the terms tend to zero:

$$
\|x_n-p_n\|^2 \longrightarrow 0.
$$

This uses `Summable.tendsto_atTop_zero`. Shifting by two gives

$$
\|x_{k+2}-p_{k+2}\|^2 \longrightarrow 0,
$$

using the fact that shifting a sequence does not change its limit at infinity. Multiplying by $M_2$ gives

$$
M_2\|p_{k+2}-x_{k+2}\|^2 \longrightarrow 0,
$$

where the norm symmetry $\|p_{k+2}-x_{k+2}\|=\|x_{k+2}-p_{k+2}\|$ is used.

Recall that $a_k\to l_a$. By the definition of $a_k$ and the effective-domain rewrite,

$$
a_k
=
(P.objective(p_{k+2})).\operatorname{toReal}
+
M_2\|p_{k+2}-x_{k+2}\|^2.
$$

Subtracting the vanishing quadratic term gives

$$
(P.objective(p_{k+2})).\operatorname{toReal}
\longrightarrow l_a.
$$

This uses continuity of subtraction in the reals: the difference of the convergent sequence $a_k$ and the null sequence of quadratic terms converges to $l_a$. The proof uses `convert` and `ring` here to identify the difference pointwise with the real part of the objective.

Since each $p_{k+2}$ is in the effective domain of $P.objective$, the extended-real value $P.objective(p_{k+2})$ is exactly the coercion of its real part:

$$
P.objective(p_{k+2})
=
\bigl((P.objective(p_{k+2})).\operatorname{toReal} : \overline{\mathbb R}\bigr).
$$

Therefore `EReal.tendsto_coe` upgrades the real convergence to extended-real convergence:

$$
P.objective(p_{k+2}) \longrightarrow (l_a : \overline{\mathbb R})
$$

in $\overline{\mathbb R}$. Finally, the cited result `tendsto_of_tail2_tendsto` removes the two-index shift and yields

$$
P.objective(p_n) \longrightarrow (l_a : \overline{\mathbb R}).
$$

Thus the required extended-real limit exists.

The final line `exact ⟨hxp, hinc, hobj⟩` assembles the three conclusions: summability of $\|x_n-p_n\|^2$, summability of $\|x_{n+1}-x_n\|^2$, and convergence of $P.objective(p_n)$ in the extended reals.

