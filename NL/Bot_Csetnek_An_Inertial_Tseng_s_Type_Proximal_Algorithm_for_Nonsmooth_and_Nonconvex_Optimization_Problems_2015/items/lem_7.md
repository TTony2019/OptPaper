## Source file
`Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015/items/lem_7.lean`

## Lean statement
```lean
theorem lemma_3_7_pair_cluster_points {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective) :
    (omega (pairSequence A)).Nonempty ∧
      omega (pairSequence A) ⊆ HCriticalSet P (A.M2 nu mu) ∧
      HCriticalSet P (A.M2 nu mu) = diagonalCriticalSet P ∧
      Tendsto (fun n : Nat => Metric.infDist (pairSequence A n) (omega (pairSequence A)))
        atTop (nhds 0) ∧
      IsCompact (omega (pairSequence A)) ∧
      IsConnected (omega (pairSequence A)) ∧
      (∃ c : EReal, ∀ z ∈ omega (pairSequence A), HFunction P (A.M2 nu mu) z = c)
```

## Statement explanation
The theorem `lemma_3_7_pair_cluster_points` is a paired-sequence version of the cluster-point lemma for the \(p\)-sequence of an inertial proximal algorithm. It is stated for a natural dimension \(m\), a problem datum \(P\) over the \(m\)-dimensional Euclidean space, an algorithm datum \(A\) for \(P\), and real parameters \(\nu,\mu\). Its two explicit hypotheses are

\[
\text{chosenAsInLemma33}(A,\nu,\mu)
\]

and

\[
\operatorname{CoerciveEReal}(P.\mathrm{objective}).
\]

Write \(p_n=A.p\,n\) and \(x_n=A.x\,n\), and let the paired sequence be

\[
S_n=\operatorname{pairSequence}(A)(n)=(p_n,x_n).
\]

The set \(\omega(z)\) is the set of sequential cluster points of the sequence \(z\). Thus \(\omega(A.p)\) is the set of cluster points of the \(p\)-sequence, while \(\omega(S)\) is the set of cluster points of the pair sequence \((p_n,x_n)\).

The conclusion is the conjunction of seven assertions:

\[
\begin{aligned}
&\omega(S)\neq \varnothing,\\
&\omega(S)\subseteq \operatorname{HCriticalSet}(P,A.\mathrm{M2}(\nu,\mu)),\\
&\operatorname{HCriticalSet}(P,A.\mathrm{M2}(\nu,\mu))
  =\operatorname{diagonalCriticalSet}(P),\\
&\operatorname{infDist}(S_n,\omega(S))\to 0,\\
&\omega(S)\text{ is compact},\\
&\omega(S)\text{ is connected},\\
&\exists c\in \overline{\mathbb R},\ \forall z\in\omega(S),\
  \operatorname{HFunction}(P,A.\mathrm{M2}(\nu,\mu),z)=c.
\end{aligned}
\]

The set `diagonalCriticalSet P` is defined as

\[
\{z\mid z_1=z_2\ \text{and}\ z_1\in \operatorname{criticalPoints}(P.\mathrm{objective})\}.
\]

The definition `HCriticalSet P M2` is exactly `diagonalCriticalSet P`, independently of the real parameter `M2`. Hence the third conjunct is a definitional identity. The second conjunct therefore says that every cluster point of the paired sequence is a diagonal point whose common coordinate is a critical point of the objective.

The function `HFunction P M2` is defined by applying `objectiveWithQuadratic P M2` to the two coordinates of \(z\). The proof uses the unfolding

\[
\operatorname{HFunction}(P,M2,z)
=
\operatorname{erealAddReal}
\bigl(P.\mathrm{objective}(z_1),\, M2\,\|z_1-z_2\|^2\bigr).
\]

On diagonal points \(z_1=z_2\), the quadratic penalty vanishes, so the value reduces to \(P.\mathrm{objective}(z_1)\). Thus the last conjunct says that this paired Lyapunov function is constant on the paired omega-limit set.

Overall, the theorem says: under the same parameter-choice and coercivity hypotheses that govern the one-coordinate cluster-point result, the paired sequence \((p_n,x_n)\) has nonempty, compact, connected omega-limit set; that set lies in the diagonal critical set; the distance from \(S_n\) to its omega-limit set tends to zero; and the quadratic Lyapunov function is constant on that omega-limit set.

## Lean proof
```lean
by
  have hchosen_copy := hchosen
  rcases hchosen_copy with ⟨_hnu, _hmu, _hstrict, _hM2ltM1⟩
  have h36 := lemma_3_6_cluster_points A nu mu hchosen hcoercive
  rcases h36 with
    ⟨hp_omega_nonempty, hp_crit, hp_dist, hp_compact, hp_connected, hp_const⟩
  have hboundedBelowReal :
      ∃ C : Real, ∀ x : EuclideanSpace m, (C : EReal) <= P.objective x :=
    objective_bddBelow_of_coercive hcoercive
  have hboundedBelow : BddBelow (Set.range P.objective) := by
    rcases hboundedBelowReal with ⟨C, hC⟩
    refine ⟨(C : EReal), ?_⟩
    rintro y ⟨x, rfl⟩
    exact hC x
  rcases lemma_3_4_decrease A nu mu hchosen hboundedBelowReal with
    ⟨hxp_sum, _hxx_sum, _hobj_conv⟩
  have hxp_vec :
      Tendsto (fun n : Nat => A.x n - A.p n) atTop
        (nhds (0 : EuclideanSpace m)) :=
    tendsto_of_summable_norm_sq_local hxp_sum
  let diagMap : EuclideanSpace m -> EuclideanSpace m × EuclideanSpace m :=
    fun p => (p, p)
  have hdiag_cont : Continuous diagMap := by
    rw [continuous_iff_continuousAt]
    intro p
    rw [ContinuousAt, Prod.tendsto_iff]
    exact ⟨tendsto_id, tendsto_id⟩
  have homega_eq :
      omega (pairSequence A) = diagMap '' omega A.p := by
    simpa [diagMap] using omega_pair_eq_diag_image (A := A) hxp_vec
  have homega_nonempty : (omega (pairSequence A)).Nonempty := by
    rcases hp_omega_nonempty with ⟨p, hp⟩
    refine ⟨diagMap p, ?_⟩
    rw [homega_eq]
    exact ⟨p, hp, rfl⟩
  have homega_compact : IsCompact (omega (pairSequence A)) := by
    rw [homega_eq]
    exact hp_compact.image hdiag_cont
  have homega_connected : IsConnected (omega (pairSequence A)) := by
    rw [homega_eq]
    exact hp_connected.image diagMap hdiag_cont.continuousOn
  have hsubset_diag : omega (pairSequence A) ⊆ diagonalCriticalSet P := by
    intro z hz
    exact ⟨omega_pair_diagonal hxp_vec hz, hp_crit (omega_pair_fst_mem hz)⟩
  have hdist_pair :
      Tendsto (fun n : Nat => Metric.infDist (pairSequence A n) (omega (pairSequence A)))
        atTop (nhds 0) := by
    have hxp_dist :
        Tendsto (fun n : Nat => dist (A.x n) (A.p n)) atTop (nhds 0) := by
      have hnorm :
          Tendsto (fun n : Nat => ‖A.x n - A.p n‖) atTop (nhds 0) :=
        tendsto_norm_of_summable_norm_sq_local hxp_sum
      simpa [dist_eq_norm] using hnorm
    rw [Metric.tendsto_atTop]
    intro eps heps
    have heps3 : 0 < eps / 3 := by positivity
    rcases (Metric.tendsto_atTop.1 hp_dist (eps / 3) heps3) with ⟨Np, hNp⟩
    rcases (Metric.tendsto_atTop.1 hxp_dist (eps / 3) heps3) with ⟨Nx, hNx⟩
    refine ⟨max Np Nx, ?_⟩
    intro n hn
    have hnNp : n ≥ Np := le_trans (le_max_left Np Nx) hn
    have hnNx : n ≥ Nx := le_trans (le_max_right Np Nx) hn
    have hp_inf_lt :
        Metric.infDist (A.p n) (omega A.p) < eps / 3 := by
      have h := hNp n hnNp
      simpa [Real.dist_eq, abs_of_nonneg Metric.infDist_nonneg] using h
    have hx_dist_lt : dist (A.x n) (A.p n) < eps / 3 := by
      have h := hNx n hnNx
      simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using h
    rcases (Metric.infDist_lt_iff hp_omega_nonempty).1 hp_inf_lt with
      ⟨q, hq, hpq_lt⟩
    have hq_pair : (q, q) ∈ omega (pairSequence A) := by
      rw [homega_eq]
      exact ⟨q, hq, rfl⟩
    have hpq_eps : dist (A.p n) q < eps := by
      nlinarith [hpq_lt, heps]
    have hxq_lt : dist (A.x n) q < eps := by
      have hxq_le : dist (A.x n) q ≤ dist (A.x n) (A.p n) + dist (A.p n) q :=
        dist_triangle (A.x n) (A.p n) q
      have hsum : dist (A.x n) (A.p n) + dist (A.p n) q < eps / 3 + eps / 3 :=
        add_lt_add hx_dist_lt hpq_lt
      have htwo : eps / 3 + eps / 3 < eps := by nlinarith [heps]
      exact lt_of_le_of_lt hxq_le (lt_trans hsum htwo)
    have hpair_dist_lt : dist (pairSequence A n) (q, q) < eps := by
      rw [pairSequence, Prod.dist_eq]
      exact max_lt hpq_eps hxq_lt
    have hinf_lt :
        Metric.infDist (pairSequence A n) (omega (pairSequence A)) < eps :=
      lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hq_pair) hpair_dist_lt
    simpa [Real.dist_eq, abs_of_nonneg Metric.infDist_nonneg] using hinf_lt
  have hH_const :
      ∃ c : EReal, ∀ z ∈ omega (pairSequence A), HFunction P (A.M2 nu mu) z = c := by
    rcases hp_const with ⟨cR, hcR⟩
    refine ⟨(cR : EReal), ?_⟩
    intro z hz
    have hzp : z.1 ∈ omega A.p := omega_pair_fst_mem hz
    have hzdiag : z.1 = z.2 := omega_pair_diagonal hxp_vec hz
    calc
      HFunction P (A.M2 nu mu) z
          = erealAddReal (P.objective z.1) ((A.M2 nu mu) * ‖z.1 - z.2‖ ^ 2) := by
              rfl
      _ = erealAddReal (P.objective z.1) 0 := by
              rw [hzdiag, sub_self]
              norm_num
      _ = P.objective z.1 := erealAddReal_zero _
      _ = (cR : EReal) := hcR z.1 hzp
  exact ⟨homega_nonempty, by simpa [HCriticalSet] using hsubset_diag, rfl,
    hdist_pair, homega_compact, homega_connected, hH_const⟩
```

## Proof explanation
The proof first obtains the one-coordinate cluster-point information for the \(p\)-sequence, then uses summability of \(\|x_n-p_n\|^2\) to transfer cluster points of \(p_n\) to diagonal cluster points of the pair sequence \((p_n,x_n)\), and finally verifies the seven conjuncts.

1. The proof begins with

   ```lean
   have hchosen_copy := hchosen
   rcases hchosen_copy with ⟨_hnu, _hmu, _hstrict, _hM2ltM1⟩
   ```

   This copies the parameter-choice hypothesis and destructs it into four components. All four component names begin with underscores, so none of them is used later. The original hypothesis `hchosen` remains available and is passed unchanged to Lemmas 3.4 and 3.6.

2. The proof applies `lemma_3_6_cluster_points A nu mu hchosen hcoercive`. That lemma states, for the \(p\)-sequence alone, that

   \[
   \begin{aligned}
   &\omega(A.p)\neq\varnothing,\\
   &\omega(A.p)\subseteq \operatorname{criticalPoints}(P.\mathrm{objective}),\\
   &\operatorname{infDist}(A.p_n,\omega(A.p))\to 0,\\
   &\omega(A.p)\text{ is compact},\\
   &\omega(A.p)\text{ is connected},\\
   &\exists c_R\in\mathbb R,\ \forall p\in\omega(A.p),\
     P.\mathrm{objective}(p)=(c_R:\overline{\mathbb R}).
   \end{aligned}
   \]

   The `rcases` command names these six facts `hp_omega_nonempty`, `hp_crit`, `hp_dist`, `hp_compact`, `hp_connected`, and `hp_const`. These are the source of the compactness, connectedness, criticality, distance convergence, and objective constancy that will be transferred to the pair sequence.

3. The proof invokes `objective_bddBelow_of_coercive hcoercive`. This gives a real lower bound: there exists \(C\in\mathbb R\) such that for every \(x\),

   \[
   (C:\overline{\mathbb R})\le P.\mathrm{objective}(x).
   \]

   The proof also forms `hboundedBelow : BddBelow (Set.range P.objective)`, converting that pointwise lower bound into a lower bound for the range. That intermediate fact is not used later; the real lower bound itself is what is needed.

   Next the proof applies `lemma_3_4_decrease A nu mu hchosen hboundedBelowReal`. The relevant part of that lemma gives

   \[
   \sum_n \|A.x\,n-A.p\,n\|^2<\infty,
   \qquad
   \sum_n \|A.x\,(n+1)-A.x\,n\|^2<\infty,
   \]

   and the convergence of \(P.\mathrm{objective}(A.p\,n)\) to some extended real. The proof names the first summable sequence `hxp_sum`; the other two conclusions are ignored. Only the summability of \(\|x_n-p_n\|^2\) is used.

4. From `hxp_sum`, the proof applies `tendsto_of_summable_norm_sq_local` to the sequence \(z_n=A.x\,n-A.p\,n\). That lemma says that if \(\sum_n\|z_n\|^2<\infty\), then \(z_n\to 0\). Hence

   \[
   A.x\,n-A.p\,n\to 0.
   \]

   This is the fact `hxp_vec`. It expresses that the two coordinates \(x_n\) and \(p_n\) become asymptotically equal.

5. The proof defines the diagonal map

   \[
   d(p)=(p,p)
   \]

   as `diagMap`, and proves that it is continuous. To do so it rewrites `Continuous diagMap` using `continuous_iff_continuousAt`, so it suffices to prove continuity at every point \(p\). For fixed \(p\), it rewrites `ContinuousAt` and then uses `Prod.tendsto_iff`, which says convergence in a product space is coordinatewise convergence. Both coordinates of \(d\) are the identity map, so `tendsto_id` proves the two coordinate limits. Thus \(d\) is continuous.

6. The proof uses `omega_pair_eq_diag_image` with `hxp_vec`. This theorem states that if \(A.x\,n-A.p\,n\to 0\), then

   \[
   \omega(\operatorname{pairSequence}(A))
   =
   d\bigl(\omega(A.p)\bigr).
   \]

   In words, the cluster points of the pair sequence \((p_n,x_n)\) are exactly the diagonal pairs \((q,q)\) where \(q\) is a cluster point of \(p_n\). The proof records this as `homega_eq`, using `simpa [diagMap]`.

7. Nonemptiness of \(\omega(S)\) follows from nonemptiness of \(\omega(A.p)\). If \(p\in\omega(A.p)\), then \(d(p)=(p,p)\in d(\omega(A.p))=\omega(S)\). This proves `homega_nonempty`.

8. Compactness of \(\omega(S)\) follows by rewriting \(\omega(S)=d(\omega(A.p))\). Since \(\omega(A.p)\) is compact by Lemma 3.6 and \(d\) is continuous, the continuous image \(d(\omega(A.p))\) is compact. This is the step `hp_compact.image hdiag_cont`.

9. Connectedness is similar. A continuous image of a connected set is connected. Since \(\omega(A.p)\) is connected and \(d\) is continuous, \(d(\omega(A.p))=\omega(S)\) is connected. This gives `homega_connected`.

10. To prove \(\omega(S)\subseteq \operatorname{diagonalCriticalSet}(P)\), the proof takes arbitrary \(z\in\omega(S)\). Two cited facts are used:

    - `omega_pair_diagonal hxp_vec hz`: since \(x_n-p_n\to0\), every cluster point \(z=(z_1,z_2)\) of the pair sequence satisfies \(z_1=z_2\).
    - `omega_pair_fst_mem hz`: the first coordinate satisfies \(z_1\in\omega(A.p)\).

    From Lemma 3.6, `hp_crit` gives \(\omega(A.p)\subseteq \operatorname{criticalPoints}(P.\mathrm{objective})\). Therefore \(z_1\in\operatorname{criticalPoints}(P.\mathrm{objective})\). Together with \(z_1=z_2\), this means \(z\in\operatorname{diagonalCriticalSet}(P)\). This is `hsubset_diag`.

11. The distance-convergence conjunct is

    \[
    \operatorname{infDist}(S_n,\omega(S))\to 0.
    \]

    The proof first obtains two auxiliary limits. From `hxp_sum` and `tendsto_norm_of_summable_norm_sq_local`, it gets

    \[
    \|x_n-p_n\|\to 0.
    \]

    Using `dist_eq_norm`, this becomes

    \[
    \operatorname{dist}(x_n,p_n)\to 0.
    \]

    Lemma 3.6 gives

    \[
    \operatorname{infDist}(p_n,\omega(A.p))\to 0.
    \]

    Now fix \(\varepsilon>0\). Since \(\varepsilon/3>0\), the two limits provide \(N_p\) and \(N_x\) such that for \(n\ge N_p\),

    \[
    \operatorname{infDist}(p_n,\omega(A.p))<\varepsilon/3,
    \]

    and for \(n\ge N_x\),

    \[
    \operatorname{dist}(x_n,p_n)<\varepsilon/3.
    \]

    Taking \(N=\max(N_p,N_x)\), both inequalities hold for \(n\ge N\).

    Because \(\omega(A.p)\) is nonempty, `Metric.infDist_lt_iff` gives a point \(q\in\omega(A.p)\) with

    \[
    \operatorname{dist}(p_n,q)<\varepsilon/3.
    \]

    Since \(q\in\omega(A.p)\), the pair \((q,q)\) lies in \(\omega(S)\) by the diagonal-image description `homega_eq`.

    The triangle inequality gives

    \[
    \operatorname{dist}(x_n,q)
    \le \operatorname{dist}(x_n,p_n)+\operatorname{dist}(p_n,q)
    < \frac{\varepsilon}{3}+\frac{\varepsilon}{3}
    < \varepsilon.
    \]

    Also \(\operatorname{dist}(p_n,q)<\varepsilon\). Using `Prod.dist_eq`, the distance between the pairs is the maximum of the coordinate distances, so

    \[
    \operatorname{dist}(S_n,(q,q))<\varepsilon.
    \]

    Since \((q,q)\in\omega(S)\), the definition of infimum distance gives

    \[
    \operatorname{infDist}(S_n,\omega(S))
    \le \operatorname{dist}(S_n,(q,q))
    < \varepsilon.
    \]

    Finally, because \(\operatorname{infDist}\) is nonnegative, this is the same as

    \[
    \operatorname{dist}\bigl(\operatorname{infDist}(S_n,\omega(S)),0\bigr)<\varepsilon.
    \]

    Therefore \(\operatorname{infDist}(S_n,\omega(S))\to 0\), proving `hdist_pair`.

12. The final substantive conjunct is the constancy of `HFunction`. Lemma 3.6 provides a real number \(c_R\) such that

    \[
    P.\mathrm{objective}(p)=(c_R:\overline{\mathbb R})
    \]

    for every \(p\in\omega(A.p)\).

    For arbitrary \(z\in\omega(S)\), the proof uses:

    - `omega_pair_fst_mem hz` to get \(z_1\in\omega(A.p)\);
    - `omega_pair_diagonal hxp_vec hz` to get \(z_1=z_2\).

    It then computes

    \[
    \begin{aligned}
    \operatorname{HFunction}(P,A.\mathrm{M2}(\nu,\mu),z)
    &=
    \operatorname{erealAddReal}
    \bigl(P.\mathrm{objective}(z_1),
      A.\mathrm{M2}(\nu,\mu)\|z_1-z_2\|^2\bigr)\\
    &=
    \operatorname{erealAddReal}
    \bigl(P.\mathrm{objective}(z_1),0\bigr)\\
    &=
    P.\mathrm{objective}(z_1)\\
    &=
    (c_R:\overline{\mathbb R}).
    \end{aligned}
    \]

    The first equality is the definitional unfolding of `HFunction`. The second uses \(z_1=z_2\), so \(z_1-z_2=0\) and the quadratic penalty is \(0\). The third uses `erealAddReal_zero`, which states that for every extended real \(a\),

    \[
    \operatorname{erealAddReal}(a,0)=a.
    \]

    The last equality uses the constancy result from Lemma 3.6 applied to \(z_1\in\omega(A.p)\). Thus \(c=(c_R:\overline{\mathbb R})\) witnesses that `HFunction` is constant on \(\omega(S)\).

13. Finally, the proof assembles the seven conclusions:

    \[
    \langle
    \text{homega_nonempty},
    \text{subset into } \operatorname{HCriticalSet},
    \operatorname{HCriticalSet}=\operatorname{diagonalCriticalSet},
    \text{hdist_pair},
    \text{homega_compact},
    \text{homega_connected},
    \text{hH_const}
    \rangle.
    \]

    The subset `hsubset_diag` was stated for `diagonalCriticalSet P`; the command `simpa [HCriticalSet]` rewrites it into a subset of `HCriticalSet P (A.M2 nu mu)`, using the definition of `HCriticalSet`. The equality \(\operatorname{HCriticalSet}(P,A.\mathrm{M2}(\nu,\mu))=\operatorname{diagonalCriticalSet}(P)\) is proved by `rfl`, again because it is definitional. Thus the proof establishes the paired cluster-point theorem.

