## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_4.lean`

## Lean statement
```lean
theorem proposition6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) :
    Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds (sInf (Set.range Θ))) ∧
    (∀ q, IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k)) (toWeakSpace ℝ H q) →
      q ∈ Optimization.argminSet Θ) ∧
    (Optimization.argminSet Θ = ∅ → Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop Filter.atTop)
```

## Statement explanation
`proposition6` is a theorem about a complete real inner product space $H$, i.e. a real Hilbert space. The data are two extended-real-valued functions $\phi,\Theta:H\to\overline{\mathbb R}$, a real-valued function $\psi:H\to\mathbb R$, a map $\mathrm{gradPsi}:H\to H$, real parameters $a,b,\lambda,L_\psi$, and two sequences $u,y:\mathbb N\to H$. The hypotheses `hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi` and `hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y` are the standing assumptions of the inertial forward-backward method. The proof uses in particular that $\Theta$ has convex epigraph, that $\Theta$ is bounded below by a real constant, that $\Theta$ is related to $\phi$ and $\psi$ by the identity encoded in `hH.theta_eq`, and that $b>0$ and $\lambda>0$.

The conclusion is a conjunction of three statements.

First, the sequence of objective values converges, in the extended-real topology, to the infimum of the range of $\Theta$:

$$
\Theta(u_k)\longrightarrow \inf_{x\in H}\Theta(x)
\quad\text{as } k\to\infty .
$$

Second, every weak sequential cluster point of the sequence $(u_k)$ is a minimizer of $\Theta$. More precisely, if $q$ is such that some strictly increasing subsequence of $(u_k)$ converges weakly to $q$, then

$$
q\in \mathrm{argmin}\Theta,
$$

meaning

$$
\forall x\in H,\qquad \Theta(q)\le \Theta(x).
$$

Third, if $\Theta$ has no minimizer at all, i.e.

$$
\mathrm{argmin}\Theta=\varnothing,
$$

then the norms of the iterates diverge to infinity:

$$
\|u_k\|\longrightarrow +\infty
\quad\text{as } k\to\infty .
$$

Thus the proposition says that, under the inertial forward-backward hypotheses, the objective values converge to the infimum of the objective, every weak limit point of the trajectory is already a minimizer, and if no minimizer exists then the trajectory must escape to infinity in norm.

## Lean proof
```lean
by
  rcases proposition2 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB with
    ⟨henergy_mono, hsq, e, henergy_tail, hTheta_tail⟩
  have hTheta : Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop (nhds e) :=
    tendsto_of_tendsto_nat_succ hTheta_tail
  have hobjective : Filter.Tendsto (fun k ↦ Θ (u k)) Filter.atTop
      (nhds (sInf (Set.range Θ))) := by
    let E : ℕ → EReal := fun k ↦
      mechanicalEnergy Θ u (gamma a b lam) (k + 1) (by omega)
    have hE : Filter.Tendsto E Filter.atTop (nhds e) := by
      simpa [E] using henergy_tail
    have hE_mono : ∀ k, E (k + 1) ≤ E k := by
      intro k
      simpa [E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using henergy_mono k
    have hE_lower : ∀ k, e ≤ E k := energy_limit_le_local E e hE_mono hE
    have hvelocity_error : Summable (fun k : ℕ ↦
        (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2) := by
      simpa using Summable.mul_left (b * gamma a b lam) hsq
    obtain ⟨m, hm⟩ := hH.theta_bounded_below
    have hrange_bdd : BddBelow (Set.range Θ) := by
      refine ⟨(m : EReal), ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hm x
    have heq : e = sInf (Set.range Θ) := by
      apply le_antisymm
      · apply le_csInf
        · exact Set.range_nonempty Θ
        · intro z hz
          rcases hz with ⟨q, rfl⟩
          by_cases hqtop : Θ q = ⊤
          · rw [hqtop]
            exact le_top
          have hqbot : Θ q ≠ ⊥ := theta_ne_bot phi Θ psi gradPsi a b lam Lpsi hH q
          have hqphi : q ∈ ERealFunction.dom phi := by
            apply (ERealFunction.mem_dom_iff phi q).mpr
            apply (lt_top_iff_ne_top).2
            intro hphitop
            apply hqtop
            rw [hH.theta_eq, hphitop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
          obtain ⟨C, hC⟩ := liapunov_distance_increment_le phi Θ psi gradPsi a b lam Lpsi
            u y hH hIFB q hqphi
          have hm_e : (m : EReal) ≤ e := by
            apply ge_of_tendsto hTheta
            filter_upwards [] with k
            exact hm (u k)
          have hE0 : e ≤ E 0 := hE_lower 0
          have hE0top : E 0 ≠ ⊤ := by
            dsimp [E, mechanicalEnergy]
            exact EReal.add_ne_top (theta_trajectory_finite phi Θ psi gradPsi a b lam Lpsi
              u y hH hIFB 0).1 (EReal.coe_ne_top _)
          have hetop : e ≠ ⊤ := ne_top_of_le_ne_top hE0top hE0
          have hebot : e ≠ ⊥ := by
            intro he
            have : (m : EReal) = ⊥ := le_bot_iff.mp (he ▸ hm_e)
            exact EReal.coe_ne_bot m this
          have hecoe : ((e.toReal : ℝ) : EReal) = e := EReal.coe_toReal hetop hebot
          let α : ℝ := (1 + b * lam) / (2 * lam ^ 2)
          let aF : ℕ → ℝ := fun k ↦
            liapunovF u y a b lam q (k + 1) (by omega) - C
          let bDist : ℕ → ℝ := fun k ↦ α * ‖u (k + 1) - q‖ ^ 2
          let eps : ℕ → ℝ := fun k ↦
            (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2
          let theta : ℝ := b * ((Θ q).toReal - e.toReal)
          have heps : Summable eps := by
            simpa [eps] using hvelocity_error
          have hinc (k : ℕ) (hk : 1 ≤ k) :
              aF k - aF (k - 1) ≤ theta + eps k := by
            dsimp [aF, eps, theta]
            have hF := liapunov_succ_increment_le_gap_local phi Θ psi gradPsi a b lam Lpsi
              u y q hH hIFB hqtop hqbot k hk
            have hEk := hE_lower k
            dsimp [E, mechanicalEnergy] at hEk
            obtain ⟨hukt, hukb⟩ :=
              theta_trajectory_finite phi Θ psi gradPsi a b lam Lpsi u y hH hIFB k
            have hEkreal : e.toReal ≤ (Θ (u (k + 1))).toReal +
                gamma a b lam * ‖u (k + 1) - u k‖ ^ 2 := by
              rw [← EReal.coe_toReal hetop hebot,
                ← EReal.coe_toReal hukt hukb] at hEk
              norm_num at hEk
              rw [velocity_eq_sub_of_one_le] at hEk
              simpa only [Nat.add_sub_cancel] using (EReal.coe_le_coe_iff.mp hEk)
            have hgap : b * ((Θ q).toReal - (Θ (u (k + 1))).toReal) ≤
                b * ((Θ q).toReal - e.toReal) +
                  (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_left hEkreal hH.b_pos.le]
            have hFk : liapunovF u y a b lam q (k + 1) (by omega) -
                liapunovF u y a b lam q k (by omega) ≤
                b * ((Θ q).toReal - e.toReal) +
                  (b * gamma a b lam) * ‖u (k + 1) - u k‖ ^ 2 :=
              hF.trans hgap
            simpa [Nat.sub_add_cancel hk] using hFk
          have hdist (k : ℕ) (hk : 1 ≤ k) :
              bDist (k + 1) - bDist k ≤ aF k := by
            dsimp [bDist, aF, α]
            simpa [Nat.add_assoc] using hC (k + 1) (by omega)
          have hα : 0 < α := by
            dsimp [α]
            apply div_pos <;> nlinarith [hH.b_pos, hH.step_pos]
          have hnonneg (k : ℕ) (_ : 1 ≤ k) : 0 ≤ bDist k := by
            exact mul_nonneg hα.le (sq_nonneg _)
          have htheta : 0 ≤ theta :=
            lemma5 aF bDist eps theta 1 (by omega) heps.norm hinc hdist hnonneg
          have hreal : e.toReal ≤ (Θ q).toReal := by
            dsimp [theta] at htheta
            nlinarith [hH.b_pos]
          rw [← hecoe, ← EReal.coe_toReal hqtop hqbot]
          exact_mod_cast hreal
      · apply ge_of_tendsto hTheta
        filter_upwards [] with k
        exact csInf_le hrange_bdd ⟨u k, rfl⟩
    simpa [heq] using hTheta
  have hcluster : ∀ q, IsSequentialClusterPt (fun k ↦ toWeakSpace ℝ H (u k))
      (toWeakSpace ℝ H q) → q ∈ Optimization.argminSet Θ := by
    intro q hq
    obtain ⟨σ, hσ, hσweak⟩ := hq.exists_subseq_tendsto
    have hsubTheta : Filter.Tendsto (fun n ↦ Θ (u (σ n))) Filter.atTop
        (nhds (sInf (Set.range Θ))) := by
      simpa [Function.comp_def] using hobjective.comp hσ.tendsto_atTop
    have hqle : Θ q ≤ sInf (Set.range Θ) := by
      by_contra hnot
      have hlt : sInf (Set.range Θ) < Θ q := lt_of_not_ge hnot
      obtain ⟨r, hrleft, hrright⟩ := EReal.exists_between_coe_real hlt
      have hevent : ∀ᶠ n in Filter.atTop, Θ (u (σ n)) < (r : EReal) :=
        hsubTheta.eventually (Iio_mem_nhds hrleft)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
      have hclosed : IsClosed (ERealFunction.lowerLevelSet Θ r) :=
        (ERealFunction.lowerSemicontinuous_iff_isClosed_lowerLevelSet Θ).mp
          (theta_lowerSemicontinuous phi Θ psi gradPsi a b lam Lpsi hH) r
      have hconvex : Convex ℝ (ERealFunction.lowerLevelSet Θ r) :=
        convex_lowerLevelSet_theta Θ r hH.theta_convex
      have hmem : ∀ n, u (σ (n + N)) ∈ ERealFunction.lowerLevelSet Θ r := by
        intro n
        exact le_of_lt (hN _ (Nat.le_add_left N n))
      have hweakshift : Filter.Tendsto
          (fun n ↦ toWeakSpace ℝ H (u (σ (n + N)))) Filter.atTop
          (nhds (toWeakSpace ℝ H q)) := by
        simpa [Function.comp_def] using hσweak.comp (Filter.tendsto_add_atTop_nat N)
      have hqr : q ∈ ERealFunction.lowerLevelSet Θ r :=
        mem_of_tendsto_weakly_of_isClosed_convex hclosed hconvex hmem hweakshift
      exact (not_le_of_gt hrright) hqr
    rw [Optimization.mem_argminSet_iff_eq_sInf]
    exact le_antisymm hqle (csInf_le' ⟨q, rfl⟩)
  refine ⟨hobjective, hcluster, ?_⟩
  intro hempty
  apply tendsto_norm_atTop_of_no_weak_cluster u
  intro q hq
  have hqmin := hcluster q hq
  rw [hempty] at hqmin
  simp at hqmin
```

## Proof explanation
The proof begins by applying `proposition2` to the same data. That result provides three facts: the mechanical energy along the shifted indices is nonincreasing,

$$
\mathcal E_{k+2}\le \mathcal E_{k+1},
$$

the squared velocity increments are summable,

$$
\sum_k \|u_{k+1}-u_k\|^2<\infty,
$$

and there exists an extended real number $e$ such that both the shifted mechanical energies and the shifted objective values converge to $e$:

$$
\mathcal E_{k+1}\to e,
\qquad
\Theta(u_{k+1})\to e.
$$

Here the mechanical energy is defined using the parameter

$$
\gamma(a,b,\lambda)=\frac{1-a\lambda}{2b\lambda^2},
$$

so that

$$
\mathcal E_k
=\Theta(u_k)+\gamma(a,b,\lambda)\,\|u_k-u_{k-1}\|^2 .
$$

The Lean tactic `rcases` destructs this conjunction into `henergy_mono`, `hsq`, and the limiting data.

Next, the proof uses `tendsto_of_tendsto_nat_succ`. This lemma says that if a sequence shifted by one converges to a limit, then the original sequence converges to the same limit. Applying it to the known convergence $\Theta(u_{k+1})\to e$ gives

$$
\Theta(u_k)\to e.
$$

The proof then defines

$$
E_k=\mathcal E_{k+1}
=\Theta(u_{k+1})+\gamma(a,b,\lambda)\|u_{k+1}-u_k\|^2 .
$$

From `proposition2`, $E_k\to e$, and from the monotonicity of the mechanical energy, $E_{k+1}\le E_k$. The lemma `energy_limit_le_local` then gives

$$
e\le E_k
$$

for every $k$. This is a standard fact for a nonincreasing sequence in the extended reals: its limit is below every term of the sequence.

The proof also records that the sequence

$$
\varepsilon_k=(b\gamma(a,b,\lambda))\|u_{k+1}-u_k\|^2
$$

is summable, using `Summable.mul_left`, since multiplying a summable real sequence by the constant $b\gamma(a,b,\lambda)$ preserves summability.

The hypothesis `hH.theta_bounded_below` supplies a real number $m$ such that

$$
(m:\overline{\mathbb R})\le \Theta(x)
$$

for every $x\in H$. Hence the range of $\Theta$ is bounded below, which is recorded as `hrange_bdd`.

The main work of the first part is to prove

$$
e=\inf(\mathrm{range}\Theta).
$$

This is shown by antisymmetry.

For the inequality

$$
e\le \inf(\mathrm{range}\Theta),
$$

the proof uses `le_csInf`: it suffices to show that $e$ is below every element of the range. So take an arbitrary value $\Theta(q)$. If $\Theta(q)=\top$, then $e\le\top$ is trivial. Otherwise, `theta_ne_bot` gives $\Theta(q)\ne\bot$. To apply the Liapunov estimate, the proof needs $q\in \mathrm{dom}\phi$, meaning $\phi(q)<\top$. Using `ERealFunction.mem_dom_iff`, this is reduced to showing $\phi(q)\ne\top$. If $\phi(q)=\top$, then the identity in `hH.theta_eq` together with the fact that $\psi(q)$ is a real number, hence not $\bot$, would imply $\Theta(q)=\top$, contradicting the case assumption. Therefore $q\in\mathrm{dom}\phi$.

At this point the cited lemma `liapunov_distance_increment_le` is applied. It provides a constant $C$ such that for every $k\ge 1$,

$$
\frac{1+b\lambda}{2\lambda^2}\|u_{k+1}-q\|^2
-\frac{1+b\lambda}{2\lambda^2}\|u_k-q\|^2
\le
\mathrm{liapunovF}(u,y,a,b,\lambda,q,k)-C.
$$

Thus the Liapunov function controls the increment of the squared distance to $q$, up to the constant $C$. The proof denotes

$$
\alpha=\frac{1+b\lambda}{2\lambda^2},
$$

and defines

$$
aF_k=\mathrm{liapunovF}(u,y,a,b,\lambda,q,k+1)-C,
\qquad
bDist_k=\alpha\|u_{k+1}-q\|^2,
\qquad
\varepsilon_k=(b\gamma(a,b,\lambda))\|u_{k+1}-u_k\|^2,
$$

and

$$
\theta=b\left((\Theta(q))_{\mathbb R}-e_{\mathbb R}\right).
$$

Here $e_{\mathbb R}$ and $(\Theta(q))_{\mathbb R}$ are the real representatives of the finite extended-real numbers $e$ and $\Theta(q)$. The finiteness of $e$ is obtained from the earlier inequality $e\le E_0$ and the fact that the trajectory values $\Theta(u_{k+1})$ are neither $\top$ nor $\bot$, supplied by `theta_trajectory_finite`. The finiteness of $\Theta(q)$ in the current case comes from $\Theta(q)\ne\top$ and `theta_ne_bot`.

The proof now verifies the hypotheses of `lemma5`, a discrete comparison lemma. That lemma says that if $(\varepsilon_k)$ is absolutely summable and, for all sufficiently large $k$,

$$
a_k-a_{k-1}\le \theta+\varepsilon_k,
\qquad
b_{k+1}-b_k\le a_k,
\qquad
b_k\ge 0,
$$

then necessarily $\theta\ge 0$.

The first inequality for `lemma5` is established using `liapunov_succ_increment_le_gap_local`, which states that, at the current finite values of $\Theta(q)$ and $\Theta(u_{k+1})$,

$$
\mathrm{liapunovF}(u,y,a,b,\lambda,q,k+1)
-\mathrm{liapunovF}(u,y,a,b,\lambda,q,k)
\le
b\left((\Theta(q))_{\mathbb R}-(\Theta(u_{k+1}))_{\mathbb R}\right).
$$

Combining this with the earlier inequality $e\le E_k$, i.e.

$$
e\le \Theta(u_{k+1})+\gamma(a,b,\lambda)\|u_{k+1}-u_k\|^2,
$$

and converting it to real numbers using the finiteness of the relevant extended reals gives

$$
e_{\mathbb R}
\le
(\Theta(u_{k+1}))_{\mathbb R}
+\gamma(a,b,\lambda)\|u_{k+1}-u_k\|^2.
$$

Multiplication by $b>0$ and elementary real arithmetic then yield

$$
aF_k-aF_{k-1}
\le
\theta+\varepsilon_k .
$$

The second inequality for `lemma5`,

$$
bDist_{k+1}-bDist_k\le aF_k,
$$

is exactly the Liapunov distance estimate shifted by one. The nonnegativity condition $bDist_k\ge 0$ follows because

$$
\alpha=\frac{1+b\lambda}{2\lambda^2}>0,
$$

using $b>0$ and $\lambda>0$ from `hH`, and because a square is nonnegative. The tactic `nlinarith` discharges these real arithmetic inequalities.

Applying `lemma5` gives $\theta\ge 0$. Since $b>0$, this implies

$$
e_{\mathbb R}\le (\Theta(q))_{\mathbb R}.
$$

Converting back from real numbers to extended real numbers using the finiteness facts gives

$$
e\le \Theta(q).
$$

Since $q$ was arbitrary, $e$ is below every element of the range of $\Theta$, so

$$
e\le \inf(\mathrm{range}\Theta).
$$

For the reverse inequality, the proof uses the convergence $\Theta(u_k)\to e$. For every $k$, the value $\Theta(u_k)$ lies in the range of $\Theta$, so

$$
\inf(\mathrm{range}\Theta)\le \Theta(u_k).
$$

Passing to the limit and using `ge_of_tendsto` yields

$$
\inf(\mathrm{range}\Theta)\le e.
$$

Therefore

$$
e=\inf(\mathrm{range}\Theta),
$$

and since $\Theta(u_k)\to e$, the first conjunct of the theorem follows.

The second conjunct concerns weak sequential cluster points. Let $q$ be such a cluster point. By definition of `IsSequentialClusterPt`, there is a strictly increasing sequence $\sigma:\mathbb N\to\mathbb N$ such that

$$
u_{\sigma(n)}\rightharpoonup q
$$

weakly. Since $\Theta(u_k)\to \inf(\mathrm{range}\Theta)$, the subsequence also satisfies

$$
\Theta(u_{\sigma(n)})\to \inf(\mathrm{range}\Theta).
$$

The proof shows $\Theta(q)\le \inf(\mathrm{range}\Theta)$. Suppose not. Then

$$
\inf(\mathrm{range}\Theta)<\Theta(q).
$$

The lemma `EReal.exists_between_coe_real` provides a real number $r$ with

$$
\inf(\mathrm{range}\Theta)<(r:\overline{\mathbb R})<\Theta(q).
$$

Because $\Theta(u_{\sigma(n)})\to \inf(\mathrm{range}\Theta)$ and $\inf(\mathrm{range}\Theta)<r$, eventually

$$
\Theta(u_{\sigma(n)})<r.
$$

Thus, after shifting the subsequence by some $N$, all terms $u_{\sigma(n+N)}$ belong to the lower level set

$$
L_r=\{x\in H:\Theta(x)\le r\}.
$$

Now `theta_lowerSemicontinuous` gives that $\Theta$ is lower semicontinuous. The cited equivalence `lowerSemicontinuous_iff_isClosed_lowerLevelSet` says that lower semicontinuity of $\Theta$ is equivalent to closedness of every real lower level set $L_r$. Hence $L_r$ is closed. Also, `convex_lowerLevelSet_theta` says that if the epigraph of $\Theta$ is convex, then the lower level set $L_r$ is convex. Since `hH.theta_convex` supplies the convexity of the epigraph, $L_r$ is convex.

The shifted subsequence still converges weakly to $q$, because adding a fixed natural number to the index does not change the limit. The cited theorem `mem_of_tendsto_weakly_of_isClosed_convex` states that a weak sequential limit of points in a closed convex set remains in that set. Applying it to $L_r$ gives

$$
q\in L_r,
$$

i.e.

$$
\Theta(q)\le r.
$$

This contradicts the choice $r<\Theta(q)$. Therefore

$$
\Theta(q)\le \inf(\mathrm{range}\Theta).
$$

On the other hand, $\Theta(q)$ belongs to the range of $\Theta$, so

$$
\inf(\mathrm{range}\Theta)\le \Theta(q).
$$

Hence

$$
\Theta(q)=\inf(\mathrm{range}\Theta).
$$

The theorem `Optimization.mem_argminSet_iff_eq_sInf` says that, in a complete linear order, a point $q$ belongs to the argmin set of $\Theta$ exactly when $\Theta(q)$ equals the infimum of the range of $\Theta$. Applying this equivalence gives

$$
q\in\mathrm{argmin}\Theta.
$$

This proves the second conjunct.

Finally, assume

$$
\mathrm{argmin}\Theta=\varnothing.
$$

The proof applies `tendsto_norm_atTop_of_no_weak_cluster`. This theorem states that, in a complete space, if a sequence has no weak sequential cluster point, then its norm tends to $+\infty$. To verify its hypothesis, suppose $q$ were a weak sequential cluster point of $(u_k)$. By the just-proved second conjunct, $q\in\mathrm{argmin}\Theta$. But the argmin set is assumed empty, a contradiction. Therefore no such $q$ exists, and `tendsto_norm_atTop_of_no_weak_cluster` yields

$$
\|u_k\|\longrightarrow +\infty.
$$

This proves the third conjunct and completes the theorem.

