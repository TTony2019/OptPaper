## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_5.lean`

## Lean statement
```lean
theorem proposition8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (u y : ℕ → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y)
    (hS : (Optimization.argminSet Θ).Nonempty) :
    Bornology.IsBounded (Set.range u) ∧
    ∀ q ∈ Optimization.argminSet Θ, ∃ l : ℝ,
      Filter.Tendsto (fun k : ℕ => liapunovF u y a b lam q (k + 1) (by omega))
        Filter.atTop (nhds l)
```

## Statement explanation
The theorem `proposition8` is set in a real inner product space $H$, with norm $\|\cdot\|$ and inner product $\langle \cdot,\cdot\rangle$. It takes extended-real-valued functions

$$
\phi,\Theta:H\to \overline{\mathbb R},
$$

a real-valued function

$$
\psi:H\to\mathbb R,
$$

a map

$$
\mathrm{gradPsi}:H\to H,
$$

two sequences

$$
u,y:\mathbb N\to H,
$$

and real parameters $a,b,\lambda,L_{\psi}$.

The hypothesis `hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi` is the structural assumption on the convex/forward-backward problem. The proof uses from it only that $a>0$, $b>0$, $0<\lambda$, a step-size bound from which $\lambda<1/a$ is extracted, and convexity of $\mathrm{epigraph}\Theta$. The hypothesis `hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y` says that $(u,y)$ is an inertial forward-backward trajectory for the given data. The hypothesis

$$
hS : (\mathrm{argminSet}\Theta).\text{Nonempty}
$$

says that the set of global minimizers of $\Theta$,

$$
\mathrm{argminSet}(\Theta)=\{x\in H:\forall y\in H,\ \Theta(x)\le \Theta(y)\},
$$

is nonempty.

The conclusion is the conjunction of two statements.

First,

$$
\mathrm{Bornology.IsBounded}(\{u_k:k\in\mathbb N\}),
$$

meaning that the range of the sequence $u$ is a bounded subset of $H$.

Second, for every minimizer

$$
q\in \mathrm{argminSet}(\Theta),
$$

there exists a real number $l$ such that the sequence

$$
k\mapsto \mathrm{liapunovF}(u,y,a,b,\lambda,q,k+1)
$$

converges to $l$ as $k\to\infty$.

Here `liapunovF` is the Liapunov-type function built from $u,y,a,b,\lambda,q$. For $k\ge 1$, writing

$$
v_i:=\mathrm{velocity}(u,i)=u_i-u_{i-1}\qquad(i\ge 1),
$$

and setting

$$
\alpha=\frac{1+b\lambda}{2\lambda^2},\qquad
\delta=\frac{2+(b-a)\lambda}{2\lambda^2},
$$

one has

$$
\mathrm{liapunovF}(u,y,a,b,\lambda,q,k)
=
\frac{a+b}{2\lambda}\|u_k-q\|^2
-\left(\frac1\lambda+b\right)G_{k+1}
-\delta\sum_{i=2}^{k}\|v_i\|^2
+2\alpha\langle v_{k+1},u_k-q\rangle,
$$

where $G_{k+1}=\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k+1)$. Thus the theorem says that any inertial forward-backward trajectory has bounded iterates, and the Liapunov sequence associated with any minimizer $q$ of $\Theta$ has a finite limit.

## Lean proof
```lean
by
  obtain ⟨q₀, hq₀⟩ := hS
  obtain ⟨_, hsq, _⟩ := proposition2 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB
  let S : ℝ := ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun n => sq_nonneg _
  have hpoint (n : ℕ) : ‖u (n + 1) - u n‖ ^ 2 ≤ S := by
    dsimp [S]
    simpa using hsq.sum_le_tsum ({n} : Finset ℕ) (fun _ _ => sq_nonneg _)
  let A : ℝ := (a + b) / (2 * lam)
  let c : ℝ := 1 / lam + b
  let α : ℝ := (1 + b * lam) / (2 * lam ^ 2)
  let δ : ℝ := (2 + (b - a) * lam) / (2 * lam ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    apply div_pos
    · nlinarith [hH.a_pos, hH.b_pos]
    · nlinarith [hH.step_pos]
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [one_div_pos.mpr hH.step_pos, hH.b_pos]
  have hα : 0 < α := by
    dsimp [α]
    apply div_pos
    · nlinarith [mul_pos hH.b_pos hH.step_pos]
    · nlinarith [sq_pos_of_pos hH.step_pos]
  have hδ : 0 < δ := by
    have hlt : lam < 1 / a := lt_of_lt_of_le hH.step_lt (min_le_left _ _)
    have hla : lam * a < 1 := (lt_div_iff₀ hH.a_pos).mp hlt
    have hnum : 0 < 2 + (b - a) * lam := by
      nlinarith [mul_pos hH.b_pos hH.step_pos]
    dsimp [δ]
    exact div_pos hnum (by nlinarith [sq_pos_of_pos hH.step_pos])
  have hsqdist (q : H) (hq : q ∈ Optimization.argminSet Θ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ‖u k - q‖ ^ 2 ≤ B := by
    have hqdom := minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq
    let M : ℝ := Classical.choose (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom)
    have hG (j : ℕ) (hj : 2 ≤ j) : auxiliaryG u y a b lam q j hj ≤ M := by
      dsimp [M]
      exact Classical.choose_spec
        (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom) j hj
    let F : ℕ → ℝ := fun n => liapunovF u y a b lam q (n + 1) (by omega)
    have hF_succ (n : ℕ) : F (n + 1) ≤ F n := by
      dsimp [F]
      have hmono := (proposition3 phi Θ psi gradPsi u y a b lam Lpsi q (n + 1)
        hH hIFB (by omega) hH.theta_convex).2.2 hq
      exact liapunovF_le_proof_irrel u y a b lam q (n + 1 + 1) (n + 1)
        (hk := by omega) (hk' := by omega) (hl := by omega) (hl' := by omega) hmono
    have hFanti : Antitone F := antitone_nat_of_succ_le hF_succ
    have hupper (k : ℕ) : F k ≤ F 0 := hFanti (Nat.zero_le k)
    let C : ℝ := liapunovF u y a b lam q 1 (by omega) + c * M + δ * S +
      (2 * α ^ 2 / A) * S
    have htail (k : ℕ) : ‖u (k + 1) - q‖ ^ 2 ≤ max 0 (2 * C / A) := by
      have hsum := liapunov_velocity_sum_le_tsum u hsq (k + 1)
      have hGk : auxiliaryG u y a b lam q (k + 2) (by omega) ≤ M :=
        hG (k + 2) (by omega)
      have hvelsq : ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤ S := by
        rw [velocity_eq_sub_of_one_le]
        simpa using hpoint (k + 1)
      have hGM : -c * M ≤ -c * auxiliaryG u y a b lam q (k + 2) (by omega) := by
        nlinarith [mul_le_mul_of_nonneg_left hGk (le_of_lt hc)]
      have hTS : -δ * S ≤ -δ * (∑ i ∈ (Finset.Icc 2 (k + 1)).attach,
          ‖velocity u i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)‖ ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hδ)]
      have hYoung := liapunov_cross_young A α hA (le_of_lt hα)
        (velocity u (k + 2) (by omega)) (u (k + 1) - q)
      have hcoef : 0 ≤ 2 * α ^ 2 / A := by positivity
      have hvelS : (2 * α ^ 2 / A) * ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤
          (2 * α ^ 2 / A) * S :=
        mul_le_mul_of_nonneg_left hvelsq hcoef
      have hcross : -(A / 2) * ‖u (k + 1) - q‖ ^ 2 -
          (2 * α ^ 2 / A) * ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤
          2 * α * inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) := by
        nlinarith [hYoung]
      have hF : (A / 2) * ‖u (k + 1) - q‖ ^ 2 - c * M - δ * S -
          (2 * α ^ 2 / A) * S ≤ liapunovF u y a b lam q (k + 1) (by omega) := by
        dsimp [liapunovF]
        nlinarith [hvelS, hcross]
      have hhalf : (A / 2) * ‖u (k + 1) - q‖ ^ 2 ≤ C := by
        dsimp [C]
        nlinarith [hF, hupper k]
      have hdiv : ‖u (k + 1) - q‖ ^ 2 ≤ 2 * C / A := by
        apply (le_div_iff₀ hA).mpr
        nlinarith
      exact hdiv.trans (le_max_right _ _)
    let B : ℝ := max (max 0 (2 * C / A)) (‖u 0 - q‖ ^ 2)
    refine ⟨B, ?_, ?_⟩
    · exact le_trans (sq_nonneg _) (le_max_right _ _)
    · intro k
      cases k with
      | zero => exact le_max_right _ _
      | succ k => exact (htail k).trans (le_max_left _ _)
  have hbd : Bornology.IsBounded (Set.range u) := by
    obtain ⟨B, hB0, hB⟩ := hsqdist q₀ hq₀
    apply bounded_iterates_of_bounded_sq_distance u q₀
    exact bounded_nonnegative_real_range (fun k => ‖u k - q₀‖ ^ 2) B
      (fun k => sq_nonneg _) hB
  refine ⟨hbd, ?_⟩
  intro q hq
  obtain ⟨B, hB0, hB⟩ := hsqdist q hq
  have hqdom := minimizer_mem_phi_dom phi Θ psi gradPsi a b lam Lpsi hH hq
  let M : ℝ := Classical.choose (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom)
  have hG (j : ℕ) (hj : 2 ≤ j) : auxiliaryG u y a b lam q j hj ≤ M := by
    dsimp [M]
    exact Classical.choose_spec
      (proposition4 phi Θ psi gradPsi u y a b lam Lpsi hH hIFB q hqdom) j hj
  let F : ℕ → ℝ := fun n => liapunovF u y a b lam q (n + 1) (by omega)
  have hF_succ (n : ℕ) : F (n + 1) ≤ F n := by
    dsimp [F]
    have hmono := (proposition3 phi Θ psi gradPsi u y a b lam Lpsi q (n + 1)
      hH hIFB (by omega) hH.theta_convex).2.2 hq
    exact liapunovF_le_proof_irrel u y a b lam q (n + 1 + 1) (n + 1)
      (hk := by omega) (hk' := by omega) (hl := by omega) (hl' := by omega) hmono
  have hFanti : Antitone F := antitone_nat_of_succ_le hF_succ
  let L : ℝ := -c * M - δ * S - 2 * α * Real.sqrt S * Real.sqrt B
  have hlower (k : ℕ) : L ≤ F k := by
    have hsum := liapunov_velocity_sum_le_tsum u hsq (k + 1)
    have hGk : auxiliaryG u y a b lam q (k + 2) (by omega) ≤ M := by
      exact hG (k + 2) (by omega)
    have hvelsq : ‖velocity u (k + 2) (by omega)‖ ^ 2 ≤ S := by
      rw [velocity_eq_sub_of_one_le]
      simpa using hpoint (k + 1)
    have hvel : ‖velocity u (k + 2) (by omega)‖ ≤ Real.sqrt S := by
      nlinarith [norm_nonneg (velocity u (k + 2) (by omega)), Real.sqrt_nonneg S,
        Real.sq_sqrt hSnonneg]
    have hdist : ‖u (k + 1) - q‖ ≤ Real.sqrt B := by
      nlinarith [norm_nonneg (u (k + 1) - q), Real.sqrt_nonneg B,
        Real.sq_sqrt hB0, hB (k + 1)]
    have hinter : -‖velocity u (k + 2) (by omega)‖ * ‖u (k + 1) - q‖ ≤
        inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) := by
      simpa only [neg_mul] using
        (neg_le_of_abs_le (abs_real_inner_le_norm (velocity u (k + 2) (by omega))
          (u (k + 1) - q)))
    have hcross : -2 * α * Real.sqrt S * Real.sqrt B ≤
        2 * α * inner ℝ (velocity u (k + 2) (by omega)) (u (k + 1) - q) := by
      have hmul := mul_le_mul_of_nonneg_left hinter (by positivity : 0 ≤ 2 * α)
      nlinarith [mul_nonneg (norm_nonneg (velocity u (k + 2) (by omega)))
          (norm_nonneg (u (k + 1) - q)),
        mul_le_mul hvel hdist (norm_nonneg _) (Real.sqrt_nonneg _)]
    have hGM : -c * M ≤ -c * auxiliaryG u y a b lam q (k + 2) (by omega) := by
      nlinarith [mul_le_mul_of_nonneg_left hGk (le_of_lt hc)]
    have hTS : -δ * S ≤ -δ * (∑ i ∈ (Finset.Icc 2 (k + 1)).attach,
        ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hsum (le_of_lt hδ)]
    dsimp [F, L, liapunovF]
    nlinarith [mul_nonneg (le_of_lt hA) (sq_nonneg (‖u (k + 1) - q‖))]
  have hbelow : BddBelow (Set.range F) :=
    ⟨L, by rintro _ ⟨k, rfl⟩; exact hlower k⟩
  refine ⟨⨅ k, F k, ?_⟩
  exact tendsto_atTop_ciInf hFanti hbelow
```

## Proof explanation
The proof begins by extracting a minimizer from $hS$. Since $hS$ is the nonemptiness of $\mathrm{argminSet}(\Theta)$, the pattern
`obtain ⟨q₀, hq₀⟩ := hS`
introduces a point $q_0\in H$ together with the assertion

$$
q_0\in \mathrm{argminSet}(\Theta).
$$

Next, the proof invokes `proposition2` with the full data and trajectory hypotheses:

$$
\texttt{proposition2}\ \phi\ \Theta\ \psi\ \mathrm{gradPsi}\ a\ b\ \lambda\ L_{\psi}\ u\ y\ hH\ hIFB.
$$

That result states three things: the mechanical energy is nonincreasing along the trajectory, the series of squared successive differences is summable, and the mechanical energy and $\Theta(u_{k+1})$ converge to a common extended-real limit. The proof uses only the summability part, extracting it by
`obtain ⟨_, hsq, _⟩ := ...`.
Thus

$$
hsq:\quad \sum_{n=0}^{\infty}\|u_{n+1}-u_n\|^2<\infty,
$$

or in Lean terms, the function

$$
n\mapsto \|u_{n+1}-u_n\|^2
$$

is summable.

The proof then defines the total velocity energy

$$
S:=\sum_{n=0}^{\infty}\|u_{n+1}-u_n\|^2.
$$

Using `tsum_nonneg` and `sq_nonneg`, it proves

$$
0\le S.
$$

Then, for each $n$, it proves

$$
\|u_{n+1}-u_n\|^2\le S.
$$

This uses `hsq.sum_le_tsum` applied to the singleton finite set $\{n\}$: for a summable nonnegative series, every finite sub-sum is at most the total sum. In this case the finite sum is just the single nonnegative term $\|u_{n+1}-u_n\|^2$.

The proof introduces abbreviations for important coefficients:

$$
A=\frac{a+b}{2\lambda},\qquad
c=\frac1\lambda+b,\qquad
\alpha=\frac{1+b\lambda}{2\lambda^2},\qquad
\delta=\frac{2+(b-a)\lambda}{2\lambda^2}.
$$

These match the coefficients appearing in `liapunovF`.

It proves the positivity of these coefficients:

- $A>0$: since $a>0$, $b>0$, and $\lambda>0$, both $a+b$ and $2\lambda$ are positive.
- $c>0$: since $1/\lambda>0$ and $b>0$.
- $\alpha>0$: the numerator $1+b\lambda$ is positive because $b\lambda>0$, and the denominator $2\lambda^2$ is positive.
- $\delta>0$: the proof uses the step-size hypothesis to get $\lambda<1/a$, hence $\lambda a<1$. Therefore

$$
2+(b-a)\lambda=2+b\lambda-a\lambda>0,
$$

and the denominator $2\lambda^2$ is positive.

The central intermediate result is `hsqdist`. For every minimizer

$$
q\in \mathrm{argminSet}(\Theta),
$$

it proves that there exists a real bound $B$ with $B\ge 0$ such that

$$
\forall k\in\mathbb N,\qquad \|u_k-q\|^2\le B.
$$

This is proved as follows.

First, the proof applies `minimizer_mem_phi_dom`. This lemma says that if $q$ is a minimizer of $\Theta$ and the hypothesis `hH` holds, then $q$ lies in the domain of $\phi$:

$$
q\in \mathrm{dom}\phi.
$$

This is needed to apply `proposition4`.

Next, `proposition4` is invoked with $q$ and the fact $q\in\mathrm{dom}\phi$. It gives the existence of a real number $M$ such that for every $j\ge 2$,

$$
\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,j)\le M.
$$

The proof chooses such an $M$ by `Classical.choose` and records its defining property by `Classical.choose_spec`, obtaining

$$
\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,j)\le M
$$

for every $j\ge 2$.

Then the proof defines

$$
F_n:=\mathrm{liapunovF}(u,y,a,b,\lambda,q,n+1).
$$

For each $n$, it proves

$$
F_{n+1}\le F_n.
$$

This comes from `proposition3`. For $k\ge 1$, with convexity of $\mathrm{epigraph}\Theta$ supplied by `hH.theta_convex`, `proposition3` states in particular that if $q\in\mathrm{argminSet}(\Theta)$, then

$$
\mathrm{liapunovF}(u,y,a,b,\lambda,q,k+1)
\le
\mathrm{liapunovF}(u,y,a,b,\lambda,q,k).
$$

Taking $k=n+1$ gives the successor inequality $F_{n+1}\le F_n$. The lemma `liapunovF_le_proof_irrel` is used here because `liapunovF` carries a proof argument that the index is at least $1$; this lemma says that the inequality does not depend on which proof of the index bound is used.

From the successor inequality, the library lemma `antitone_nat_of_succ_le` gives that $F$ is antitone, meaning

$$
m\le n\implies F_n\le F_m.
$$

In particular, for every $k$,

$$
F_k\le F_0=\mathrm{liapunovF}(u,y,a,b,\lambda,q,1).
$$

The proof then defines

$$
C:=\mathrm{liapunovF}(u,y,a,b,\lambda,q,1)+cM+\delta S+\frac{2\alpha^2}{A}S.
$$

It proves that for every $k$,

$$
\|u_{k+1}-q\|^2\le \max\left(0,\frac{2C}{A}\right).
$$

The key estimates are the following.

From `liapunov_velocity_sum_le_tsum`, applied with $k+1$, one has

$$
\sum_{i=2}^{k+1}\|\mathrm{velocity}(u,i)\|^2\le S.
$$

Also, using `velocity_eq_sub_of_one_le`,

$$
\mathrm{velocity}(u,k+2)=u_{k+2}-u_{k+1},
$$

so the earlier singleton estimate gives

$$
\|\mathrm{velocity}(u,k+2)\|^2\le S.
$$

Since $c>0$ and

$$
\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k+2)\le M,
$$

one obtains

$$
-cM\le -c\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k+2).
$$

Similarly, since $\delta>0$,

$$
-\delta S\le -\delta\sum_{i=2}^{k+1}\|\mathrm{velocity}(u,i)\|^2.
$$

The cross term is controlled by `liapunov_cross_young`. That lemma states that if $A>0$, $\alpha\ge 0$, and $v,d\in H$, then

$$
-2\alpha\langle v,d\rangle
\le
\frac A2\|d\|^2+\frac{2\alpha^2}{A}\|v\|^2.
$$

Applying it with

$$
v=\mathrm{velocity}(u,k+2),\qquad d=u_{k+1}-q
$$

and rearranging gives

$$
-\frac A2\|u_{k+1}-q\|^2
-\frac{2\alpha^2}{A}\|\mathrm{velocity}(u,k+2)\|^2
\le
2\alpha\langle \mathrm{velocity}(u,k+2),u_{k+1}-q\rangle.
$$

Together with

$$
\|\mathrm{velocity}(u,k+2)\|^2\le S,
$$

this bounds the cross term from below by

$$
-\frac A2\|u_{k+1}-q\|^2-\frac{2\alpha^2}{A}S.
$$

Using these inequalities and unfolding `liapunovF`, the proof establishes

$$
\frac A2\|u_{k+1}-q\|^2-cM-\delta S-\frac{2\alpha^2}{A}S
\le F_k.
$$

Since $F_k\le F_0$, this implies

$$
\frac A2\|u_{k+1}-q\|^2\le C.
$$

Because $A>0$, division gives

$$
\|u_{k+1}-q\|^2\le \frac{2C}{A},
$$

and hence also

$$
\|u_{k+1}-q\|^2\le \max\left(0,\frac{2C}{A}\right).
$$

The proof then sets

$$
B:=\max\left(\max\left(0,\frac{2C}{A}\right),\|u_0-q\|^2\right).
$$

It verifies $B\ge 0$, and then checks the two cases $k=0$ and $k=k'+1$. For $k=0$, the bound is immediate from the second component of the maximum. For $k=k'+1$, the estimate above gives the desired bound. This completes `hsqdist`.

With `hsqdist` available for the initial minimizer $q_0$, the proof establishes boundedness of the range of $u$. It uses `bounded_nonnegative_real_range` to convert the uniform bound

$$
\forall k,\ \|u_k-q_0\|^2\le B
$$

into boundedness of the range of the real sequence

$$
k\mapsto \|u_k-q_0\|^2.
$$

The lemma requires exactly that the sequence is nonnegative and bounded above. Then it applies `bounded_iterates_of_bounded_sq_distance` with $q=q_0$. That lemma says that if the range of the squared distances $\|u_k-q_0\|^2$ is bounded, then the range of $u$ itself is bounded. This proves the first conjunct.

It remains to prove the convergence statement for an arbitrary minimizer $q\in\mathrm{argminSet}(\Theta)$. The proof reintroduces $q$, obtains the squared-distance bound from `hsqdist`, applies `minimizer_mem_phi_dom` to get $q\in\mathrm{dom}\phi$, and again uses `proposition4` to obtain a real $M$ such that

$$
\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,j)\le M
$$

for all $j\ge 2$.

It again defines

$$
F_n:=\mathrm{liapunovF}(u,y,a,b,\lambda,q,n+1)
$$

and proves $F_{n+1}\le F_n$ in the same way as before, using `proposition3` and `liapunovF_le_proof_irrel`. Hence $F$ is antitone.

Now the goal is to show that $F$ is bounded below. The proof defines

$$
L:=-cM-\delta S-2\alpha\sqrt S\sqrt B.
$$

It proves for every $k$,

$$
L\le F_k.
$$

The ingredients are similar to the previous estimate, but the cross term is bounded below by Cauchy–Schwarz instead of Young's inequality.

Indeed, from

$$
\|\mathrm{velocity}(u,k+2)\|^2\le S,
\qquad
\|u_{k+1}-q\|^2\le B,
$$

and the nonnegativity of norms and square roots, the proof obtains

$$
\|\mathrm{velocity}(u,k+2)\|\le\sqrt S,
\qquad
\|u_{k+1}-q\|\le\sqrt B.
$$

Here it uses `Real.sq_sqrt`, which says that for nonnegative $x$, $(\sqrt x)^2=x$.

The inequality `abs_real_inner_le_norm` is the Cauchy–Schwarz bound

$$
|\langle v,d\rangle|\le \|v\|\|d\|.
$$

Applied to $v=\mathrm{velocity}(u,k+2)$ and $d=u_{k+1}-q$, it gives

$$
-\|\mathrm{velocity}(u,k+2)\|\|u_{k+1}-q\|
\le
\langle \mathrm{velocity}(u,k+2),u_{k+1}-q\rangle.
$$

Since $\alpha>0$, multiplying by $2\alpha$ preserves the inequality, and using the square-root bounds yields

$$
-2\alpha\sqrt S\sqrt B
\le
2\alpha\langle \mathrm{velocity}(u,k+2),u_{k+1}-q\rangle.
$$

Together with the previous bounds

$$
-cM\le -c\mathrm{auxiliaryG}(u,y,a,b,\lambda,q,k+2),
$$

$$
-\delta S\le -\delta\sum_{i=2}^{k+1}\|\mathrm{velocity}(u,i)\|^2,
$$

and the fact that

$$
A\|u_{k+1}-q\|^2\ge 0,
$$

unfolding `liapunovF` gives

$$
L\le F_k.
$$

Thus $L$ is a lower bound for the range of $F$, so

$$
\mathrm{BddBelow}(\{F_k:k\in\mathbb N\}).
$$

Finally, since $F$ is antitone and bounded below, the proof applies `tendsto_atTop_ciInf`. This theorem states that an antitone sequence of real numbers that is bounded below converges to its infimum. In Lean notation, the limit is

$$
\bigwedge_{k}F_k,
$$

written `⨅ k, F k`. The final `refine ⟨⨅ k, F k, ?_⟩` chooses this infimum as the required limit $l$, and `tendsto_atTop_ciInf hFanti hbelow` supplies the convergence proof. This completes the second conjunct and hence the theorem.

