## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_3.lean`

## Lean statement
```lean
theorem proposition4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (u y : ℕ → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis Φ Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory Φ psi gradPsi a b lam u y) (q : H)
    (hq : q ∈ ERealFunction.dom Φ) :
    ∃ M : ℝ, ∀ k (hk : 2 ≤ k), auxiliaryG u y a b lam q k hk ≤ M
```

## Statement explanation
The declaration `proposition4` is set in a real inner product space $H$. It takes extended-real functions $\Phi,\Theta:H\to\overline{\mathbb R}$, a real-valued function $\psi:H\to\mathbb R$, a map `gradPsi` from $H$ to $H$, two sequences $u,y:\mathbb N\to H$, real parameters $a,b,\lambda,L_\psi$, an inertial-forward-backward hypothesis `hH`, and a trajectory hypothesis `hIFB` saying that $u,y$ form an inertial forward-backward trajectory for these data. It also takes a point $q\in H$ with $q\in\mathrm{dom}\Phi$; by the cited `mem_dom_iff`, this means precisely that $\Phi(q)<+\infty$.

For each $k\ge 2$, the expression `auxiliaryG u y a b lam q k hk` denotes an auxiliary quantity, which we may write as $G_k$. The conclusion is that there exists a real number $M$, independent of $k$, such that for every natural number $k\ge 2$,

$$
G_k\le M.
$$

Thus the theorem asserts a uniform upper bound on the auxiliary quantities $G_k$ along the inertial forward-backward trajectory, provided the reference point $q$ lies in the domain of $\Phi$. The definition of `auxiliaryG` is not included in the supplied source; the proof uses the cited identity `auxiliaryG_summation_by_parts` to rewrite $G_k$ into an explicit sum of inner products.

## Lean proof
```lean
by
  have hfinite (n : ℕ) :
      Φ (u (n + 1)) ≠ ⊤ ∧ Φ (u (n + 1)) ≠ ⊥ ∧ Θ (u (n + 1)) ≠ ⊤ ∧
        Θ (u (n + 1)) ≠ ⊥ :=
    trajectory_value_finite Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB n
  have hsub (j : ℕ) (hj : 1 ≤ j) :
      -zSequence u y a b lam j hj ∈ subdifferential Φ (u j) :=
    z_neg_mem_convexSubdifferential Φ psi gradPsi u y a b lam hIFB j hj
  obtain ⟨_, hsq, _⟩ := proposition2 Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB
  obtain ⟨m, hm⟩ := hH.theta_bounded_below
  classical
  have htelPhi : ∀ k : ℕ, 2 ≤ k → ∑ i ∈ Finset.Icc 2 k,
      ((Φ (u i)).toReal - (Φ (u (i - 1))).toReal) =
        (Φ (u k)).toReal - (Φ (u 1)).toReal := by
    intro k hk
    refine Nat.le_induction ?_ ?_ k hk
    · norm_num
    · intro n hn ih
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      norm_num
  have htelTheta : ∀ k : ℕ, 2 ≤ k → ∑ i ∈ Finset.Icc 2 k,
      ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal) =
        (Θ (u 1)).toReal - (Θ (u k)).toReal := by
    intro k hk
    refine Nat.le_induction ?_ ?_ k hk
    · norm_num
    · intro n hn ih
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      norm_num
  have hqtop : Φ q ≠ ⊤ := ne_of_lt ((ERealFunction.mem_dom_iff Φ q).mp hq)
  let A : ℝ := (b * lam ^ 2 * Lpsi - (a + 2 * b) * lam - 1) / (2 * lam)
  let B : ℝ := (1 - a * lam) / (2 * lam)
  let S : ℝ := ∑' n : ℕ, ‖u (n + 1) - u n‖ ^ 2
  refine ⟨(Φ q).toReal - (Φ (u 1)).toReal +
      b * lam * ((Θ (u 1)).toReal - m) + (|A| + |B|) * S, ?_⟩
  intro k hk
  have hS : 0 ≤ S := tsum_nonneg (fun n ↦ sq_nonneg _)
  have hsum1 : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ S :=
    velocity_Icc_sum_le_tsum u hsq k hk
  have hsum0 : ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ S :=
    predecessor_velocity_Icc_sum_le_tsum u hsq k hk
  have hend := endpoint_subgradient_bound Φ u y a b lam q
    (fun n ↦ ⟨(hfinite n).1, (hfinite n).2.1⟩) hsub hqtop k (by omega)
  have hpred : -∑ i ∈ (Finset.Icc 2 k).attach,
      inner ℝ (zSequence u y a b lam (i.1 - 1) (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega))
        (velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)) ≤
      (Φ (u k)).toReal - (Φ (u 1)).toReal := by
    calc
      -∑ i ∈ (Finset.Icc 2 k).attach,
          inner ℝ (zSequence u y a b lam (i.1 - 1) (by
            have hi := (Finset.mem_Icc.mp i.2).1; omega))
            (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) =
          ∑ i ∈ (Finset.Icc 2 k).attach, -inner ℝ
            (zSequence u y a b lam (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega))
            (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) := by
              rw [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ (Finset.Icc 2 k).attach,
          ((Φ (u i.1)).toReal - (Φ (u (i.1 - 1))).toReal) := by
        apply Finset.sum_le_sum
        intro i hi
        exact predecessor_subgradient_bound Φ u y a b lam
          (fun n ↦ ⟨(hfinite n).1, (hfinite n).2.1⟩) hsub i.1
          ((Finset.mem_Icc.mp i.2).1)
      _ = _ := by
        have hattach : ∑ i ∈ (Finset.Icc 2 k).attach,
            ((Φ (u i.1)).toReal - (Φ (u (i.1 - 1))).toReal) =
            ∑ i ∈ Finset.Icc 2 k,
              ((Φ (u i)).toReal - (Φ (u (i - 1))).toReal) := by
          simpa only using Finset.sum_attach (Finset.Icc 2 k)
            (fun i : ℕ ↦ ((Φ (u i)).toReal - (Φ (u (i - 1))).toReal))
        rw [hattach, htelPhi k hk]
  have hdiff : -∑ i ∈ (Finset.Icc 2 k).attach,
      inner ℝ (zSequence u y a b lam i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega) - zSequence u y a b lam (i.1 - 1) (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega))
        (velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)) ≤
      A * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
        have hi := (Finset.mem_Icc.mp i.2).1
        omega)‖ ^ 2 +
        B * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 +
        b * lam * ((Θ (u 1)).toReal - (Θ (u k)).toReal) := by
    calc
      -∑ i ∈ (Finset.Icc 2 k).attach, inner ℝ
          (zSequence u y a b lam i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega) -
            zSequence u y a b lam (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega))
          (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) =
          ∑ i ∈ (Finset.Icc 2 k).attach, -inner ℝ
            (zSequence u y a b lam i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega) -
              zSequence u y a b lam (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega))
            (velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)) := by
              rw [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ (Finset.Icc 2 k).attach,
          (A * ‖velocity u i.1 (by have hi := (Finset.mem_Icc.mp i.2).1; omega)‖ ^ 2 +
            B * ‖velocity u (i.1 - 1) (by have hi := (Finset.mem_Icc.mp i.2).1; omega)‖ ^ 2 +
            b * lam * ((Θ (u (i.1 - 1))).toReal - (Θ (u i.1)).toReal)) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [A, B] using z_difference_bound Φ Θ psi gradPsi a b lam Lpsi u y hH hIFB i.1
          ((Finset.mem_Icc.mp i.2).1)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
        have hattach : ∑ i ∈ (Finset.Icc 2 k).attach,
            ((Θ (u (i.1 - 1))).toReal - (Θ (u i.1)).toReal) =
            ∑ i ∈ Finset.Icc 2 k,
              ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal) := by
          simpa only using Finset.sum_attach (Finset.Icc 2 k)
            (fun i : ℕ ↦ ((Θ (u (i - 1))).toReal - (Θ (u i)).toReal))
        rw [hattach, htelTheta k hk]
  have hmreal : m ≤ (Θ (u k)).toReal := by
    have hkm1 : k - 1 + 1 = k := by omega
    exact EReal.toReal_le_toReal (hm (u k))
      (EReal.coe_ne_bot m)
      (by simpa only [hkm1] using (hfinite (k - 1)).2.2.1)
  have htheta : b * lam * ((Θ (u 1)).toReal - (Θ (u k)).toReal) ≤
      b * lam * ((Θ (u 1)).toReal - m) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact le_of_lt (mul_pos hH.b_pos hH.step_pos)
  have hA : A * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ |A| * S := by
    calc
      A * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 ≤
          |A| * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u i.1 (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self A) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ ≤ |A| * S := mul_le_mul_of_nonneg_left hsum1 (abs_nonneg A)
  have hB : B * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
      have hi := (Finset.mem_Icc.mp i.2).1
      omega)‖ ^ 2 ≤ |B| * S := by
    calc
      B * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
          have hi := (Finset.mem_Icc.mp i.2).1
          omega)‖ ^ 2 ≤
          |B| * ∑ i ∈ (Finset.Icc 2 k).attach, ‖velocity u (i.1 - 1) (by
            have hi := (Finset.mem_Icc.mp i.2).1
            omega)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      _ ≤ |B| * S := mul_le_mul_of_nonneg_left hsum0 (abs_nonneg B)
  rw [auxiliaryG_summation_by_parts]
  linarith
```

## Proof explanation
The proof begins by extracting several consequences from the hypotheses.

First, `hfinite` is established using `trajectory_value_finite`. For every $n\in\mathbb N$, it gives

$$
\Phi(u(n+1))\ne +\infty,\qquad
\Phi(u(n+1))\ne -\infty,\qquad
\Theta(u(n+1))\ne +\infty,\qquad
\Theta(u(n+1))\ne -\infty.
$$

This is needed so that the real parts $(\Phi(u(n+1)))_{\mathbb R}$ and $(\Theta(u(n+1)))_{\mathbb R}$ are finite and may be used in ordinary real inequalities.

Second, `hsub` is established using `z_neg_mem_convexSubdifferential`. For every $j\ge 1$,

$$
-z_j\in \partial\Phi(u(j)),
$$

where

$$
z_j
=
zSequence(u,y,a,b,\lambda,j)
=
\lambda^{-1}(u(j)-u(j-1))+a u(j-1)-b y(j-1).
$$

The subdifferential membership means that for every $w\in H$,

$$
\langle w-u(j),-z_j\rangle+\Phi(u(j))\le \Phi(w).
$$

Equivalently,

$$
\langle u(j)-w,z_j\rangle+\Phi(u(j))\le \Phi(w).
$$

This is later specialized to $w=q$ and to $w=u(i)$.

Third, `proposition2` is applied to `hH` and `hIFB`. It provides, among other things, the summability

$$
\sum_{n=0}^{\infty}\|u(n+1)-u(n)\|^2<\infty.
$$

Only this summability part is used, stored as `hsq`. The other conclusions of `proposition2`, namely monotonicity of the mechanical energy and convergence results, are discarded in the proof.

Fourth, from `hH.theta_bounded_below`, the proof obtains a real number $m$ such that

$$
m\le \Theta(x)
$$

for every $x\in H$, where the left side is regarded as the extended real constant. This $m$ is the lower bound for $\Theta$ used later.

Next, the proof establishes two telescoping identities.

`htelPhi` states that for every $k\ge 2$,

$$
\sum_{i=2}^{k}\Bigl((\Phi(u(i)))_{\mathbb R}-(\Phi(u(i-1)))_{\mathbb R}\Bigr)
=
(\Phi(u(k)))_{\mathbb R}-(\Phi(u(1)))_{\mathbb R}.
$$

It is proved by induction on $k$ starting at $2$, using `Nat.le_induction`. In the successor step, `Finset.sum_Icc_succ_top` adds the last term of the sum over $\{2,\dots,k\}$, and `norm_num` simplifies the resulting arithmetic.

Similarly, `htelTheta` states that for every $k\ge 2$,

$$
\sum_{i=2}^{k}\Bigl((\Theta(u(i-1)))_{\mathbb R}-(\Theta(u(i)))_{\mathbb R}\Bigr)
=
(\Theta(u(1)))_{\mathbb R}-(\Theta(u(k)))_{\mathbb R}.
$$

Next, from $q\in\mathrm{dom}\Phi$, the proof obtains `hqtop` using `ERealFunction.mem_dom_iff`, which says

$$
q\in\mathrm{dom}\Phi \iff \Phi(q)<+\infty.
$$

Hence $\Phi(q)\ne +\infty$.

The proof then defines three real constants:

$$
A=\frac{b\lambda^2L_\psi-(a+2b)\lambda-1}{2\lambda},
\qquad
B=\frac{1-a\lambda}{2\lambda},
$$

and

$$
S=\sum_{n=0}^{\infty}\|u(n+1)-u(n)\|^2.
$$

It proposes the explicit upper bound

$$
M=(\Phi(q))_{\mathbb R}-(\Phi(u(1)))_{\mathbb R}
+b\lambda\bigl((\Theta(u(1)))_{\mathbb R}-m\bigr)
+(|A|+|B|)S.
$$

It remains to prove $G_k\le M$ for every $k\ge 2$.

The proof fixes such a $k$. It first notes $S\ge 0$ because $S$ is a sum of squares. Then it uses `velocity_Icc_sum_le_tsum` to obtain

$$
\sum_{i=2}^{k}\|v_i\|^2\le S,
\qquad
v_i=u(i)-u(i-1),
$$

and it uses `predecessor_velocity_Icc_sum_le_tsum` to obtain

$$
\sum_{i=2}^{k}\|v_{i-1}\|^2\le S.
$$

These are finite partial sums of nonnegative squared velocity terms, bounded by the full summable series.

Next, the proof applies `endpoint_subgradient_bound` with the index $k$. It gives

$$
\langle z_k,u(k)-q\rangle
\le
(\Phi(q))_{\mathbb R}-(\Phi(u(k)))_{\mathbb R}.
$$

This is the subgradient inequality at $u(k)$, with test point $q$, rearranged and converted to real parts.

Then it proves `hpred`, the bound

$$
-\sum_{i=2}^{k}\langle z_{i-1},v_i\rangle
\le
(\Phi(u(k)))_{\mathbb R}-(\Phi(u(1)))_{\mathbb R}.
$$

The proof rewrites the negative sum as the sum of the negatives using `Finset.sum_neg_distrib`. For each $i\in\{2,\dots,k\}$, it applies `predecessor_subgradient_bound`, which gives

$$
-\langle z_{i-1},v_i\rangle
\le
(\Phi(u(i)))_{\mathbb R}-(\Phi(u(i-1)))_{\mathbb R}.
$$

Summing these inequalities with `Finset.sum_le_sum`, converting the attached sum to an ordinary sum with `Finset.sum_attach`, and using the telescoping identity `htelPhi`, yields the desired bound.

The proof then proves `hdiff`, the bound

$$
-\sum_{i=2}^{k}\langle z_i-z_{i-1},v_i\rangle
\le
A\sum_{i=2}^{k}\|v_i\|^2
+
B\sum_{i=2}^{k}\|v_{i-1}\|^2
+
b\lambda\Bigl((\Theta(u(1)))_{\mathbb R}-(\Theta(u(k)))_{\mathbb R}\Bigr).
$$

To do this, it again rewrites the negative sum as a sum of negatives. For each $i$, `z_difference_bound` gives

$$
-\langle z_i-z_{i-1},v_i\rangle
\le
A\|v_i\|^2+B\|v_{i-1}\|^2
+
b\lambda\Bigl((\Theta(u(i-1)))_{\mathbb R}-(\Theta(u(i)))_{\mathbb R}\Bigr).
$$

The proof uses `simpa only [A, B]` to unfold the local definitions $A,B$ so that they match the coefficients in `z_difference_bound`. Then `Finset.sum_le_sum` sums the inequalities. Finally, `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.sum_attach`, and the telescoping identity `htelTheta` convert the sum to the displayed form.

The proof also needs a lower bound for $(\Theta(u(k)))_{\mathbb R}$. It proves `hmreal`:

$$
m\le (\Theta(u(k)))_{\mathbb R}.
$$

This follows from the extended-real inequality $m\le \Theta(u(k))$ supplied by `hH.theta_bounded_below`, together with the fact that $(m:\overline{\mathbb R})\ne -\infty$ and $\Theta(u(k))\ne +\infty$, using `EReal.toReal_le_toReal`.

Consequently, `htheta` gives

$$
b\lambda\Bigl((\Theta(u(1)))_{\mathbb R}-(\Theta(u(k)))_{\mathbb R}\Bigr)
\le
b\lambda\Bigl((\Theta(u(1)))_{\mathbb R}-m\Bigr).
$$

This uses that $b\lambda>0$, which follows from `hH.b_pos` and `hH.step_pos`.

The proof then bounds the two quadratic sums. It proves `hA`:

$$
A\sum_{i=2}^{k}\|v_i\|^2\le |A|S.
$$

Indeed, $A\le |A|$, the finite sum is nonnegative, and the sum is at most $S$. Similarly, `hB` proves

$$
B\sum_{i=2}^{k}\|v_{i-1}\|^2\le |B|S.
$$

Finally, the proof rewrites $G_k$ using `auxiliaryG_summation_by_parts`:

$$
G_k=
\langle z_k,u(k)-q\rangle
-\sum_{i=2}^{k}\langle z_{i-1},v_i\rangle
-\sum_{i=2}^{k}\langle z_i-z_{i-1},v_i\rangle.
$$

Now all estimates are combined. The endpoint term is at most

$$
(\Phi(q))_{\mathbb R}-(\Phi(u(k)))_{\mathbb R}.
$$

The predecessor sum is at most

$$
(\Phi(u(k)))_{\mathbb R}-(\Phi(u(1)))_{\mathbb R}.
$$

The difference sum is at most

$$
A\sum_{i=2}^{k}\|v_i\|^2
+
B\sum_{i=2}^{k}\|v_{i-1}\|^2
+
b\lambda\Bigl((\Theta(u(1)))_{\mathbb R}-(\Theta(u(k)))_{\mathbb R}\Bigr).
$$

Then the quadratic terms are bounded by

$$
(|A|+|B|)S,
$$

and the $\Theta$-term is bounded by

$$
b\lambda\Bigl((\Theta(u(1)))_{\mathbb R}-m\Bigr).
$$

Adding these inequalities gives

$$
G_k\le
(\Phi(q))_{\mathbb R}-(\Phi(u(1)))_{\mathbb R}
+
b\lambda\Bigl((\Theta(u(1)))_{\mathbb R}-m\Bigr)
+
(|A|+|B|)S
=
M.
$$

The final `linarith` closes the goal by combining these real linear inequalities. This proves that the auxiliary quantities $G_k$ admit the uniform upper bound $M$ for all $k\ge 2$.

