## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/prop_2.lean`

## Lean statement
```lean
theorem proposition3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (u y : ℕ → H)
    (a b lam Lpsi : ℝ) (q : H) (k : ℕ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y) (hk : 1 ≤ k)
    (hconvex : Convex ℝ (ERealFunction.epigraph Θ)) :
    ((b : EReal) * (Θ q - Θ (u (k + 1))) ≥
      ((b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) : EReal)) ∧
    (b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
      (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) =
      liapunovF u y a b lam q (k + 1) (by omega) - liapunovF u y a b lam q k hk) ∧
    (q ∈ Optimization.argminSet Θ →
      liapunovF u y a b lam q (k + 1) (by omega) ≤ liapunovF u y a b lam q k hk)
```

## Statement explanation
`proposition3` is a theorem about a real inner product space $H$. The data are two extended-real functions $\phi,\Theta:H\to\overline{\mathbb R}$, a real function $\psi:H\to\mathbb R$, its specified gradient $\operatorname{grad}\psi:H\to H$, two sequences $u,y:\mathbb N\to H$, real parameters $a,b,\lambda,L_\psi$, a point $q\in H$, and an index $k\in\mathbb N$. The hypotheses say that $k\ge1$, that $hH$ is an `IFBHypothesis` for $(\phi,\Theta,\psi,\operatorname{grad}\psi,a,b,\lambda,L_\psi)$, that `hIFB` is an `IsIFBTrajectory` for $(\phi,\psi,\operatorname{grad}\psi,a,b,\lambda,u,y)$, and that the epigraph of $\Theta$ is convex over $\mathbb R$, i.e. $\Theta$ is an extended-real convex function. The proof uses in particular that $b>0$ and that $\Theta(q)$ can be rewritten through `hH.theta_eq` in terms of $\phi(q)$ and a real term, while `hH.phi_proper` gives that $\phi(q)\ne\bot$.

For $k\ge1$, write

$$
v_k=u_k-u_{k-1},\qquad \zeta y_k=y_k-y_{k-1},
$$

and

$$
z_k=\frac1\lambda v_k+a u_{k-1}-b y_{k-1}.
$$

Also set

$$
S_k=\left(\frac1\lambda-a\right)v_{k+1}+\left(\frac1\lambda+b\right)\zeta y_{k+1}.
$$

Let

$$
F_k=\operatorname{liapunovF}(u,y,a,b,\lambda,q,k)
$$

be the Liapunov expression from the statement. Its definition is

$$
F_k=
\frac{a+b}{2\lambda}\|u_k-q\|^2
-\left(\frac1\lambda+b\right)G_{k+1}
-\delta\sum_{i=2}^k\|v_i\|^2
+2\alpha\left\langle v_{k+1},u_k-q\right\rangle,
$$

where

$$
\alpha=\frac{1+b\lambda}{2\lambda^2},\qquad
\delta=\frac{2+(b-a)\lambda}{2\lambda^2},
$$

and $G_{k+1}$ is the auxiliary term `auxiliaryG`. The conclusion of `proposition3` is the conjunction of three assertions:

1. In the extended-real order,

$$
b\bigl(\Theta(q)-\Theta(u_{k+1})\bigr)
\ge
\left(b\langle S_k,u_{k+1}-q\rangle\right)_{\mathbb R}.
$$

Here the right-hand side is the real number $b\langle S_k,u_{k+1}-q\rangle$ regarded as an element of $\overline{\mathbb R}$.

2. The same scalar quantity is the increment of the Liapunov expression:

$$
b\langle S_k,u_{k+1}-q\rangle
=
F_{k+1}-F_k.
$$

3. If $q$ is a minimizer of $\Theta$, i.e. $q\in\operatorname{argminSet}\Theta$, then

$$
F_{k+1}\le F_k.
$$

Thus the proposition says that the scalar product appearing in the discrete subgradient inequality is exactly the Liapunov increment, and that at a global minimizer of $\Theta$ this increment is nonpositive, so the Liapunov function does not increase.

## Lean proof
```lean
by
  obtain ⟨g, hg, hvector⟩ :=
    ifb_update_vector_identity phi psi gradPsi u y a b lam hIFB k
  have htheta_finite :=
    theta_value_finite_of_phi_subgradient phi Θ psi gradPsi a b lam Lpsi hH hg
  -- The next required fact is the EReal-valued differentiable perturbation rule:
  -- `hg` and `hH.theta_eq` must show that `g + gradPsi (u (k+1))` supports `Θ`.
  have hfirst :
      (b : EReal) * (Θ q - Θ (u (k + 1))) ≥
        ((b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
          (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) : EReal) := by
    have hsupp := theta_support_of_phi_subgradient phi Θ psi gradPsi a b lam Lpsi hH hconvex
      (q := q) hg
    rw [hvector] at hsupp
    have hsupp' :
        Θ q ≥ Θ (u (k + 1)) +
          (inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
            (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) := by
      have hinner :
          inner ℝ (-((1 / lam - a) • velocity u (k + 1) (by omega) +
            (1 / lam + b) • zeta y (k + 1) (by omega))) (q - u (k + 1)) =
          inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
            (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) := by
        rw [inner_neg_left]
        have hsub : q - u (k + 1) = -(u (k + 1) - q) := by abel
        rw [hsub, inner_neg_right]
        ring
      rw [hinner] at hsupp
      exact hsupp
    by_cases hq : Θ q = ⊤
    · rw [hq]
      rw [EReal.top_sub htheta_finite.1]
      rw [EReal.mul_top_of_pos (by exact_mod_cast hIFB.b_pos)]
      exact le_top
    have hqbot : Θ q ≠ ⊥ := by
      rw [hH.theta_eq]
      exact EReal.add_ne_bot_iff.mpr ⟨hH.phi_proper.1 q, EReal.coe_ne_bot _⟩
    have hreal :
        inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
          (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) ≤
          (Θ q).toReal - (Θ (u (k + 1))).toReal := by
      rw [← htheta_finite.2.2, ← EReal.coe_toReal hq hqbot] at hsupp'
      linarith [EReal.coe_le_coe_iff.mp hsupp']
    have hmul := mul_le_mul_of_nonneg_left hreal hIFB.b_pos.le
    rw [← htheta_finite.2.2, ← EReal.coe_toReal hq hqbot]
    exact_mod_cast hmul
  have hsecond :
      b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) =
        liapunovF u y a b lam q (k + 1) (by omega) - liapunovF u y a b lam q k hk := by
    have hscalar := scalar_product_normal_form u y a b lam q k hk
    have hF := liapunovF_increment_normal_form u y a b lam q k hk
    rw [hscalar, hF]
    have hv1 : velocity u (k + 1) (by omega) = u (k + 1) - u k := by
      rw [velocity_eq_sub_of_one_le]
      simp only [Nat.add_sub_cancel]
    have hnat : k + 2 - 1 = k + 1 := by omega
    have hv2 : velocity u (k + 2) (by omega) = u (k + 2) - u (k + 1) := by
      rw [velocity_eq_sub_of_one_le]
      rw [hnat]
    rw [hv1, hv2]
    unfold zSequence
    rw [hv1, hv2]
    rw [hnat]
    simp only [Nat.add_sub_cancel]
    rw [← real_inner_self_eq_norm_sq (u (k + 1) - u k)]
    simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
      starRingEnd_apply, star_trivial]
    rw [real_inner_comm (u (k + 1)) (u k)]
    by_cases hlam : lam = 0
    · subst lam
      norm_num
      ring
    · field_simp [hlam]
      ring
  refine ⟨hfirst, hsecond, ?_⟩
  intro hq
  rw [Optimization.mem_argminSet_iff_eq_sInf] at hq
  have hq_le : Θ q ≤ Θ (u (k + 1)) := by
    rw [hq]
    exact sInf_le (Set.mem_range_self _)
  have hleft_nonpos : (b : EReal) * (Θ q - Θ (u (k + 1))) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact_mod_cast hIFB.b_pos.le
    · exact EReal.sub_nonpos.mpr hq_le
  have hscalar_ereal :
      ((b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) : ℝ) : EReal) ≤ 0 :=
    hfirst.trans hleft_nonpos
  have hscalar :
      b * inner ℝ ((1 / lam - a) • velocity u (k + 1) (by omega) +
        (1 / lam + b) • zeta y (k + 1) (by omega)) (u (k + 1) - q) ≤ 0 := by
    exact_mod_cast hscalar_ereal
  rw [hsecond] at hscalar
  linarith
```

## Proof explanation
The proof begins by applying `ifb_update_vector_identity` to the trajectory hypothesis `hIFB`. This lemma gives, for the index $k$, a point

$$
g\in\partial\phi(u_{k+1})
$$

such that

$$
g+\operatorname{grad}\psi(u_{k+1})
=
-\left(
\left(\frac1\lambda-a\right)v_{k+1}
+\left(\frac1\lambda+b\right)\zeta y_{k+1}
\right)
=-S_k.
$$

This is the discrete optimality relation extracted from the inertial forward-backward trajectory. The proof destructs the existential with `obtain` and keeps the subgradient membership `hg` and the vector identity `hvector`.

Next, the lemma `theta_value_finite_of_phi_subgradient` is applied with the same `hH` and with $g\in\partial\phi(u_{k+1})$. Its conclusion, specialized to $x=u_{k+1}$, is that

$$
\Theta(u_{k+1})\ne\top,\qquad
\Theta(u_{k+1})\ne\bot,\qquad
\left((\Theta(u_{k+1})).\mathrm{toReal}\right)_{\overline{\mathbb R}}
=
\Theta(u_{k+1}).
$$

So the value of $\Theta$ at the next iterate is finite and may be treated as a real number. This is used later to move between extended-real and real inequalities.

To prove the first component, the proof invokes `theta_support_of_phi_subgradient`. Under the `IFBHypothesis`, under convexity of the epigraph of $\Theta$, and under $g\in\partial\phi(x)$, that theorem states

$$
\Theta(q)\ge
\Theta(x)+\langle g+\operatorname{grad}\psi(x),q-x\rangle
$$

for every $q\in H$. Taking $x=u_{k+1}$, this is a subgradient inequality for $\Theta$ at $u_{k+1}$. The proof rewrites the supporting vector $g+\operatorname{grad}\psi(u_{k+1})$ using `hvector`, obtaining

$$
\Theta(q)\ge
\Theta(u_{k+1})+\langle -S_k,q-u_{k+1}\rangle.
$$

A small inner-product sign calculation gives

$$
\langle -S_k,q-u_{k+1}\rangle
=
\langle S_k,u_{k+1}-q\rangle.
$$

Indeed, $q-u_{k+1}=-(u_{k+1}-q)$, and using bilinearity and symmetry of the real inner product changes the two minus signs into the displayed equality. Hence

$$
\Theta(q)\ge
\Theta(u_{k+1})+\langle S_k,u_{k+1}-q\rangle
$$

as an extended-real inequality.

The proof then splits on whether $\Theta(q)=\top$. If so, then because $\Theta(u_{k+1})$ is finite, the difference $\top-\Theta(u_{k+1})$ is $\top$, and since $b>0$, multiplying by $b$ still gives $\top$. The desired inequality is then trivial. In the remaining case, the proof shows $\Theta(q)\ne\bot$. This uses `hH.theta_eq` to rewrite $\Theta(q)$ as an extended-real sum involving $\phi(q)$ and a real term, and then uses properness of $\phi$ together with the fact that a real number is not $\bot$. Thus $\Theta(q)$ is a finite extended real.

Now both $\Theta(q)$ and $\Theta(u_{k+1})$ are finite. The support inequality is rewritten using the coercions

$$
\Theta(q)=\left((\Theta(q)).\mathrm{toReal}\right)_{\overline{\mathbb R}},\qquad
\Theta(u_{k+1})=\left((\Theta(u_{k+1})).\mathrm{toReal}\right)_{\overline{\mathbb R}}.
$$

The lemma `EReal.coe_le_coe_iff` converts the resulting inequality between embedded real numbers into the real inequality

$$
\langle S_k,u_{k+1}-q\rangle
\le
(\Theta(q)).\mathrm{toReal}
-
(\Theta(u_{k+1})).\mathrm{toReal}.
$$

Since $b\ge0$, multiplying by $b$ preserves the inequality:

$$
b\langle S_k,u_{k+1}-q\rangle
\le
b\left((\Theta(q)).\mathrm{toReal}
-
(\Theta(u_{k+1})).\mathrm{toReal}\right).
$$

Casting back to $\overline{\mathbb R}$ gives the first asserted inequality. This is the content of the `linarith` and `exact_mod_cast` steps in the first part.

For the second component, the proof uses two normal-form lemmas. The first is `scalar_product_normal_form`. It states that, for $k\ge1$,

$$
\begin{aligned}
& b\langle S_k,u_{k+1}-q\rangle \\
&=
\frac{a+b}{2\lambda}
\left(\|u_{k+1}-q\|^2-\|u_k-q\|^2\right)
+\left(\frac1\lambda+b\right)\langle z_{k+1},v_{k+1}\rangle
-\frac{2+(b-a)\lambda}{2\lambda^2}\|v_{k+1}\|^2 \\
&\quad
-\left(\frac1\lambda+b\right)
\Bigl(
\langle a u_{k+1}-b y_{k+1},u_{k+1}-q\rangle
-
\langle a u_k-b y_k,u_k-q\rangle
\Bigr).
\end{aligned}
$$

The second is `liapunovF_increment_normal_form`. It states that, for $k\ge1$,

$$
\begin{aligned}
F_{k+1}-F_k
&=
\frac{a+b}{2\lambda}
\left(\|u_{k+1}-q\|^2-\|u_k-q\|^2\right)
+\left(\frac1\lambda+b\right)\langle z_{k+2},v_{k+2}\rangle
-\frac{2+(b-a)\lambda}{2\lambda^2}\|v_{k+1}\|^2 \\
&\quad
-\left(\frac1\lambda+b\right)
\Bigl(
\langle z_{k+2},u_{k+2}-q\rangle
-
\langle z_{k+1},u_{k+1}-q\rangle
\Bigr) \\
&\quad
+2\frac{1+b\lambda}{2\lambda^2}
\Bigl(
\langle v_{k+2},u_{k+1}-q\rangle
-
\langle v_{k+1},u_k-q\rangle
\Bigr).
\end{aligned}
$$

After rewriting the goal with these two formulas, the proof reduces the equality to algebra. It uses `velocity_eq_sub_of_one_le` to replace

$$
v_{k+1}=u_{k+1}-u_k,\qquad
v_{k+2}=u_{k+2}-u_{k+1},
$$

and it unfolds `zSequence`, so $z_{k+1}$ and $z_{k+2}$ become

$$
z_{k+1}=\frac1\lambda v_{k+1}+a u_k-b y_k,\qquad
z_{k+2}=\frac1\lambda v_{k+2}+a u_{k+1}-b y_{k+1}.
$$

Then the proof expands all inner products using bilinearity of the real inner product. The lemma `real_inner_self_eq_norm_sq` replaces $\|x\|^2$ by $\langle x,x\rangle$, and `real_inner_comm` uses symmetry, for instance $\langle u_{k+1},u_k\rangle=\langle u_k,u_{k+1}\rangle$. The cases $\lambda=0$ and $\lambda\ne0$ are handled separately: in the first case `norm_num` and `ring` close the numeric/algebraic identity, and in the second case `field_simp` clears the denominators and `ring` proves the remaining polynomial identity. Thus the scalar product equals the Liapunov increment.

Finally, the proof establishes the third component. It assumes `hq : q ∈ Optimization.argminSet Θ`. The lemma `mem_argminSet_iff_eq_sInf` says that, for a complete linear order and a function $f:X\to R$, one has

$$
x\in\operatorname{argminSet} f
\quad\Longleftrightarrow\quad
f(x)=\inf\{f(y):y\in X\}.
$$

Applying this to $f=\Theta$ and $x=q$ rewrites the hypothesis as

$$
\Theta(q)=\inf\Theta(H).
$$

Since an infimum is at most any value in the set, the proof obtains

$$
\Theta(q)\le \Theta(u_{k+1}).
$$

Therefore

$$
\Theta(q)-\Theta(u_{k+1})\le0.
$$

Because $b\ge0$, multiplying by $b$ gives

$$
b\bigl(\Theta(q)-\Theta(u_{k+1})\bigr)\le0.
$$

Combining this with the first inequality

$$
b\bigl(\Theta(q)-\Theta(u_{k+1})\bigr)
\ge
\left(b\langle S_k,u_{k+1}-q\rangle\right)_{\mathbb R}
$$

shows

$$
\left(b\langle S_k,u_{k+1}-q\rangle\right)_{\mathbb R}\le0
$$

in $\overline{\mathbb R}$, hence

$$
b\langle S_k,u_{k+1}-q\rangle\le0
$$

as a real inequality. Using the second component

$$
b\langle S_k,u_{k+1}-q\rangle=F_{k+1}-F_k,
$$

the proof obtains

$$
F_{k+1}-F_k\le0.
$$

The final `linarith` step rearranges this to

$$
F_{k+1}\le F_k.
$$

This completes the proof that at a minimizer of $\Theta$ the Liapunov function does not increase at the step from $k$ to $k+1$.

