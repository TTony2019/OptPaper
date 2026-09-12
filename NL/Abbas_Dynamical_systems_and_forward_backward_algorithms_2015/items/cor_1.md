## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/cor_1.lean`

## Lean statement
```lean
theorem strong_convex_solution_unique_and_convergent {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H)
    (S : Set H) (x v : ℝ → H) (lam : ℝ)
    (mu beta : ℝ) (hS : S.Nonempty) (hlam : 0 < lam) (hmu : 0 < mu)
    (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (hvL2 : ∀ b, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧
      ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi)
    (hweak : ∃ xinf ∈ S,
      Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop
        (nhds (toWeakSpace ℝ H xinf)))
    (hsolution : ∀ z, z ∈ S → -B z ∈ ERealFunction.subdifferential Phi z)
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hstrong_support : ∃ m : ℝ, 0 < m ∧ ∀ {a u y : H},
      u ∈ ERealFunction.subdifferential Phi a →
      y ∈ ERealFunction.effectiveDomain Phi →
      m / 2 * ‖y - a‖ ^ 2 ≤
        (Phi y : EReal).toReal - (Phi a : EReal).toReal - inner ℝ u (y - a)) :
    ∃ z, S = {z} ∧ Tendsto x atTop (nhds z)
```

## Statement explanation
The declaration is a theorem in a real Hilbert space $H$, meaning that $H$ is a complete normed additive commutative group equipped with a real inner product. The function $\Phi : H \to \operatorname{EReal}$ takes values strictly greater than $\bot$, where $\bot$ is the bottom element of the extended reals, so $\Phi$ never takes the value $-\infty$. The hypothesis $hPhi$ says that $\Phi$ belongs to `ERealFunction.gammaZero H`. The provided excerpt defines the ambient class $\Gamma(H)$ as the convex, lower semicontinuous functions; the zero-class is the corresponding properness/domain class used by the subgradient theory. The proof itself only passes this hypothesis unchanged to `proposition_2_16`.

The other objects are a single-valued operator $B : H \to H$, a nonempty set $S \subseteq H$ of candidate solutions, two trajectories $x,v : \mathbb R \to H$, and real parameters $\lambda,\mu,\beta$. The assumptions on the parameters are $0<\lambda$, $0<\mu$, $\mu\lambda=1$, and $0<\beta$. The hypothesis $hB$ says that $B$ is $\beta$-cocoercive on all of $H$. In the proof this is used in the form that for any $y,z\in H$,

$$
\beta\|By-Bz\|^2 \le \langle y-z, By-Bz\rangle,
$$

so in particular the inner product $\langle y-z, By-Bz\rangle$ is nonnegative.

The trajectory hypotheses say that $x$ and $v$ are absolutely continuous on every $[0,b]$ with $b>0$, and that for every $T>0$, almost every $t\in[0,T]$ satisfies

$$
\operatorname{HasDerivAt}\, x\,(\operatorname{deriv} x(t))\,t,
\qquad
\operatorname{HasDerivAt}\, v\,(\operatorname{deriv} v(t))\,t.
$$

Thus $x$ and $v$ are locally absolutely continuous and almost everywhere differentiable with the stated derivatives. The hypotheses $hvL2$ and $hdxL2$ say that $v$ and $\operatorname{deriv} x$ are in $L^2$ on every finite interval $[0,b]$. The hypothesis $hsubgradient$ says that for every $t\ge 0$,

$$
v(t)\in \partial\Phi(x(t)).
$$

The domain hypothesis $hdom$ says that for every $t\ge 0$, $x(t)\in\operatorname{dom}\Phi$, and that every $w\in S$ lies in $\operatorname{dom}\Phi$. The weak convergence hypothesis $hweak$ says that there exists $x_\infty\in S$ such that $x(t)$ converges weakly to $x_\infty$ as $t\to\infty$. The solution hypothesis $hsolution$ says that for every $z\in S$,

$$
-Bz\in \partial\Phi(z),
$$

equivalently $0\in Bz+\partial\Phi(z)$. The orbit equation $horbit$ says that for almost every $t\in[0,\infty)$,

$$
v(t)\in \partial\Phi(x(t))
\quad\text{and}\quad
\lambda\,\dot x(t)+\dot v(t)+v(t)+B(x(t))=0.
$$

Finally, $hstrong_support$ is a strong-convexity hypothesis on $\Phi$: there exists $m>0$ such that for all $a,u,y\in H$, if $u\in\partial\Phi(a)$ and $y\in\operatorname{dom}\Phi$, then

$$
\frac m2\|y-a\|^2
\le
(\Phi y)_{\mathbb R}-(\Phi a)_{\mathbb R}
-\langle u,y-a\rangle.
$$

Here $(\Phi y)_{\mathbb R}$ denotes the real part of the extended-real value $\Phi y$. This is the subgradient form of strong convexity with modulus $m$.

The conclusion is that there exists $z$ such that

$$
S=\{z\}
\quad\text{and}\quad
x(t)\to z \text{ strongly in }H \text{ as }t\to\infty.
$$

Thus the theorem says that, under the dynamical system, cocoercivity, and strong convexity assumptions, the solution set is a singleton and the trajectory $x$ converges strongly to that unique solution.

## Lean proof
```lean
by
  rcases hS with ⟨z, hz⟩
  rcases hstrong_support with ⟨m, hm, hsupp⟩
  have hS_singleton : S = {z} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hz, ?_⟩
    intro y hy
    have h1 := hsupp (a := z) (u := -B z) (y := y) (hsolution z hz) (hdom.2 y hy)
    have h2 := hsupp (a := y) (u := -B y) (y := z) (hsolution y hy) (hdom.2 z hz)
    have hineq := hB.ineq ⟨y, Set.mem_univ y⟩ ⟨z, Set.mem_univ z⟩
    have hinner : 0 ≤ inner ℝ (y - z) (B y - B z) := by
      exact le_trans (mul_nonneg hbeta.le (sq_nonneg _)) hineq
    have hdist : m * ‖y - z‖ ^ 2 ≤ 0 := by
      have hsum : m * ‖y - z‖ ^ 2 ≤ -inner ℝ (y - z) (B y - B z) := by
        have h1' : m / 2 * ‖y - z‖ ^ 2 ≤
            (Phi y : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (y - z) (B z) := by
          simpa [inner_neg_left, real_inner_comm] using h1
        have h2' : m / 2 * ‖y - z‖ ^ 2 ≤
            (Phi z : EReal).toReal - (Phi y : EReal).toReal -
              inner ℝ (y - z) (B y) := by
          have hi : inner ℝ (B y) (z - y) = -inner ℝ (y - z) (B y) := by
            rw [← neg_sub, inner_neg_right, real_inner_comm (B y) (y - z)]
          rw [inner_neg_left, hi, norm_sub_rev] at h2
          simpa using h2
        have hinner_eq : inner ℝ (y - z) (B y - B z) =
            inner ℝ (y - z) (B y) - inner ℝ (y - z) (B z) := by
          rw [inner_sub_right]
        nlinarith [h1', h2', hinner_eq]
      exact le_trans hsum (neg_nonpos.mpr hinner)
    have hzero : ‖y - z‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖y - z‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  have hp := proposition_2_16 S Phi hPhi B x v z lam mu beta ⟨z, hz⟩ hz hlam hmu
    hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2
    horbit hsolution hdom hweak
  have hF_lim := hp.2.1
  let gamma : ℝ := m / 2
  have hgamma : 0 < gamma := by dsimp [gamma]; linarith
  have hnorm_lim : Tendsto (fun t => ‖x t - z‖) atTop (nhds 0) := by
    have hsquare : Tendsto (fun t => ‖x t - z‖ ^ 2) atTop (nhds 0) := by
      refine squeeze_zero' (g := fun t => gamma⁻¹ *
          ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
            inner ℝ (B z) (x t - z)))
        (Eventually.of_forall (fun t => sq_nonneg _)) ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        have hgap := hsupp (a := z) (u := -B z) (y := x t) (hsolution z hz) (hdom.1 t ht)
        have hgap' : gamma * ‖x t - z‖ ^ 2 ≤
            (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z) := by
          simpa [gamma, inner_neg_left] using hgap
        have hnonneg : 0 ≤
            gamma⁻¹ * ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z)) := by
          have : 0 ≤ (Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z) := by nlinarith [hgap']
          exact mul_nonneg (inv_nonneg.mpr hgamma.le) this
        have hsq : ‖x t - z‖ ^ 2 ≤ gamma⁻¹ *
            ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
              inner ℝ (B z) (x t - z)) := by
          calc
            ‖x t - z‖ ^ 2 = gamma⁻¹ * (gamma * ‖x t - z‖ ^ 2) := by
              rw [← mul_assoc, inv_mul_cancel₀ hgamma.ne', one_mul]
            _ ≤ gamma⁻¹ * ((Phi (x t) : EReal).toReal - (Phi z : EReal).toReal +
                inner ℝ (B z) (x t - z)) :=
              mul_le_mul_of_nonneg_left hgap' (inv_nonneg.mpr hgamma.le)
        exact hsq
      · simpa using (hF_lim.const_mul gamma⁻¹)
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsquare
  have hsub_lim : Tendsto (fun t => x t - z) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_lim
  exact ⟨z, hS_singleton, tendsto_sub_nhds_zero_iff.mp hsub_lim⟩
```

## Proof explanation
The proof begins by using `rcases hS with ⟨z, hz⟩` to choose an element $z\in S$, and `rcases hstrong_support with ⟨m, hm, hsupp⟩` to choose the strong-convexity modulus $m>0$ together with the inequality $hsupp$.

First the proof shows that $S$ is the singleton $\{z\}$. It applies `Set.eq_singleton_iff_unique_mem.mpr`, which reduces the goal $S=\{z\}$ to proving two things: that $z\in S$, supplied by $hz$, and that every $y\in S$ is equal to $z$. The command `intro y hy` introduces an arbitrary $y\in S$ and the proof `hy` of membership.

For this arbitrary $y\in S$, the proof applies the strong-convexity inequality $hsupp$ twice. First, with $a=z$, $u=-Bz$, and the second variable equal to $y$, using $hsolution z hz$ to know that $-Bz\in\partial\Phi(z)$ and $hdom.2 y hy$ to know that $y\in\operatorname{dom}\Phi$. This gives

$$
\frac m2\|y-z\|^2
\le
(\Phi y)_{\mathbb R}-(\Phi z)_{\mathbb R}
-\langle -Bz,y-z\rangle.
$$

Using $\langle -Bz,y-z\rangle=-\langle Bz,y-z\rangle=-\langle y-z,Bz\rangle$, the proof rewrites this as

$$
\frac m2\|y-z\|^2
\le
(\Phi y)_{\mathbb R}-(\Phi z)_{\mathbb R}
+\langle y-z,Bz\rangle.
$$

Second, with $a=y$, $u=-By$, and the second variable equal to $z$, using $hsolution y hy$ to know that $-By\in\partial\Phi(y)$ and $hdom.2 z hz$ to know that $z\in\operatorname{dom}\Phi$, the proof obtains

$$
\frac m2\|z-y\|^2
\le
(\Phi z)_{\mathbb R}-(\Phi y)_{\mathbb R}
-\langle -By,z-y\rangle.
$$

The proof rewrites the inner product term using $\langle -By,z-y\rangle=-\langle By,z-y\rangle$, then uses $\langle By,z-y\rangle=-\langle y-z,By\rangle$, and replaces $\|z-y\|$ by $\|y-z\|$. The result is

$$
\frac m2\|y-z\|^2
\le
(\Phi z)_{\mathbb R}-(\Phi y)_{\mathbb R}
-\langle y-z,By\rangle.
$$

Next the proof uses cocoercivity. The call `hB.ineq` gives the inequality

$$
\beta\|By-Bz\|^2
\le
\langle y-z,By-Bz\rangle.
$$

Because $\beta>0$ and $\|By-Bz\|^2\ge 0$, the left-hand side is nonnegative, so the inner product on the right is nonnegative:

$$
0\le \langle y-z,By-Bz\rangle.
$$

Adding the two strong-convexity inequalities, the $\Phi$-terms cancel. Using

$$
\langle y-z,By-Bz\rangle
=
\langle y-z,By\rangle-\langle y-z,Bz\rangle,
$$

the proof obtains

$$
m\|y-z\|^2
\le
-\langle y-z,By-Bz\rangle.
$$

Since the inner product is nonnegative, the right-hand side is nonpositive, hence

$$
m\|y-z\|^2\le 0.
$$

Because $m>0$ and $\|y-z\|^2\ge 0$, the proof concludes that $\|y-z\|^2=0$. Therefore $\|y-z\|=0$, then $y-z=0$, and finally $y=z$. This proves uniqueness of the element of $S$, so $S=\{z\}$.

The proof then invokes `proposition_2_16`. This proposition applies to the same Hilbert space, the same $\Phi$, $B$, $S$, $x$, $v$, and parameters, with the chosen element $z\in S$. Its conclusion includes the statement that the function

$$
F(t)
=
(\Phi(x(t)))_{\mathbb R}-(\Phi(z))_{\mathbb R}
+\langle Bz,x(t)-z\rangle
$$

is integrable on $[0,\infty)$, that

$$
F(t)\to 0 \quad\text{as }t\to\infty,
$$

and that there exists a weak limit point in $S$ together with convergence of $\Phi(x(t))$ to its value. The proof only uses the second conjunct, extracted as `hp.2.1`, which is precisely the convergence

$$
F(t)\to 0.
$$

The proof next defines

$$
\gamma=\frac m2.
$$

Since $m>0$, `linarith` proves $\gamma>0$. The goal is to prove

$$
\|x(t)-z\|\to 0.
$$

The proof first proves the squared norm converges to zero by a squeeze argument. For $t\ge 0$, applying the strong-convexity inequality $hsupp$ with $a=z$, $u=-Bz$, and the second variable equal to $x(t)$, using $hsolution z hz$ and $hdom.1 t ht$, gives

$$
\gamma\|x(t)-z\|^2
\le
F(t).
$$

The left-hand side is nonnegative, so $F(t)\ge 0$. Since $\gamma^{-1}\ge 0$, multiplying by $\gamma^{-1}$ gives

$$
0\le \|x(t)-z\|^2
\le
\gamma^{-1}F(t)
$$

eventually. The command `filter_upwards [eventually_ge_atTop (0 : ℝ)]` makes the argument eventual in $t$, because the strong-convexity inequality is available only for $t\ge 0$. Since $F(t)\to 0$, the scalar multiple satisfies

$$
\gamma^{-1}F(t)\to 0.
$$

The theorem `squeeze_zero'` then yields

$$
\|x(t)-z\|^2\to 0.
$$

Finally, the proof converts convergence of the square of the norm into convergence of the norm itself. The square-root function is continuous at $0$, and for a nonnegative norm,

$$
\sqrt{\|x(t)-z\|^2}=\|x(t)-z\|.
$$

Thus composing continuity of $\sqrt{\cdot}$ at $0$ with $\|x(t)-z\|^2\to 0$ gives

$$
\|x(t)-z\|\to 0.
$$

The lemma `tendsto_zero_iff_norm_tendsto_zero.mpr` then gives

$$
x(t)-z\to 0.
$$

Finally, `tendsto_sub_nhds_zero_iff.mp` converts $x(t)-z\to 0$ into

$$
x(t)\to z.
$$

Together with the already established equality $S=\{z\}$, this proves the desired conclusion

$$
\exists z,\quad S=\{z\}
\quad\text{and}\quad
x(t)\to z \text{ strongly as }t\to\infty.
$$

