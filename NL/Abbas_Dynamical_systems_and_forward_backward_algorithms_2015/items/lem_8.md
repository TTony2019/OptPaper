## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/lem_8.lean`

## Lean statement
```lean
theorem bregman_gap_properties {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (S : Set H) (B : H → H) (x v : ℝ → H) (z : H)
    (hz : z ∈ S)
    (hsubgradient : ∀ t, 0 ≤ t →
      v t ∈ ERealFunction.subdifferential Phi (x t))
    (hsolution : ∀ w, w ∈ S → -B w ∈ ERealFunction.subdifferential Phi w)
    (hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ b : ℝ, 0 < b →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ b : ℝ, 0 < b →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 b), HasDerivAt v (deriv v t) t)
    (hvL2 : ∀ b : ℝ, 0 < b → MemLp v 2 (volume.restrict (Set.Icc 0 b)))
    (hdxL2 : ∀ b : ℝ, 0 < b → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 b)))
    (g : ℝ → ℝ)
    (hg : ∀ t, g t = (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
      inner ℝ (z - x t) (v t)) :
    (∀ t, 0 ≤ t → 0 ≤ g t) ∧
    ∀ᵐ t ∂volume.restrict (Set.Ici 0), deriv g t = inner ℝ (x t - z) (deriv v t)
```

## Statement explanation
The theorem `bregman_gap_properties` is stated in a complete real inner product space $H$, hence a real Hilbert space. It fixes an extended-real-valued function $\Phi$ whose values lie in $\mathbb R\cup\{+\infty\}$ rather than in the full extended real line; the hypothesis `hPhi` says $\Phi\in\Gamma_0(H)$, i.e. $\Phi$ is a proper convex lower semicontinuous extended-real function in the usual convex-analysis sense. The notation $(\Phi(x))_{\mathbb R}$ denotes the `toReal` value of the extended real $\Phi(x)$, and $\partial\Phi$ denotes its subdifferential.

The data are a set $S\subseteq H$, a map $B:H\to H$, two curves $x,v:\mathbb R\to H$, and a point $z\in H$ with $z\in S$. The main hypotheses are:

$$
\forall t\ge 0,\quad v(t)\in \partial\Phi(x(t)),
$$

so $v(t)$ is a subgradient of $\Phi$ at $x(t)$ for every nonnegative time; and

$$
\forall w\in S,\quad -B(w)\in \partial\Phi(w),
$$

which is the stationarity condition $0\in B(w)+\partial\Phi(w)$ for every $w\in S$.

There are also regularity assumptions. For every $b>0$, the curves $x$ and $v$ are absolutely continuous on $[0,b]$, and almost everywhere on $[0,b]$ they have derivatives $\operatorname{deriv}x(t)$ and $\operatorname{deriv}v(t)$. Moreover $v$ and $\operatorname{deriv}x$ are square-integrable on each $[0,b]$. These are exactly the hypotheses needed to apply the subgradient chain rule on finite intervals.

A real-valued function $g:\mathbb R\to\mathbb R$ is then assumed to satisfy, for every $t$,

$$
g(t)=(\Phi(z))_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t),v(t)\rangle .
$$

This is the Bregman gap between $z$ and $x(t)$, measured using the subgradient $v(t)$.

The conclusion is a conjunction:

$$
\bigl(\forall t,\;0\le t\Rightarrow 0\le g(t)\bigr)
$$

and, almost everywhere with respect to Lebesgue measure restricted to $[0,\infty)$,

$$
\operatorname{deriv}g(t)=\langle x(t)-z,\operatorname{deriv}v(t)\rangle .
$$

Thus the Bregman gap is nonnegative along nonnegative times, and its derivative is given almost everywhere by the inner product of $x(t)-z$ with the derivative of $v$.

## Lean proof
```lean
by
  have hdomPhi := (ERealFunction.isProper_of_mem_gammaZero hPhi).2
  have hzdom : z ∈ ERealFunction.effectiveDomain Phi :=
    ERealFunction.SubdifferentiableAt.mem_effectiveDomain hdomPhi
      ⟨-B z, hsolution z hz⟩
  constructor
  · intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsubgradient t ht) hzdom
    rw [hg t]
    rw [real_inner_comm]
    linarith
  · have hlocal : ∀ n : ℕ,
        ∀ᵐ t ∂volume.restrict (Set.Icc 0 ((n : ℝ) + 1)),
          deriv g t = inner ℝ (x t - z) (deriv v t) := by
      intro n
      let T : ℝ := (n : ℝ) + 1
      have hT : 0 < T := by dsimp [T]; positivity
      have hchain := subgradient_chain_rule Phi hPhi x v T hT (hx_ac T hT)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hsubgradient t ht.1)
        (by
          intro t ht
          exact ERealFunction.SubdifferentiableAt.mem_effectiveDomain hdomPhi
            ⟨v t, hsubgradient t ht.1⟩)
        (hx_deriv T hT)
        (hvL2 T hT) (hdxL2 T hT)
      filter_upwards [hx_deriv T hT, hv_deriv T hT, hchain.2,
        ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae hchain.1.ae_differentiableAt] with
        t hxt hvt hphit ht hphid
      have hphi : HasDerivAt (fun s => (Phi (x s) : EReal).toReal)
          (deriv (fun s => (Phi (x s) : EReal).toReal) t) t :=
        (hphid (by simpa [Set.uIcc_of_le hT.le] using ht)).hasDerivAt
      have hin : HasDerivAt (fun s => inner ℝ (z - x s) (v s))
          (inner ℝ (z - x t) (deriv v t) - inner ℝ (deriv x t) (v t)) t := by
        convert ((hasDerivAt_const (x := t) z).sub hxt).inner ℝ hvt using 1
        simp [inner_sub_left, real_inner_comm]
        ring
      have hraw : HasDerivAt (fun s => (Phi z : EReal).toReal -
          (Phi (x s) : EReal).toReal - inner ℝ (z - x s) (v s))
          (inner ℝ (x t - z) (deriv v t)) t := by
        have h := ((hasDerivAt_const (x := t) ((Phi z : EReal).toReal)).sub hphi).sub hin
        convert h using 1
        simp only [hphit, sub_eq_add_neg, real_inner_comm]
        rw [show x t + -z = -(z + -x t) by abel, inner_neg_right]
        ring
      have hgeq : g = fun s => (Phi z : EReal).toReal -
          (Phi (x s) : EReal).toReal - inner ℝ (z - x s) (v s) := by
        funext s
        exact hg s
      rw [hgeq]
      exact hraw.deriv
    rw [show Set.Ici (0 : ℝ) = ⋃ n : ℕ, Set.Icc 0 ((n : ℝ) + 1) by
      ext t
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_ge t
        exact Set.mem_iUnion.2 ⟨n, ⟨ht, by linarith⟩⟩
      · intro ht
        rcases Set.mem_iUnion.1 ht with ⟨n, hn⟩
        exact hn.1]
    exact (MeasureTheory.ae_restrict_iUnion_iff _ _).2 hlocal
```

## Proof explanation
The proof begins by extracting properness information from $\Phi\in\Gamma_0(H)$. The theorem `isProper_of_mem_gammaZero` says that a function in $\Gamma_0(H)$, viewed as an extended-real-valued function, is proper. The proof takes the second component of this properness assertion as `hdomPhi`. In this setting that component controls the failure of the value $-\infty$. The proof then uses `SubdifferentiableAt.mem_effectiveDomain` together with the stationarity condition. Since `hsolution z hz` gives $-B(z)\in\partial\Phi(z)$, the lemma implies that $z$ lies in the effective domain of $\Phi$, meaning $(\Phi(z))_{\mathbb R}$ is finite. This fact is named `hzdom`.

The proof then uses `constructor` to split the desired conjunction into its two parts.

For the first part, `intro t ht` fixes an arbitrary $t$ with $0\le t$. The proof applies `subgradient_ineq_toReal_of_mem_gammaZero`. That lemma states that if $f\in\Gamma_0(H)$, $u\in\partial f(x)$, and $y$ lies in the effective domain of $f$, then

$$
(f(y))_{\mathbb R}\ge (f(x))_{\mathbb R}+\langle u,y-x\rangle .
$$

Specialized here to $f=\Phi$, $x=x(t)$, $u=v(t)$, and $y=z$, and using `hsubgradient t ht` together with `hzdom`, it gives

$$
(\Phi(z))_{\mathbb R}\ge (\Phi(x(t)))_{\mathbb R}
+\langle v(t),z-x(t)\rangle .
$$

The proof rewrites $g(t)$ using `hg t`, obtaining

$$
g(t)=(\Phi(z))_{\mathbb R}-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t),v(t)\rangle .
$$

It then rewrites $\langle z-x(t),v(t)\rangle$ as $\langle v(t),z-x(t)\rangle$ using `real_inner_comm`, the symmetry of the real inner product. The inequality now directly implies $0\le g(t)$, and `linarith` finishes this linear real inequality.

For the second part, the proof proves the derivative identity locally on every interval $[0,T]$ with $T=n+1$ for $n\in\mathbb N$, and then passes to the countable union $[0,\infty)=\bigcup_{n\in\mathbb N}[0,n+1]$.

For a fixed $n$, it sets $T=n+1$ and proves $0<T$ using `positivity`. It then applies `subgradient_chain_rule`. That theorem says: if $\Phi\in\Gamma_0(H)$, $x$ is absolutely continuous on $[0,b]$, $v(t)\in\partial\Phi(x(t))$ for almost every $t\in[0,b]$, $x(t)$ lies in the effective domain of $\Phi$ for every $t\in[0,b]$, $x$ is differentiable almost everywhere with derivative $\operatorname{deriv}x(t)$, and both $v$ and $\operatorname{deriv}x$ are in $L^2([0,b])$, then the function

$$
t\mapsto (\Phi(x(t)))_{\mathbb R}
$$

is absolutely continuous on $[0,b]$, and for almost every $t\in[0,b]$,

$$
\operatorname{deriv}\bigl(t\mapsto (\Phi(x(t)))_{\mathbb R}\bigr)(t)
=\langle v(t),\operatorname{deriv}x(t)\rangle .
$$

In the proof, the almost-everywhere subgradient hypothesis is supplied by restricting `hsubgradient` to the interval using `ae_restrict_mem measurableSet_Icc`: almost every $t$ in the restricted interval lies in $[0,T]$, so $t\ge0$, and then `hsubgradient t ht.1` applies. The effective-domain hypothesis is obtained pointwise from `SubdifferentiableAt.mem_effectiveDomain`: since $v(t)\in\partial\Phi(x(t))$, the point $x(t)$ lies in the effective domain of $\Phi$. The remaining inputs are `hx_ac T hT`, `hx_deriv T hT`, `hvL2 T hT`, and `hdxL2 T hT`. Let $\phi(t)=(\Phi(x(t)))_{\mathbb R}$. The chain rule returns that $\phi$ is absolutely continuous on $[0,T]$ and that almost everywhere on $[0,T]$,

$$
\operatorname{deriv}\phi(t)=\langle v(t),\operatorname{deriv}x(t)\rangle .
$$

Next, the proof uses `filter_upwards` to combine several almost-everywhere facts on $[0,T]$: differentiability of $x$, differentiability of $v$, the chain-rule derivative identity for $\phi$, membership of $t$ in $[0,T]$, and almost-everywhere differentiability of $\phi$ coming from its absolute continuity. The fact `hchain.1.ae_differentiableAt` says that the absolutely continuous function $\phi$ is differentiable almost everywhere; after restricting to $[0,T]$, it gives differentiability of $\phi$ at the current $t$. Since $0<T$, the unordered interval `uIcc 0 T` is the same as the ordered interval $[0,T]$, so the proof converts the membership `ht` accordingly. Then `.hasDerivAt` turns differentiability of $\phi$ at $t$ into the statement that $\phi$ has derivative

$$
\operatorname{deriv}\phi(t)
$$

at $t$.

The proof then computes the derivative of

$$
t\mapsto \langle z-x(t),v(t)\rangle .
$$

Using the constant rule, the difference rule, and the product rule for the real inner product, its derivative is

$$
\langle -\operatorname{deriv}x(t),v(t)\rangle
+\langle z-x(t),\operatorname{deriv}v(t)\rangle ,
$$

which is rewritten as

$$
\langle z-x(t),\operatorname{deriv}v(t)\rangle
-\langle \operatorname{deriv}x(t),v(t)\rangle .
$$

The Lean proof implements this by applying `HasDerivAt.sub` and `HasDerivAt.inner`, then simplifying with `inner_sub_left` and `real_inner_comm`.

Using this, the proof computes the derivative of the full expression

$$
t\mapsto (\Phi(z))_{\mathbb R}
-(\Phi(x(t)))_{\mathbb R}
-\langle z-x(t),v(t)\rangle .
$$

The derivative of the constant term $(\Phi(z))_{\mathbb R}$ is $0$. Subtracting the derivative of the $\Phi(x(t))$ term and the derivative of the inner-product term gives

$$
-\langle v(t),\operatorname{deriv}x(t)\rangle
-\langle z-x(t),\operatorname{deriv}v(t)\rangle
+\langle \operatorname{deriv}x(t),v(t)\rangle .
$$

By symmetry of the real inner product, the first and third terms cancel, leaving

$$
-\langle z-x(t),\operatorname{deriv}v(t)\rangle
=\langle x(t)-z,\operatorname{deriv}v(t)\rangle .
$$

The Lean proof carries out these algebraic rearrangements with `convert`, `simp only [hphit, sub_eq_add_neg, real_inner_comm]`, `rw` using $x(t)-z=-(z-x(t))$, `inner_neg_right`, and `ring`.

The proof then uses `funext` and `hg` to show that $g$ is pointwise equal to this explicit expression. Rewriting with this function equality reduces the goal to the just-proved derivative statement, and `hraw.deriv` converts the `HasDerivAt` fact into the equality of `deriv` values. This proves the local almost-everywhere derivative identity on each interval $[0,T]$.

Finally, the proof rewrites

$$
[0,\infty)=\bigcup_{n\in\mathbb N}[0,n+1].
$$

For $t\ge0$, `exists_nat_ge t` chooses a natural number $n$ with $t\le n$, hence $t\le n+1$. Conversely, membership in some $[0,n+1]$ implies $0\le t$. The theorem `MeasureTheory.ae_restrict_iUnion_iff` says that, for a countable union of sets, almost everywhere on the union with respect to the restricted measure is equivalent to almost everywhere on each member of the union. Applying this to the countable family $[0,n+1]$ and the local facts just proved gives the desired almost-everywhere derivative identity on $[0,\infty)$.

