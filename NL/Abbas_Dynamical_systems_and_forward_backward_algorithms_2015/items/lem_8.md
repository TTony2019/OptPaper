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
The theorem `bregman_gap_properties` assumes that \(H\) is a complete real inner product space, with the normed additive commutative group structure required by the typeclass assumptions. Let
\[
\Phi : H \to \operatorname{Set.Ioi}(\bot : \mathrm{EReal})
\]
be an extended-real-valued function whose values lie strictly above the bottom element of \(\mathrm{EReal}\), and assume
\[
h\Phi : \Phi \in \mathrm{ERealFunction.gammaZero}\;H.
\]
Further data are a set \(S \subseteq H\), a map \(B : H \to H\), curves \(x, v : \mathbb R \to H\), and a point \(z \in H\).

The assumptions are:

- \(hz : z \in S\).
- For every \(t \ge 0\), \(v(t)\) is in the subdifferential of \(\Phi\) at \(x(t)\):
  \[
  \forall t,\; 0 \le t \implies v(t)\in \mathrm{ERealFunction.subdifferential}\;\Phi\;(x(t)).
  \]
- For every \(w \in S\), \(-B(w)\) is in the subdifferential of \(\Phi\) at \(w\):
  \[
  \forall w,\; w\in S \implies -B(w)\in \mathrm{ERealFunction.subdifferential}\;\Phi\;w.
  \]
- For every \(b>0\), the curves \(x\) and \(v\) are absolutely continuous on \([0,b]\).
- For every \(b>0\), almost everywhere on \([0,b]\) with respect to Lebesgue measure restricted to \([0,b]\), the curve \(x\) has derivative \(\operatorname{deriv}x(t)\), and similarly \(v\) has derivative \(\operatorname{deriv}v(t)\).
- For every \(b>0\), \(v\) and \(\operatorname{deriv}x\) are \(L^2\) on \([0,b]\) with respect to restricted Lebesgue measure.
- The function \(g:\mathbb R \to \mathbb R\) is defined pointwise by
  \[
  g(t)
  =
  (\Phi(z):\mathrm{EReal}).\mathrm{toReal}
  -
  (\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
  -
  \langle z-x(t), v(t)\rangle,
  \]
  where \(\langle \cdot,\cdot\rangle\) denotes the real inner product.

The conclusion is a conjunction of two statements:

1. For every \(t \ge 0\),
   \[
   0 \le g(t).
   \]
2. For almost every \(t \in [0,\infty)\) with respect to Lebesgue measure restricted to \([0,\infty)\),
   \[
   \operatorname{deriv} g(t)
   =
   \langle x(t)-z, \operatorname{deriv}v(t)\rangle.
   \]

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
The proof begins by extracting properness information about \(\Phi\) from the hypothesis \(h\Phi\). The command
```lean
have hdomPhi := (ERealFunction.isProper_of_mem_gammaZero hPhi).2
```
obtains the properness component needed for domain arguments. Using \(hz : z \in S\) and the assumption \(hsolution\), the proof obtains that \(-B z\) is a subgradient of \(\Phi\) at \(z\). Since subdifferentiability implies membership in the effective domain, it concludes
```lean
hzdom : z ∈ ERealFunction.effectiveDomain Phi.
```

The two conclusions are then proved separately using `constructor`.

For the first conclusion, fix \(t\) with \(0 \le t\). The proof applies a subgradient inequality for functions in `gammaZero`:
```lean
ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero
```
using the subgradient \(v(t)\) at \(x(t)\) and the fact \(z\) is in the effective domain of \(\Phi\). This gives the inequality
\[
(\Phi(x(t)))_{\mathbb R}
+
\langle v(t), z-x(t)\rangle
\le
(\Phi(z))_{\mathbb R}.
\]
After rewriting \(g(t)\) using the definition \(hg\), and commuting the inner product with `real_inner_comm`, the goal becomes a linear inequality that `linarith` closes.

For the second conclusion, the proof first proves the derivative equality locally on each interval \([0,T]\), where \(T=n+1\) for a natural number \(n\). It sets \(T = n+1\) and proves \(T>0\) using `positivity`.

The main local step is an application of the library theorem
```lean
subgradient_chain_rule
```
to \(\Phi\), \(x\), \(v\), and \(T\). The proof supplies this theorem with the absolute continuity of \(x\) on \([0,T]\), the subgradient condition for \(v(t)\) on \([0,T]\), the fact that \(x(t)\) lies in the effective domain of \(\Phi\), the almost-everywhere derivative condition for \(x\), and the \(L^2\) hypotheses for \(v\) and \(\operatorname{deriv}x\). The chain rule gives two pieces of information used later:

- \(hchain.1\) is an almost-everywhere differentiability statement for the function
  \[
  s \mapsto (\Phi(x(s)):\mathrm{EReal}).\mathrm{toReal}.
  \]
- \(hchain.2\) is the almost-everywhere derivative formula
  \[
  \operatorname{deriv}\bigl(s\mapsto (\Phi(x(s)):\mathrm{EReal}).\mathrm{toReal}\bigr)(t)
  =
  \langle v(t), \operatorname{deriv}x(t)\rangle.
  \]

The proof then uses `filter_upwards` to collect the following almost-everywhere facts on \([0,T]\):

- the derivative condition for \(x\),
- the derivative condition for \(v\),
- the chain-rule derivative formula for \(\Phi(x(t))\),
- membership in the interval \([0,T]\),
- differentiability of \(s \mapsto (\Phi(x(s)))_{\mathbb R}\).

On this set of points \(t\), the proof constructs several derivative facts:

1. The function
   \[
   s \mapsto (\Phi(x(s)):\mathrm{EReal}).\mathrm{toReal}
   \]
   has derivative
   \[
   \operatorname{deriv}\bigl(s\mapsto (\Phi(x(s)):\mathrm{EReal}).\mathrm{toReal}\bigr)(t).
   \]

2. The inner-product term
   \[
   s \mapsto \langle z-x(s), v(s)\rangle
   \]
   has derivative
   \[
   \langle z-x(t), \operatorname{deriv}v(t)\rangle
   -
   \langle \operatorname{deriv}x(t), v(t)\rangle.
   \]
   This is obtained using the derivative rules for \(x\) and \(v\), followed by simplification with `simp` and `ring`.

3. The combined expression
   \[
   s \mapsto
   (\Phi(z):\mathrm{EReal}).\mathrm{toReal}
   -
   (\Phi(x(s)):\mathrm{EReal}).\mathrm{toReal}
   -
   \langle z-x(s), v(s)\rangle
   \]
   has derivative
   \[
   \langle x(t)-z, \operatorname{deriv}v(t)\rangle.
   \]
   The proof uses `convert` and the chain-rule formula \(hchain.2\) to cancel the terms involving \(\operatorname{deriv}x(t)\), and uses `ring` for the remaining algebra.

Since \(g\) is pointwise equal to that combined expression by \(hg\), rewriting the goal and applying the derivative equality yields
\[
\operatorname{deriv} g(t)
=
\langle x(t)-z, \operatorname{deriv}v(t)\rangle
\]
almost everywhere on \([0,T]\).

Finally, the proof observes that
\[
[0,\infty)
=
\bigcup_{n\in\mathbb N} [0,n+1].
\]
For any \(t \ge 0\), the lemma `exists_nat_ge` gives a natural number \(n\) with \(t \le n+1\). Conversely, every interval \([0,n+1]\) lies in \([0,\infty)\). The proof then applies
```lean
MeasureTheory.ae_restrict_iUnion_iff
```
to lift the local almost-everywhere equality on each interval \([0,n+1]\) to the whole union \([0,\infty)\).

