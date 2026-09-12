## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/prop_2.lean`

## Lean statement
```lean
theorem subgradient_gap_tendsto_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (z : H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hz : z ∈ S) (hlam : 0 < lam)
    (hmu : 0 < mu) (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hvL2 : ∀ T, 0 < T → MemLp v 2 (volume.restrict (Set.Icc 0 T)))
    (hdxL2 : ∀ T, 0 < T → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 T)))
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S ↔ -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : ∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi)
    (hdomS : ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi) :
    Tendsto (fun t ↦ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
      inner ℝ (v t) (z - x t)) atTop (nhds 0)
```

## Statement explanation
The declaration `subgradient_gap_tendsto_zero` is a convergence theorem for a continuous-time dynamical system in a real Hilbert space \(H\). The data are a set \(S\subseteq H\), a point \(z\in S\), an extended-real function \(\Phi:H\to\mathrm{EReal}\) whose values lie above the bottom element of \(\mathrm{EReal}\), a map \(B:H\to H\), two trajectories \(x,v:\mathbb R\to H\), and positive parameters \(\lambda,\mu,\beta\) satisfying \(\mu\lambda=1\).

The hypotheses say the following. The set \(S\) is nonempty and \(z\in S\). The function \(\Phi\) belongs to the class `ERealFunction.gammaZero H`; in the proof this membership is used exactly as the hypothesis that permits the cited subgradient inequality for \(\Phi\). The map \(B\) is \(\beta\)-cocoercive on all of \(H\). The trajectories \(x\) and \(v\) are absolutely continuous on every interval \([0,b]\) with \(b>0\), their derivatives exist almost everywhere on every \([0,T]\) with \(T>0\), and \(v\) and \(\operatorname{deriv} x\) are \(L^2\) on every such interval. For every \(t\ge 0\), the vector \(v(t)\) is a subgradient of \(\Phi\) at \(x(t)\), i.e.
\[
v(t)\in \partial \Phi(x(t)).
\]
Almost everywhere for \(t\ge 0\), the dynamical equation
\[
\lambda \operatorname{deriv} x(t)+\operatorname{deriv} v(t)+v(t)+B(x(t))=0
\]
holds. For every \(w\), membership in \(S\) is equivalent to
\[
-B(w)\in \partial \Phi(w).
\]
Finally, \(x(t)\) lies in the effective domain of \(\Phi\) for every \(t\ge 0\), and every point of \(S\) lies in the effective domain of \(\Phi\).

The definition of the subdifferential used here is
\[
u\in \partial \Phi(x)
\quad\Longleftrightarrow\quad
\forall y,\quad
\langle y-x,u\rangle+\Phi(x)\le \Phi(y),
\]
with the inner product taken over \(\mathbb R\). The cited theorem `subgradient_ineq_toReal_of_mem_gammaZero` turns this into the real-valued inequality
\[
(\Phi(y):\mathrm{EReal}).\mathrm{toReal}
\ge
(\Phi(x):\mathrm{EReal}).\mathrm{toReal}
+
\langle u,y-x\rangle
\]
whenever \(u\in \partial \Phi(x)\) and \(y\) is in the effective domain of \(\Phi\).

The conclusion of `subgradient_gap_tendsto_zero` is
\[
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
-
\langle v(t),z-x(t)\rangle
\longrightarrow 0
\qquad (t\to\infty).
\]
Because \(v(t)\in \partial \Phi(x(t))\), the subgradient inequality implies that this quantity is nonnegative whenever \(z\) is in the effective domain of \(\Phi\). Thus the theorem says that the subgradient or duality gap between the trajectory point \(x(t)\) and the fixed point \(z\) tends to \(0\).

## Lean proof
```lean
by
  have hnonneg : ∀ t, 0 ≤ t → 0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
      inner ℝ (v t) (z - x t) := by
    intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsubgradient t ht) (hdomS z hz)
    linarith
  have horbit_pair : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ici, horbit] with t ht hEq
    exact ⟨hsubgradient t ht, hEq⟩
  have hLyapunov := proposition_2_12 S Phi hPhi B x v z lam mu beta hS hz
    hlam hmu hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient
    hvL2 hdxL2 horbit_pair (fun w hw => (hsolution w).1 hw) ⟨hdom, hdomS⟩
  obtain ⟨C, hC⟩ := hLyapunov.2.2.2.1
  have hconvergence := theorem_2_8_convergence S Phi hPhi B x v lam beta hS
    hlam hbeta hB horbit hx_ac hv_ac hx_deriv hv_deriv hvL2 hdxL2
    hsubgradient hsolution
  have hvlim : Tendsto (fun t => v t + B z) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => B z) atTop (nhds (B z)) := tendsto_const_nhds
    have h := (hconvergence.2.2.1 z hz).add hconst
    simpa using h
  have hupperlim : Tendsto (fun t => ‖v t + B z‖ * (C + ‖z‖)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => C + ‖z‖) atTop (nhds (C + ‖z‖)) :=
      tendsto_const_nhds
    simpa using hvlim.norm.mul hconst
  have hnonneg' : ∀ᶠ t in atTop,
      0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (v t) (z - x t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hnonneg t ht
  have hupper : ∀ᶠ t in atTop,
      (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
          inner ℝ (v t) (z - x t) ≤ ‖v t + B z‖ * (C + ‖z‖) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hzineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      ((hsolution z).1 hz) (hdom t ht)
    have hxz : ‖x t - z‖ ≤ C + ‖z‖ := by
      calc
        ‖x t - z‖ ≤ ‖x t‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ C + ‖z‖ := add_le_add (hC t ht) le_rfl
    have hinner : inner ℝ (v t + B z) (x t - z) ≤
        ‖v t + B z‖ * ‖x t - z‖ := by
      exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have hmul : ‖v t + B z‖ * ‖x t - z‖ ≤
        ‖v t + B z‖ * (C + ‖z‖) :=
      mul_le_mul_of_nonneg_left hxz (norm_nonneg _)
    have hzineq' : (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal ≤
        inner ℝ (B z) (x t - z) := by
      rw [inner_neg_left] at hzineq
      linarith
    have hgap : (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (v t) (z - x t) ≤ inner ℝ (v t + B z) (x t - z) := by
      rw [show z - x t = -(x t - z) by abel, inner_neg_right, inner_add_left]
      linarith [hzineq']
    exact hgap.trans (hinner.trans hmul)
  exact squeeze_zero' hnonneg' hupper hupperlim
```

## Proof explanation
The proof first establishes that the gap expression is nonnegative. For any \(t\ge 0\), the hypothesis \(hsubgradient\) gives \(v(t)\in \partial \Phi(x(t))\). The hypothesis \(hdomS\) gives \(z\in \operatorname{dom}\Phi\), since \(z\in S\). Applying `subgradient_ineq_toReal_of_mem_gammaZero` with \(f=\Phi\), \(x=x(t)\), \(u=v(t)\), and \(y=z\) yields
\[
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
\ge
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
+
\langle v(t),z-x(t)\rangle .
\]
Rearranging this inequality gives
\[
0\le
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
-
\langle v(t),z-x(t)\rangle .
\]
The tactic `linarith` performs precisely this linear rearrangement over the reals. This proves the local fact `hnonneg`.

Next, the proof forms an almost-everywhere statement that is acceptable to `proposition_2_12`. The original `horbit` hypothesis gives the dynamical equation almost everywhere for \(t\ge 0\). The theorem `ae_restrict_mem measurableSet_Ici` records that almost every point with respect to the restricted measure on \([0,\infty)\) actually belongs to \([0,\infty)\), i.e. satisfies \(t\ge 0\). Combining that with `horbit` and with the pointwise subgradient hypothesis `hsubgradient` gives, almost everywhere for \(t\ge 0\),
\[
v(t)\in \partial \Phi(x(t))
\quad\text{and}\quad
\lambda \operatorname{deriv} x(t)+\operatorname{deriv} v(t)+v(t)+B(x(t))=0.
\]
This is the almost-everywhere conjunction required by `proposition_2_12`; the tactic `filter_upwards` performs the passage from the separate almost-everywhere facts to the combined one.

The proof then invokes `proposition_2_12`. The hypotheses supplied are the nonemptiness of \(S\), the membership \(z\in S\), the positivity and product condition \(\lambda>0\), \(\mu>0\), \(\mu\lambda=1\), \(\beta>0\), the cocoercivity of \(B\), the absolute continuity and a.e. differentiability of \(x\) and \(v\), the \(L^2\) assumptions, the subgradient condition \(v(t)\in \partial \Phi(x(t))\), the almost-everywhere orbit equation, the implication \(w\in S\Rightarrow -B(w)\in \partial \Phi(w)\), and the domain assumptions for \(x(t)\) and for points of \(S\). The conclusion of `proposition_2_12` is a long conjunction. It says that the function
\[
t\mapsto
\frac12\|x(t)-z\|^2
+
\mu\left(
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
-
\langle z-x(t),v(t)\rangle
\right)
\]
is antitone on \([0,\infty)\), that it has a finite limit at \(+\infty\), and it also gives several integrability and boundedness conclusions. The proof extracts from this conjunction the assertion that there exists a real constant \(C\) such that
\[
\|x(t)\|\le C
\qquad\text{for all }t\ge 0.
\]
This is the component `hLyapunov.2.2.2.1`, destructed as `⟨C, hC⟩`.

The proof also invokes `theorem_2_8_convergence`. The hypotheses passed are the nonemptiness of \(S\), the positivity of \(\lambda\) and \(\beta\), the cocoercivity of \(B\), the almost-everywhere orbit equation, the absolute continuity and a.e. differentiability of \(x\) and \(v\), the \(L^2\) assumptions, the subgradient condition, and the equivalence
\[
w\in S \Longleftrightarrow -B(w)\in \partial \Phi(w).
\]
That theorem concludes, among other things, that
\[
\|v(t)+B(x(t))\|\to 0,
\]
that for every \(w\in S\), \(B(x(t))\to B(w)\), that for every \(w\in S\), \(v(t)\to -B(w)\), and that some weak limit of \(x(t)\) lies in \(S\). The proof uses the third component with the fixed point \(z\in S\), obtaining
\[
v(t)\to -B(z).
\]
Adding the constant trajectory \(t\mapsto B(z)\), which tends to \(B(z)\) by `tendsto_const_nhds`, gives
\[
v(t)+B(z)\to (-B(z))+B(z)=0.
\]
This is the statement `hvlim`.

From this convergence, the proof derives that the bounding factor
\[
\|v(t)+B(z)\|(C+\|z\|)
\]
also tends to \(0\). Indeed, taking norms gives
\[
\|v(t)+B(z)\|\to 0,
\]
and multiplying by the constant \(C+\|z\|\), which tends to itself, gives limit \(0\cdot(C+\|z\|)=0\). The tactics `hvlim.norm.mul hconst` and `simpa` implement this limit argument.

The proof then converts the pointwise nonnegativity of the gap to eventual nonnegativity at \(+\infty\). Since \(t\ge 0\) eventually as \(t\to\infty\), the earlier fact `hnonneg` yields
\[
0\le
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
-
\langle v(t),z-x(t)\rangle
\]
eventually. This is `hnonneg'`.

The main remaining step is to prove an eventual upper bound for the same gap by \(\|v(t)+B(z)\|(C+\|z\|)\). For eventually \(t\ge 0\), the proof uses the second direction of the subgradient inequality. Since \(z\in S\), the equivalence `hsolution` gives
\[
-B(z)\in \partial \Phi(z).
\]
Also \(x(t)\in \operatorname{dom}\Phi\) by `hdom`. Applying `subgradient_ineq_toReal_of_mem_gammaZero` with \(f=\Phi\), \(x=z\), \(u=-B(z)\), and \(y=x(t)\) yields
\[
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
\ge
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
+
\langle -B(z),x(t)-z\rangle .
\]
Using \(\langle -B(z),x(t)-z\rangle=-\langle B(z),x(t)-z\rangle\), the tactic `rw [inner_neg_left]` rewrites this to
\[
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
\ge
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
\langle B(z),x(t)-z\rangle .
\]
Rearranging with `linarith` gives
\[
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
\le
\langle B(z),x(t)-z\rangle .
\]
This is `hzineq'`.

The proof then bounds the norm difference \(x(t)-z\). By `norm_sub_le`,
\[
\|x(t)-z\|\le \|x(t)\|+\|z\|,
\]
and by the bound \(hC\),
\[
\|x(t)\|\le C.
\]
Hence
\[
\|x(t)-z\|\le C+\|z\|.
\]
Next, the real inner product is bounded by the product of norms. The proof uses the chain
\[
\langle v(t)+B(z),x(t)-z\rangle
\le
\|v(t)+B(z)\|\,\|x(t)-z\|
\le
\|v(t)+B(z)\|(C+\|z\|),
\]
where the first inequality combines \(a\le |a|\) with the standard estimate \(|\langle u,w\rangle|\le \|u\|\|w\|\), and the second uses multiplication by the nonnegative factor \(\|v(t)+B(z)\|\).

Finally, the proof algebraically compares the gap expression with this inner product. Since
\[
z-x(t)=-(x(t)-z),
\]
we have
\[
-\langle v(t),z-x(t)\rangle
=
\langle v(t),x(t)-z\rangle.
\]
Therefore the gap expression equals
\[
\left[
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
\right]
+
\langle v(t),x(t)-z\rangle .
\]
Using the bound \(hzineq'\), this is at most
\[
\langle B(z),x(t)-z\rangle+\langle v(t),x(t)-z\rangle
=
\langle v(t)+B(z),x(t)-z\rangle,
\]
and this in turn is at most \(\|v(t)+B(z)\|(C+\|z\|)\). The rewrites `inner_neg_right` and `inner_add_left` justify the algebra of the inner product, and `linarith [hzineq']` closes the inequality. This proves the eventual upper bound `hupper`.

At this point the proof has three facts: the gap is eventually nonnegative, it is eventually bounded above by \(\|v(t)+B(z)\|(C+\|z\|)\), and that upper bounding function tends to \(0\). The final command `exact squeeze_zero' hnonneg' hupper hupperlim` applies the squeeze theorem for filters: if \(0\le f(t)\) eventually, if \(f(t)\le g(t)\) eventually, and if \(g(t)\to 0\), then \(f(t)\to 0\). With
\[
f(t)=
(\Phi(z):\mathrm{EReal}).\mathrm{toReal}
-
(\Phi(x(t)):\mathrm{EReal}).\mathrm{toReal}
-
\langle v(t),z-x(t)\rangle
\]
and
\[
g(t)=\|v(t)+B(z)\|(C+\|z\|),
\]
this yields exactly the desired conclusion
\[
f(t)\to 0.
\]

