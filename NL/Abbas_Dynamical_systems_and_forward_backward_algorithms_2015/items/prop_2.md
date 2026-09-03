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
The theorem states a limit result under assumptions involving a convex-like function, a forward-backward dynamical system, and subdifferentials. It asserts that the “subgradient gap” at a point `z` in a set `S` tends to `0` as time tends to `+∞`.

Variables and parameters:
- `H` is a real inner product space with a norm compatible with the inner product, and `H` is complete. This is encoded by `[NormedAddCommGroup H]`, `[InnerProductSpace ℝ H]`, and `[CompleteSpace H]`.
- `S : Set H` is a subset of `H`.
- `Phi : H → Set.Ioi (⊥ : EReal)`: for each point of `H`, `Phi` returns a set of extended-real numbers strictly greater than bottom. The bottom `⊥ : EReal` is negative infinity, so this means `Phi(x)` is a subset of extended reals excluding `-∞`.
- `hPhi : Phi ∈ ERealFunction.gammaZero H`: the set-valued map `Phi` belongs to the class `gammaZero`, meaning it is a “gamma-zero” generalized convex function, i.e. it is the closure of a proper convex lower semicontinuous function, equivalently it has appropriate convex-subdifferential behavior. Its exact mathematical content is imported from `ERealFunction`, but the proof only uses subgradient inequalities available from this assumption.
- `B : H → H` is an operator.
- `x v : ℝ → H` are time-dependent curves in `H`.
- `z : H` is a point in `S`.
- `lam mu beta : ℝ` are real parameters.
- `hS : S.Nonempty` says `S` is nonempty.
- `hz : z ∈ S` says the fixed point `z` belongs to `S`.
- `hlam : 0 < lam`, `hmu : 0 < mu`, `hmu_lam : mu * lam = 1`, `hbeta : 0 < beta`: `lam`, `mu`, and `beta` are positive, and `mu * lam = 1`, so `mu = 1 / lam`.
- `hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)`: the operator `B`, restricted to the full space, is `beta`-cocoercive on the entire space. This means `B` is monotone and Lipschitz-like with cocoercivity parameter `beta`.
- `hx_ac` and `hv_ac`: for every positive endpoint `b`, the curves `x` and `v` are absolutely continuous on the interval `[0,b]`.
- `hx_deriv` and `hv_deriv`: for every `T > 0`, almost everywhere on `[0,T]` with respect to the restricted Lebesgue volume measure, `x` and `v` are differentiable with derivatives `deriv x` and `deriv v`.
- `hvL2`: for every `T > 0`, `v` belongs to `L^2` on the restricted interval `[0,T]`.
- `hdxL2`: for every `T > 0`, the derivative `deriv x` belongs to `L^2` on the restricted interval `[0,T]`.
- `hsubgradient`: for every time `t ≥ 0`, `v t` belongs to the subdifferential of `Phi` at `x t`, written `ERealFunction.subdifferential Phi (x t)`.
- `horbit`: almost everywhere on `[0,∞)`, the curve satisfies the dynamical system equation
  `lam • deriv x t + deriv v t + v t + B (x t) = 0`.
- `hsolution`: for every `w`, `w ∈ S` if and only if `-B w` belongs to the subdifferential of `Phi` at `w`.
- `hdom`: for every `t ≥ 0`, `x t` lies in the effective domain of `Phi`.
- `hdomS`: for every `w ∈ S`, `w` lies in the effective domain of `Phi`.

Conclusion:
The function
\[
t \mapsto (\Phi z)_{\mathrm{toReal}} - (\Phi(x t))_{\mathrm{toReal}}
    - \langle v t,\, z - x t\rangle
\]
tends to `0` as `t → +∞`, in the sense of `Tendsto ... atTop (nhds 0)`.
Here `(Phi z : EReal).toReal` denotes the real part of the extended-real value of `Phi z`; since `Phi` maps into sets of extended reals above `⊥`, this notation is meaningful under the strong subgradient assumptions used. The final expression is called the subgradient gap, involving the value difference and an inner-product correction with `v t`.

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
The proof has several stages. It first establishes nonnegativity of the gap, then uses previously proved results about Lyapunov functions and convergence to obtain bounds, and finally applies a squeezing theorem to force the gap to zero.

1. **Nonnegativity of the gap.**  
   The proof starts with `have hnonneg : ∀ t, 0 ≤ t → 0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal - inner ℝ (v t) (z - x t)`.  
   To prove it, for arbitrary `t ≥ 0`, it invokes
   `ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi (hsubgradient t ht) (hdomS z hz)`.  
   This imported lemma, valid because `Phi ∈ gammaZero`, says that for points in the effective domain and subgradients, a subgradient inequality holds when converted to real extended values. The conclusion produced is an inequality relating `(Phi z).toReal`, `(Phi (x t)).toReal`, and `inner (v t) (z - x t)`. The command `linarith` closes the goal because the inequality is exactly the negation rearranged to show the desired expression is nonnegative.

2. **Combining subgradient and ODE information.**  
   The proof creates `horbit_pair`, which is the almost-everywhere conjunction of the subgradient membership `v t ∈ subdifferential Phi (x t)` and the differential equation. It uses `filter_upwards [ae_restrict_mem measurableSet_Ici, horbit] with t ht hEq`. This combines two almost-everywhere facts on the upper half-line: first, that for almost every `t` in `Ici 0` we have `t ≥ 0`, and second, the ODE `horbit`. The `filter_upwards ... with t ht hEq` tactic unfolds the meaning of almost-everywhere membership and produces the conjunction
   \[
   v(t) \in \partial \Phi(x(t)) \quad\land\quad
   \lambda \dot x(t)+\dot v(t)+v(t)+B(x(t))=0.
   \]

3. **Use of previous Lyapunov results.**  
   The proof applies `proposition_2_12` to obtain a Lyapunov-type result:
   `hLyapunov := proposition_2_12 S Phi hPhi B x v z lam mu beta hS hz hlam hmu hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient hvL2 hdxL2 horbit_pair ...`.  
   The relevant part extracted is `hLyapunov.2.2.2.1`, and from it one obtains a pair `⟨C, hC⟩`: there exists a constant `C` such that for every `t ≥ 0`, `‖x t‖ ≤ C`. The proof uses `obtain ⟨C, hC⟩ := hLyapunov.2.2.2.1`.

4. **Application of a convergence theorem.**  
   The proof applies `theorem_2_8_convergence` to the original data:
   `hconvergence := theorem_2_8_convergence S Phi hPhi B x v lam beta hS hlam hbeta hB horbit hx_ac hv_ac hx_deriv hv_deriv hvL2 hdxL2 hsubgradient hsolution`.  
   This gives asymptotic convergence information. In particular, the component `hconvergence.2.2.1 z hz` states that, as `t → +∞`, the quantity `v t + B z` tends to `0`.  
   The next block proves `hvlim : Tendsto (fun t => v t + B z) atTop (nhds 0)`. It starts with `have hconst : Tendsto (fun _ : ℝ => B z) atTop (nhds (B z)) := tendsto_const_nhds`, which is the constant-net limit. It then adds this constant limit to the previously obtained limit:
   `have h := (hconvergence.2.2.1 z hz).add hconst`. This is justified because if two functions tend to limits, their pointwise sum tends to the sum of the limits. Finally `simpa using h` simplifies the expression to get exactly `Tendsto (v t + B z) atTop (nhds 0)`.

5. **Limit of the upper-bound factor.**  
   The proof next proves
   `hupperlim : Tendsto (fun t => ‖v t + B z‖ * (C + ‖z‖)) atTop (nhds 0)`.  
   Since `C + ‖z‖` is a constant, the proof forms its constant limit and then uses `.norm.mul hconst`:
   `simpa using hvlim.norm.mul hconst`.  
   The tactic `.norm` takes the norm of the limit, and `.mul` multiplies by a constant limit. Therefore the product tends to `0 * (C + ‖z‖) = 0`.

6. **The gap is eventually nonnegative.**  
   The proof forms `hnonneg'` as an `atTop` eventually fact:
   `filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht`.  
   This means for sufficiently large `t`, one has `t ≥ 0`; then it invokes the earlier `hnonneg t ht`. Thus, eventually, the gap is nonnegative.

7. **An eventual upper bound for the gap.**  
   The heart of the proof is the step establishing
   `hupper : ∀ᶠ t in atTop, (Phi z).toReal - (Phi (x t)).toReal - inner (v t) (z - x t) ≤ ‖v t + B z‖ * (C + ‖z‖)`.  
   Again the proof filters over `eventually_ge_atTop (0 : ℝ)` and fix `t ≥ 0`.  
   It first uses the subgradient inequality at the solution point `z`. Since `hz : z ∈ S`, the equivalence `hsolution` gives `-B z ∈ subdifferential Phi z`, and because `x t` is in the effective domain of `Phi`, applying
   `ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi ((hsolution z).1 hz) (hdom t ht)` yields
   \[
   (\Phi z)_{\rm real} - (\Phi(x t))_{\rm real}
     \le \langle B z,\, x t - z\rangle.
   \]
   In Lean, the inequality statement is stored with a sign on the inner product, so the proof rewrites with `rw [inner_neg_left] at hzineq` and then uses `linarith` to turn it into this form. The lemma `inner_neg_left` says \(\langle -a, b\rangle = -\langle a, b\rangle\).

   Next, the bound on the norm is obtained. The triangle inequality gives `‖x t - z‖ ≤ ‖x t‖ + ‖z‖`, and the bound `‖x t‖ ≤ C` from `hC t ht` gives
   \[
   \|x t - z\| \le C + \|z\|.
   \]
   This is proved by `calc`:
   `‖x t - z‖ ≤ ‖x t‖ + ‖z‖ := norm_sub_le _ _`, then `_ ≤ C + ‖z‖ := add_le_add (hC t ht) le_rfl`.

   The proof then bounds the inner product by a norm product. It shows
   \[
   \langle v t + B z,\; x t - z\rangle \le \|v t + B z\| \cdot \|x t - z\|.
   \]
   The Lean proof uses `(le_abs_self _).trans (abs_real_inner_le_norm _ _)`; this says that an inner product is at most its absolute value, and the absolute value of a real inner product is at most the product of norms by Cauchy–Schwarz.

   Then the norm product is bounded by the desired constant term:
   \[
   \|v t + B z\| \cdot \|x t - z\| \le \|v t + B z\| \cdot (C+\|z\|),
   \]
   using `hxz` and the nonnegativity of the norm.

   The final key algebraic step is to show that the gap is at most the inner product \(\langle v t+Bz,\; x t-z\rangle\). The proof rewrites the difference `z - x t` as `-(x t - z)` via `abel`, then applies `inner_neg_right` and `inner_add_left` to expand:
   \[
   -\langle v t,\, z-x t\rangle
   =\langle v t,\, x t-z\rangle
   \quad\text{and}\quad
   \langle v t+Bz,\,x t-z\rangle
   =\langle v t,x t-z\rangle+\langle Bz,x t-z\rangle.
   \]
   Using the earlier inequality for the value difference in terms of \(\langle Bz, x t-z\rangle\), `linarith` closes the gap:
   \[
   (\Phi z)_{\rm real} - (\Phi(x t))_{\rm real} - \langle v t,z-x t\rangle
   \le \langle v t+Bz,\,x t-z\rangle.
   \]
   Combining the three inequalities with `.trans` gives the eventual upper bound:
   \[
   \text{gap}(t) \le \|v t+Bz\|(C+\|z\|).
   \]

8. **Squeeze to zero.**  
   Finally, the proof calls
   `exact squeeze_zero' hnonneg' hupper hupperlim`.  
   The theorem `squeeze_zero'` states that if a function is eventually nonnegative, bounded above by another function, and the upper bounding function tends to `0`, then the original function tends to `0`. Here `hupperlim` provides the limit of the upper bound, `hnonneg'` provides the lower bound by zero, and `hupper` provides the eventual pointwise upper comparison. Therefore the gap, which is eventually between `0` and the tending-to-zero product, converges to `0` as `t → +∞`.

