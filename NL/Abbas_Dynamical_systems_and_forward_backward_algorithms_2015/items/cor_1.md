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
The theorem is set in a real Hilbert space, expressed through Lean's typeclass assumptions. Let me unpack the statement.

Let `H` be a type equipped with a normed additive commutative group structure, an inner product space over `ℝ`, and completeness, so `H` is a real Hilbert space. The expression `⊥ : EReal` is negative infinity in the extended real numbers, and `Set.Ioi ⊥` means the interval of extended reals strictly greater than `-∞`, i.e. finite real numbers or `+∞`. The variable `Phi : H → Set.Ioi (⊥ : EReal)` is therefore a function from `H` to extended-real-valued quantities that are never `-∞`, so `Phi` is a proper extended-real-valued function on `H`. The hypothesis `hPhi : Phi ∈ ERealFunction.gammaZero H` asserts that `Phi` belongs to the class of functions with zero "gamma" parameter, a kind of convexity or weak convexity condition used in the source framework.

The other variables are: `B : H → H`, a vector field on `H`; `S : Set H`, a subset of `H`; `x v : ℝ → H`, two time-dependent paths in `H`; `lam`, `mu`, `beta` real numbers; and `m` appears later existentially. The hypothesis `hS : S.Nonempty` says `S` is nonempty. The hypotheses `hlam : 0 < lam`, `hmu : 0 < mu`, and `hmu_lam : mu * lam = 1` mean `lam` and `mu` are positive reciprocal parameters. `hbeta : 0 < beta` says `beta` is positive. The hypothesis `hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w)` states that `B` is `beta`-cocoercive on the whole space, expressed for the subtype of elements of the universe; this is an inequality involving `⟨B w1, B w2⟩` and `⟨w1 - w2, B w1 - B w2⟩`.

The path regularity hypotheses are:
- `hx_ac : ∀ b, 0 < b → AbsolutelyContinuousOnInterval x 0 b`: for every positive time `b`, `x` is absolutely continuous on `[0,b]`.
- `hv_ac` similarly for `v`.
- `hx_deriv`: for every `T > 0`, almost everywhere on `[0,T]` with respect to restricted Lebesgue volume, `HasDerivAt x (deriv x t) t`, i.e. the derivative of `x` equals the weak/derived derivative. Same for `hv_deriv` with `v`.

The subdifferential and membership hypotheses are:
- `hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t)`: for all nonnegative times, `v t` is a subgradient of `Phi` at `x t`.
- `hvL2` and `hdxL2`: for every positive `b`, `v` and `deriv x` are square-integrable on `[0,b]`.
- `hdom : (∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi) ∧ ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi`: the path `x` and every point of `S` lie in the effective domain of `Phi`.
- `hweak : ∃ xinf ∈ S, Tendsto (fun t ↦ toWeakSpace ℝ H (x t)) atTop (nhds (toWeakSpace ℝ H xinf))`: there is a point `xinf` in `S` such that `x t` converges weakly to `xinf` as `t → ∞`.
- `hsolution : ∀ z, z ∈ S → -B z ∈ ERealFunction.subdifferential Phi z`: for every `z` in `S`, the vector `-B z` is a subgradient of `Phi` at `z`.
- `horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0), v t ∈ ERealFunction.subdifferential Phi (x t) ∧ lam • deriv x t + deriv v t + v t + B (x t) = 0`: almost everywhere on `[0,∞)`, the subgradient inclusion holds and the damped forward-backward differential equation `λ ẋ(t) + \dot v(t) + v(t) + B(x(t)) = 0` holds.
- `hstrong_support : ∃ m : ℝ, 0 < m ∧ ∀ {a u y : H}, u ∈ ERealFunction.subdifferential Phi a → y ∈ ERealFunction.effectiveDomain Phi → m / 2 * ‖y - a‖ ^ 2 ≤ (Phi y : EReal).toReal - (Phi a : EReal).toReal - inner ℝ u (y - a)`: the function `Phi` has a strong convexity-like quadratic lower bound with parameter `m` at every subgradient point.

The conclusion is: `∃ z, S = {z} ∧ Tendsto x atTop (nhds z)`. That is, there exists a point `z` such that `S` is the singleton `{z}`, and the trajectory `x t` converges strongly to `z` as `t` tends to infinity.

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
The proof has two major parts. First, it proves that `S` has exactly one point. Second, it proves that the whole trajectory `x` converges to that unique point.

The proof starts with `rcases hS with ⟨z, hz⟩`, choosing a point `z ∈ S` from nonemptiness. Then `rcases hstrong_support with ⟨m, hm, hsupp⟩` extracts the strong-support parameter `m > 0` and the quadratic inequality `hsupp`.

To show `S = {z}`, Lean uses `refine Set.eq_singleton_iff_unique_mem.mpr ⟨hz, ?_⟩`. This reduces the task to proving that every `y ∈ S` equals `z`. Take an arbitrary `y ∈ S`. Using `hsupp` twice with two subgradient inequalities:
- For `a = z`, `u = -B z`, and `y = y`, since `z ∈ S` and `hsolution z hz` gives `-B z ∈ ∂Phi z`, and `hdom.2 y hy` gives `y` in the domain, one obtains
  \[
  \frac m2 \|y-z\|^2 \le \Phi(y)-\Phi(z) - \langle -Bz, y-z\rangle.
  \]
  Using `simpa [inner_neg_left, real_inner_comm]`, this is rewritten as
  \[
  \frac m2 \|y-z\|^2 \le \Phi(y)-\Phi(z) + \langle y-z, Bz\rangle.
  \]
- For `a = y`, `u = -B y`, and `y = z`, similarly:
  \[
  \frac m2 \|z-y\|^2 \le \Phi(z)-\Phi(y) - \langle -By, z-y\rangle.
  \]
  After rewriting inner products using `inner_neg_left`, `inner_neg_right`, commutation, and `norm_sub_rev`, Lean obtains
  \[
  \frac m2 \|y-z\|^2 \le \Phi(z)-\Phi(y) - \langle y-z, By\rangle.
  \]

Next, `hineq := hB.ineq ⟨y, Set.mem_univ y⟩ ⟨z, Set.mem_univ z⟩` is the cocoercivity inequality applied to the two points `y` and `z`. Cocoercivity gives an inequality
\[
\beta \langle B y - B z, y - z\rangle \le \|B y - B z\|^2
\]
or in the form used here, combined with `hbeta.le` and `sq_nonneg`, Lean shows
\[
0 \le \langle y - z, B y - B z\rangle.
\]
This is `hinner`.

The proof then forms `hdist : m * ‖y - z‖^2 ≤ 0`. Inside, it derives an intermediate sum inequality `hsum`:
\[
m \|y-z\|^2 \le -\langle y-z, B y - B z\rangle.
\]
This is obtained by adding the two quadratic lower bounds. Writing
\[
\inner{ y-z}{ B y - B z} = \inner{ y-z}{B y} - \inner{ y-z}{B z}
\]
and using `nlinarith [h1', h2', hinner_eq]`, Lean combines the two inequalities to conclude `hsum`. Then
\[
\inner{ y-z}{ B y - B z} \ge 0
\]
implies its negation is nonpositive, so `hsum` gives `m\|y-z\|^2 ≤ 0`. Since `m > 0`, the only nonnegative number satisfying this is `0`; using `sq_nonneg`, `nlinarith` proves `hzero : ‖y - z‖^2 = 0`. Then `norm_eq_zero` and `sub_eq_zero` turn this into `y = z`. Thus `S = {z}`.

Now the proof turns to convergence. It calls `proposition_2_16 S Phi hPhi B x v z lam mu beta ⟨z, hz⟩ hz ...`. This is an imported proposition giving properties of the forward-backward dynamics. In particular it provides `hp.2.1`, named `hF_lim`, a limit involving the quantity
\[
\Phi(x(t)) - \Phi(z) + \langle B z, x(t)-z\rangle
\]
tending to zero as `t → ∞`. The proof defines `gamma := m / 2`, so `gamma > 0` by `linarith`.

The next goal is to prove `hnorm_lim : Tendsto (fun t => ‖x t - z‖) atTop (nhds 0)`. Since the norm is nonnegative, it suffices to compare it to a quantity that tends to zero. Lean introduces the auxiliary function
\[
g(t) = \frac{1}{\gamma}\Big(\Phi(x t)-\Phi(z)+\langle B z, x t - z\rangle\Big).
\]
Using `squeeze_zero'`, it shows that `‖x t - z‖^2` is squeezed between `0` and `g(t)`. The lower bound is simply `sq_nonneg`. The upper estimate comes from `hsupp` applied with `a = z`, `u = -B z`, `y = x t`. Since `z ∈ S`, `hsolution z hz` gives `-B z ∈ ∂Phi(z)`, and `hdom.1 t ht` gives `x t` in the domain. This yields
\[
\frac m 2 \|x t - z\|^2 \le \Phi(x t)-\Phi(z)+\langle B z, x t - z\rangle.
\]
Rewriting with `gamma` and `inner_neg_left`, this is exactly
\[
\gamma \|x t - z\|^2 \le \Phi(x t)-\Phi(z)+\langle B z, x t - z\rangle.
\]
Multiplying by `γ^{-1} ≥ 0` gives
\[
\|x t - z\|^2 \le γ^{-1}\big(\Phi(x t)-\Phi(z)+\langle B z, x t - z\rangle\big).
\]
Lean handles the algebraic step with `calc`, `rw`, `inv_mul_cancel₀`, and `mul_le_mul_of_nonneg_left`. The nonnegativity of the right side is shown from the same inequality and `nlinarith`, since `γ > 0`.

The right-hand quantity `g(t)` tends to zero because `hF_lim.const_mul γ⁻¹` handles multiplication by the constant `γ⁻¹`. Thus by `squeeze_zero'`, `‖x t - z‖^2 → 0`. Then continuous square root composition gives `‖x t - z‖ → 0`: `simpa ... using (Real.continuous_sqrt.tendsto 0).comp hsquare`.

Finally, from norm convergence to zero, `tendsto_zero_iff_norm_tendsto_zero` gives `x t - z → 0`. The equivalence `tendsto_sub_nhds_zero_iff.mp` turns convergence of differences to zero into `Tendsto x atTop (nhds z)`. The conclusion packages the previously proved singleton identity `S = {z}`, the point `z`, and strong convergence: `exact ⟨z, hS_singleton, tendsto_sub_nhds_zero_iff.mp hsub_lim⟩`. Thus the theorem is proved: `S` is a singleton and the whole trajectory converges strongly to its unique element.

