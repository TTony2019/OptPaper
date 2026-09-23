import Mathlib
import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.Enlargement
import TheoremLib.Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators.items.def_1

/-!
# Demiclosedness of the graph of the ε-enlargement

The original result (Svaiter–Burachik 1999, Proposition 3.4) is stated for a Banach
space `X` with `T : X ⇉ X*` and the ε-enlargement mapping into `X*`:

- (a) If `{x_k} ⊂ X` converges **strongly** to `x₀`,
       `{u_k ∈ T_{ε_k}(x_k)}` converges **weak\*** to `u₀` in `X*`,
       and `{ε_k} ⊂ ℝ_+` converges to `ε`,
       then `u₀ ∈ T_ε(x₀)`.

- (b) If `{x_k} ⊂ X` converges **weakly** to `x₀`,
       `{u_k ∈ T_{ε_k}(x_k)}` converges **strongly** to `u₀` in `X*`,
       and `{ε_k} ⊂ ℝ_+` converges to `ε`,
       then `u₀ ∈ T_ε(x₀)`.

In the Hilbert space setting of Moudafi–Oliny (`H` is a real Hilbert space), the
Riesz representation identifies `H ≅ H*` isometrically, so the ε-enlargement lands
in `H`, and **weak\* convergence in H\* coincides with weak convergence in H**.
The theorem below is the Hilbert-space adaptation used in the paper.
-/

open SetValuedOperator
open scoped InnerProductSpace Topology
open Filter

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Part (a): strong convergence of `x_k` in `H` and weak* convergence of `u_k`
(which in a Hilbert space coincides with weak convergence of the Riesz representations
in `H` via `H ≅ H*`). Together with monotonicity of `T`, this implies
`u₀ ∈ T_ε(x₀)`. -/
theorem demiclosed_strong_x_weakStar_u {T : SetValuedOperator H H}
    (hT_mono : IsMonotone T)
    {x : ℕ → H} {u : ℕ → H} {ε : ℕ → ℝ} {x0 u0 : H} {ε0 : ℝ}
    (hx : Tendsto x atTop (𝓝 x0))
    (hu : Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) atTop (𝓝 (toWeakSpace ℝ H u0)))
    (hε : Tendsto ε atTop (𝓝 ε0))
    (h : ∀ k, u k ∈ enlargement T (ε k) (x k)) :
    u0 ∈ enlargement T ε0 x0 := by
  rw [enlargement, Set.mem_setOf_eq]
  intro y v hv
  -- From `h`, for each k we have `-ε k ≤ ⟪v - u k, y - x k⟫_ℝ` = `⟪x k - y, u k - v⟫_ℝ`
  have h_eps_le : ∀ k, -ε k ≤ ⟪x k - y, u k - v⟫_ℝ := by
    intro k
    have hk := h k
    rw [enlargement, Set.mem_setOf_eq] at hk
    have hk' := hk y v hv
    -- hk' : -ε k ≤ ⟪v - u k, y - x k⟫_ℝ
    -- Rewrite: ⟪v - u k, y - x k⟫_ℝ = ⟪x k - y, u k - v⟫_ℝ
    have h_eq : ⟪v - u k, y - x k⟫_ℝ = ⟪x k - y, u k - v⟫_ℝ := by
      simp [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    simpa [h_eq] using hk'
  -- Boundedness of {x_k} and {u_k} from convergence
  have hx_bdd : Bornology.IsBounded (Set.range x) :=
    Metric.isBounded_range_of_tendsto _ hx
  have hu_bdd : Bornology.IsBounded (Set.range u) :=
    bounded_range_of_tendsto_weakly hu
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨_, hMx⟩
  rcases isBounded_iff_forall_norm_le.mp hu_bdd with ⟨Mu, hMu⟩
  -- Bound for ‖u k - u0‖
  have hMu_bound : ∀ k, ‖u k - u0‖ ≤ Mu + ‖u0‖ := by
    intro k
    calc
      ‖u k - u0‖ ≤ ‖u k‖ + ‖u0‖ := norm_sub_le _ _
      _ ≤ Mu + ‖u0‖ := by
        gcongr
        exact hMu (u k) (Set.mem_range_self k)
  -- Decompose the inner product as in the paper proof
  have h_decomp : ∀ k, ⟪x k - y, u k - v⟫_ℝ =
      ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by
    intro k
    calc
      ⟪x k - y, u k - v⟫_ℝ
          = ⟪x k - y, (u k - u0) + (u0 - v)⟫_ℝ := by simp [sub_add_sub_cancel]
      _ = ⟪x k - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by rw [inner_add_right]
      _ = ⟪(x k - x0) + (x0 - y), u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by
        simp [sub_add_sub_cancel]
      _ = (⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ) + ⟪x k - y, u0 - v⟫_ℝ := by
        rw [inner_add_left]
      _ = ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by ring
  -- Limit of ⟪x k - x0, u k - u0⟫_ℝ → 0: Cauchy-Schwarz + strong convergence of x_k
  have hlim1 : Tendsto (fun k : ℕ => ⟪x k - x0, u k - u0⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have hx_norm_tendsto : Tendsto (fun k : ℕ => ‖x k - x0‖) atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => x k - x0) atTop (𝓝 0) := by
        simpa using hx.sub_const x0
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mp this)
    have hbound : ∀ k, ‖⟪x k - x0, u k - u0⟫_ℝ‖ ≤ ‖x k - x0‖ * (Mu + ‖u0‖) := by
      intro k
      calc
        ‖⟪x k - x0, u k - u0⟫_ℝ‖ = |⟪x k - x0, u k - u0⟫_ℝ| := by rw [Real.norm_eq_abs]
        _ ≤ ‖x k - x0‖ * ‖u k - u0‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x k - x0‖ * (Mu + ‖u0‖) := by gcongr; exact hMu_bound k
    have h_prod_tendsto : Tendsto (fun k : ℕ => ‖x k - x0‖ * (Mu + ‖u0‖)) atTop (𝓝 (0 : ℝ)) := by
      simpa using hx_norm_tendsto.mul_const (Mu + ‖u0‖)
    refine squeeze_zero_norm hbound h_prod_tendsto
  -- Limit of ⟪x0 - y, u k - u0⟫_ℝ → 0: weak convergence of u_k
  have hlim2 : Tendsto (fun k : ℕ => ⟪x0 - y, u k - u0⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have h_inner_temp : Tendsto (fun k : ℕ => ⟪u k, x0 - y⟫_ℝ) atTop (𝓝 ⟪u0, x0 - y⟫_ℝ) := by
      simpa using (weakSpace_continuous_inner_right (x0 - y)).tendsto (toWeakSpace ℝ H u0) |>.comp hu
    have h_inner : Tendsto (fun k : ℕ => ⟪x0 - y, u k⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0⟫_ℝ) := by
      simpa [real_inner_comm] using h_inner_temp
    have h_eq : (fun k : ℕ => ⟪x0 - y, u k - u0⟫_ℝ) =
        (fun k : ℕ => ⟪x0 - y, u k⟫_ℝ - ⟪x0 - y, u0⟫_ℝ) := by
      ext k; simp [inner_sub_right]
    rw [h_eq]
    simpa using h_inner.sub_const ⟪x0 - y, u0⟫_ℝ
  -- Limit of ⟪x k - y, u0 - v⟫_ℝ → ⟪x0 - y, u0 - v⟫_ℝ: strong convergence of x_k
  have hlim3 : Tendsto (fun k : ℕ => ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) :=
    Filter.Tendsto.inner (hx.sub_const y) (tendsto_const_nhds (x := u0 - v))
  -- Combine the three limits
  have hlim_sum : Tendsto (fun k : ℕ => ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ +
      ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 (⟪x0 - y, u0 - v⟫_ℝ)) := by
    simpa [add_assoc] using hlim1.add (hlim2.add hlim3)
  have hlim : Tendsto (fun k : ℕ => ⟪x k - y, u k - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
    simpa [h_decomp] using hlim_sum
  have heps_lim : Tendsto (fun k : ℕ => -ε k) atTop (𝓝 (-ε0)) :=
    hε.neg
  -- Pass the inequality -ε k ≤ ⟪x k - y, u k - v⟫_ℝ through the limit
  have h_ineq : -ε0 ≤ ⟪x0 - y, u0 - v⟫_ℝ := by
    have h_eventually : (fun k : ℕ => -ε k) ≤ᶠ[atTop] (fun k : ℕ => ⟪x k - y, u k - v⟫_ℝ) :=
      Filter.Eventually.of_forall h_eps_le
    exact le_of_tendsto_of_tendsto heps_lim hlim h_eventually
  -- Convert back: ⟪x0 - y, u0 - v⟫_ℝ = ⟪v - u0, y - x0⟫_ℝ
  have h_final_eq : ⟪x0 - y, u0 - v⟫_ℝ = ⟪v - u0, y - x0⟫_ℝ := by
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  simpa [h_final_eq] using h_ineq

/-- Part (b): weak convergence of `x_k` and strong convergence of `u_k`,
together with monotonicity of `T`, imply `u₀ ∈ T_ε(x₀)`. -/
theorem demiclosed_weak_x_strong_u {T : SetValuedOperator H H}
    (hT_mono : IsMonotone T)
    {x : ℕ → H} {u : ℕ → H} {ε : ℕ → ℝ} {x0 u0 : H} {ε0 : ℝ}
    (hx : Tendsto (fun k ↦ toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H x0)))
    (hu : Tendsto u atTop (𝓝 u0))
    (hε : Tendsto ε atTop (𝓝 ε0))
    (h : ∀ k, u k ∈ enlargement T (ε k) (x k)) :
    u0 ∈ enlargement T ε0 x0 := by
  rw [enlargement, Set.mem_setOf_eq]
  intro y v hv
  -- From `h`, for each k we have `-ε k ≤ ⟪v - u k, y - x k⟫_ℝ` = `⟪x k - y, u k - v⟫_ℝ`
  have h_eps_le : ∀ k, -ε k ≤ ⟪x k - y, u k - v⟫_ℝ := by
    intro k
    have hk := h k
    rw [enlargement, Set.mem_setOf_eq] at hk
    have hk' := hk y v hv
    -- hk' : -ε k ≤ ⟪v - u k, y - x k⟫_ℝ
    -- Rewrite: ⟪v - u k, y - x k⟫_ℝ = ⟪x k - y, u k - v⟫_ℝ
    have h_eq : ⟪v - u k, y - x k⟫_ℝ = ⟪x k - y, u k - v⟫_ℝ := by
      simp [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    simpa [h_eq] using hk'
  -- Boundedness of {x_k} and {u_k} from convergence
  have hx_bdd : Bornology.IsBounded (Set.range x) :=
    bounded_range_of_tendsto_weakly hx
  have hu_bdd : Bornology.IsBounded (Set.range u) :=
    Metric.isBounded_range_of_tendsto _ hu
  rcases isBounded_iff_forall_norm_le.mp hx_bdd with ⟨Mx, hMx⟩
  rcases isBounded_iff_forall_norm_le.mp hu_bdd with ⟨_, hMu⟩
  -- Bound for ‖x k - x0‖
  have hMx_bound : ∀ k, ‖x k - x0‖ ≤ Mx + ‖x0‖ := by
    intro k
    calc
      ‖x k - x0‖ ≤ ‖x k‖ + ‖x0‖ := norm_sub_le _ _
      _ ≤ Mx + ‖x0‖ := by
        gcongr
        exact hMx (x k) (Set.mem_range_self k)
  -- Decompose the inner product as in the paper proof
  have h_decomp : ∀ k, ⟪x k - y, u k - v⟫_ℝ =
      ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by
    intro k
    calc
      ⟪x k - y, u k - v⟫_ℝ
          = ⟪x k - y, (u k - u0) + (u0 - v)⟫_ℝ := by simp [sub_add_sub_cancel]
      _ = ⟪x k - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by rw [inner_add_right]
      _ = ⟪(x k - x0) + (x0 - y), u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by
        simp [sub_add_sub_cancel]
      _ = (⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ) + ⟪x k - y, u0 - v⟫_ℝ := by
        rw [inner_add_left]
      _ = ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ + ⟪x k - y, u0 - v⟫_ℝ := by ring
  -- Limit of ⟪x k - x0, u k - u0⟫_ℝ → 0: Cauchy-Schwarz + strong convergence of u_k
  have hlim1 : Tendsto (fun k : ℕ => ⟪x k - x0, u k - u0⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have hu_norm_tendsto : Tendsto (fun k : ℕ => ‖u k - u0‖) atTop (𝓝 0) := by
      have : Tendsto (fun k : ℕ => u k - u0) atTop (𝓝 0) := by
        simpa using hu.sub_const u0
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mp this)
    have hbound : ∀ k, ‖⟪x k - x0, u k - u0⟫_ℝ‖ ≤ (Mx + ‖x0‖) * ‖u k - u0‖ := by
      intro k
      calc
        ‖⟪x k - x0, u k - u0⟫_ℝ‖ = |⟪x k - x0, u k - u0⟫_ℝ| := by rw [Real.norm_eq_abs]
        _ ≤ ‖x k - x0‖ * ‖u k - u0‖ := abs_real_inner_le_norm _ _
        _ ≤ (Mx + ‖x0‖) * ‖u k - u0‖ := by gcongr; exact hMx_bound k
    have h_prod_tendsto : Tendsto (fun k : ℕ => (Mx + ‖x0‖) * ‖u k - u0‖) atTop (𝓝 (0 : ℝ)) := by
      simpa using hu_norm_tendsto.const_mul (Mx + ‖x0‖)
    refine squeeze_zero_norm hbound h_prod_tendsto
  -- Limit of ⟪x0 - y, u k - u0⟫_ℝ → 0: strong convergence of u_k
  have hlim2 : Tendsto (fun k : ℕ => ⟪x0 - y, u k - u0⟫_ℝ) atTop (𝓝 (0 : ℝ)) := by
    have h_inner : Tendsto (fun k : ℕ => ⟪x0 - y, u k⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0⟫_ℝ) :=
      Filter.Tendsto.inner (tendsto_const_nhds (x := x0 - y)) hu
    have h_eq : (fun k : ℕ => ⟪x0 - y, u k - u0⟫_ℝ) =
        (fun k : ℕ => ⟪x0 - y, u k⟫_ℝ - ⟪x0 - y, u0⟫_ℝ) := by
      ext k; simp [inner_sub_right]
    rw [h_eq]
    simpa using h_inner.sub_const ⟪x0 - y, u0⟫_ℝ
  -- Limit of ⟪x k - y, u0 - v⟫_ℝ → ⟪x0 - y, u0 - v⟫_ℝ: weak convergence of x_k
  have hlim3 : Tendsto (fun k : ℕ => ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
    have h_inner_temp : Tendsto (fun k : ℕ => ⟪x k, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0, u0 - v⟫_ℝ) := by
      simpa using (weakSpace_continuous_inner_right (u0 - v)).tendsto
        (toWeakSpace ℝ H x0) |>.comp hx
    have h_inner : Tendsto (fun k : ℕ => ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
      simpa [inner_sub_left] using h_inner_temp.sub_const ⟪y, u0 - v⟫_ℝ
    exact h_inner
  -- Combine the three limits
  have hlim_sum : Tendsto (fun k : ℕ => ⟪x k - x0, u k - u0⟫_ℝ + ⟪x0 - y, u k - u0⟫_ℝ +
      ⟪x k - y, u0 - v⟫_ℝ) atTop (𝓝 (⟪x0 - y, u0 - v⟫_ℝ)) := by
    simpa [add_assoc] using hlim1.add (hlim2.add hlim3)
  have hlim : Tendsto (fun k : ℕ => ⟪x k - y, u k - v⟫_ℝ) atTop (𝓝 ⟪x0 - y, u0 - v⟫_ℝ) := by
    simpa [h_decomp] using hlim_sum
  have heps_lim : Tendsto (fun k : ℕ => -ε k) atTop (𝓝 (-ε0)) :=
    hε.neg
  -- Pass the inequality -ε k ≤ ⟪x k - y, u k - v⟫_ℝ through the limit
  have h_ineq : -ε0 ≤ ⟪x0 - y, u0 - v⟫_ℝ := by
    have h_eventually : (fun k : ℕ => -ε k) ≤ᶠ[atTop] (fun k : ℕ => ⟪x k - y, u k - v⟫_ℝ) :=
      Filter.Eventually.of_forall h_eps_le
    exact le_of_tendsto_of_tendsto heps_lim hlim h_eventually
  -- Convert back: ⟪x0 - y, u0 - v⟫_ℝ = ⟪v - u0, y - x0⟫_ℝ
  have h_final_eq : ⟪x0 - y, u0 - v⟫_ℝ = ⟪v - u0, y - x0⟫_ℝ := by
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  simpa [h_final_eq] using h_ineq
