import Mathlib
import Foundation.Hilbert.WeakConvergence
import Foundation.FixedPoint.Algorithms
import TheoremLib.Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007.items.prop_4

/-!
# Theorem 4.1: Weak Convergence of (CA²) in the Quadratic Case
-/

open Set Filter
open scoped Topology InnerProductSpace InnerProductGeometry BigOperators

set_option maxHeartbeats 0

noncomputable def L_beta_mu {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : H → ℝ) (β μ : ℝ) (ξ η : H) : ℝ :=
  μ * f ξ + β * g η + (β * μ / 2) * ‖ξ - η‖ ^ 2

private lemma subgrad_of_min_quadratic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f' : H → ℝ} (hf'_conv : ConvexOn ℝ (Set.univ : Set H) f')
    {p u v : H} {a b : ℝ}
    (hmin : ∀ ξ : H, f' p + (a / 2) * ‖u - p‖ ^ 2 + (b / 2) * ‖p - v‖ ^ 2 ≤
                     f' ξ + (a / 2) * ‖u - ξ‖ ^ 2 + (b / 2) * ‖ξ - v‖ ^ 2)
    (z : H) : f' z ≥ f' p + inner ℝ (a • (u - p) + b • (v - p)) (z - p) := by
  by_cases hz : z = p
  · subst z; simp
  · have hznorm_sq_pos : ‖z - p‖ ^ 2 > 0 := by
      have hznz : ‖z - p‖ ≠ 0 := mt norm_eq_zero.mp (sub_ne_zero.mpr hz)
      positivity
    set σ := a + b
    by_cases hσpos : σ > 0
    · apply le_of_forall_pos_le_add; intro ε hεpos
      have hden_pos : σ * ‖z - p‖ ^ 2 > 0 := by nlinarith
      set t : ℝ := min (1/2) (2 * ε / (σ * ‖z - p‖ ^ 2))
      have htpos : 0 < t := by
        refine lt_min_iff.mpr ⟨by norm_num, div_pos (by linarith) hden_pos⟩
      have htle : t ≤ 1/2 := min_le_left _ _
      have ht_nonneg : 0 ≤ t := by linarith
      have h_one_minus_t_nonneg : 0 ≤ 1 - t := by linarith
      set zt := p + t • (z - p)
      have hzt_conv : zt = (1 - t) • p + t • z := by
        dsimp [zt]
        calc
          p + t • (z - p) = p + (t • z - t • p) := by rw [smul_sub]
          _ = (p - t • p) + t • z := by abel
          _ = ((1 : ℝ) • p - t • p) + t • z := by simp
          _ = (1 - t) • p + t • z := by rw [sub_smul]
      have h_conv : f' zt ≤ (1 - t) * f' p + t * f' z := by
        have := hf'_conv.2 (mem_univ p) (mem_univ z) h_one_minus_t_nonneg ht_nonneg (by ring)
        simpa [zt, hzt_conv, smul_eq_mul] using this
      have h_opt : f' p + (a / 2) * ‖u - p‖ ^ 2 + (b / 2) * ‖p - v‖ ^ 2 ≤
                  f' zt + (a / 2) * ‖u - zt‖ ^ 2 + (b / 2) * ‖zt - v‖ ^ 2 := hmin zt
      have h_u_zt : ‖u - zt‖ ^ 2 = ‖u - p‖ ^ 2 - 2 * t * inner ℝ (u - p) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]
        have : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by abel
        rw [this, norm_sub_sq_real]; simp [inner_smul_right, norm_smul, abs_of_pos htpos]; ring
      have h_zt_v : ‖zt - v‖ ^ 2 = ‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]
        have : (p + t • (z - p)) - v = (p - v) + t • (z - p) := by abel
        rw [this, norm_add_sq_real]; simp [inner_smul_right, norm_smul, abs_of_pos htpos]; ring
      have h_quad_diff : (a / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (b / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) =
          t * inner ℝ (a • (u - p) + b • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
        rw [h_u_zt, h_zt_v]
        have hexpand : inner ℝ (a • (u - p) + b • (v - p)) (z - p) =
            a * inner ℝ (u - p) (z - p) + b * inner ℝ (v - p) (z - p) := by
          simp [inner_add_left, inner_smul_left]
        rw [hexpand]
        have hsign : inner ℝ (v - p) (z - p) = -inner ℝ (p - v) (z - p) := by
          have h_eq : v - p = -(p - v) := by abel
          rw [h_eq, inner_neg_left]
        rw [hsign]
        dsimp [σ]
        ring
      have h_rearr : f' zt - f' p ≥ (a / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (b / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) := by linarith
      have h_conv_rearr : f' zt - f' p ≤ t * (f' z - f' p) := by linarith
      have h_combined : t * (f' z - f' p) ≥ t * inner ℝ (a • (u - p) + b • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by linarith
      have h_divided : f' z - f' p ≥ inner ℝ (a • (u - p) + b • (v - p)) (z - p) - (σ * t / 2) * ‖z - p‖ ^ 2 := by
        have htemp : t * (f' z - f' p) ≥ t * (inner ℝ (a • (u - p) + b • (v - p)) (z - p) - (σ * t / 2) * ‖z - p‖ ^ 2) := by nlinarith
        exact (le_of_mul_le_mul_left htemp htpos)
      have htb : (σ * t / 2) * ‖z - p‖ ^ 2 ≤ ε := by
        have htle' : t ≤ 2 * ε / (σ * ‖z - p‖ ^ 2) := min_le_right _ _
        have h_nonneg : 0 ≤ (σ / 2) * ‖z - p‖ ^ 2 := by positivity
        calc
          (σ * t / 2) * ‖z - p‖ ^ 2 = t * ((σ / 2) * ‖z - p‖ ^ 2) := by ring
          _ ≤ (2 * ε / (σ * ‖z - p‖ ^ 2)) * ((σ / 2) * ‖z - p‖ ^ 2) := mul_le_mul_of_nonneg_right htle' h_nonneg
          _ = ε := by
            calc
              (2 * ε / (σ * ‖z - p‖ ^ 2)) * ((σ / 2) * ‖z - p‖ ^ 2) =
                  (2 * ε) * ((σ / 2) * ‖z - p‖ ^ 2) / (σ * ‖z - p‖ ^ 2) := by ring
              _ = ε * (σ * ‖z - p‖ ^ 2) / (σ * ‖z - p‖ ^ 2) := by ring
              _ = ε := by
                have hpos' : σ * ‖z - p‖ ^ 2 ≠ 0 := by linarith
                rw [div_eq_iff hpos']
      have h_final : f' z ≥ f' p + inner ℝ (a • (u - p) + b • (v - p)) (z - p) - ε := by
        linarith
      linarith
    · have hσ_nonpos : σ ≤ 0 := by linarith
      set t : ℝ := 1/2
      have htpos : 0 < t := by norm_num
      have h_one_minus_t_nonneg' : 0 ≤ 1 - t := by dsimp [t]; norm_num
      set zt := p + t • (z - p)
      have hzt_conv : zt = (1 - t) • p + t • z := by
        dsimp [zt]
        calc
          p + t • (z - p) = p + (t • z - t • p) := by rw [smul_sub]
          _ = (p - t • p) + t • z := by abel
          _ = ((1 : ℝ) • p - t • p) + t • z := by simp
          _ = (1 - t) • p + t • z := by rw [sub_smul]
      have h_conv : f' zt ≤ (1 - t) * f' p + t * f' z := by
        have := hf'_conv.2 (mem_univ p) (mem_univ z) h_one_minus_t_nonneg' (by linarith) (by ring)
        simpa [zt, hzt_conv, t, smul_eq_mul] using this
      have h_opt : f' p + (a / 2) * ‖u - p‖ ^ 2 + (b / 2) * ‖p - v‖ ^ 2 ≤
                  f' zt + (a / 2) * ‖u - zt‖ ^ 2 + (b / 2) * ‖zt - v‖ ^ 2 := hmin zt
      have h_u_zt : ‖u - zt‖ ^ 2 = ‖u - p‖ ^ 2 - 2 * t * inner ℝ (u - p) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]; have : u - (p + t • (z - p)) = (u - p) - t • (z - p) := by abel
        rw [this, norm_sub_sq_real]; simp [inner_smul_right, norm_smul, abs_of_pos htpos]; ring
      have h_zt_v : ‖zt - v‖ ^ 2 = ‖p - v‖ ^ 2 + 2 * t * inner ℝ (p - v) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
        dsimp [zt]; have : (p + t • (z - p)) - v = (p - v) + t • (z - p) := by abel
        rw [this, norm_add_sq_real]; simp [inner_smul_right, norm_smul, abs_of_pos htpos]; ring
      have h_quad_diff : (a / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (b / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) =
          t * inner ℝ (a • (u - p) + b • (v - p)) (z - p) - (σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
        rw [h_u_zt, h_zt_v]
        have hexpand : inner ℝ (a • (u - p) + b • (v - p)) (z - p) =
            a * inner ℝ (u - p) (z - p) + b * inner ℝ (v - p) (z - p) := by
          simp [inner_add_left, inner_smul_left]
        rw [hexpand]
        have hsign : inner ℝ (v - p) (z - p) = -inner ℝ (p - v) (z - p) := by
          have h_eq : v - p = -(p - v) := by abel
          rw [h_eq, inner_neg_left]
        rw [hsign]
        dsimp [σ]
        ring
      have h_rearr : f' zt - f' p ≥ (a / 2) * (‖u - p‖ ^ 2 - ‖u - zt‖ ^ 2) + (b / 2) * (‖p - v‖ ^ 2 - ‖zt - v‖ ^ 2) := by linarith
      have h_conv_rearr : f' zt - f' p ≤ t * (f' z - f' p) := by linarith
      have h_mid := le_trans h_rearr h_conv_rearr
      rw [h_quad_diff] at h_mid
      have h_nonneg_correction : 0 ≤ -(σ / 2) * t ^ 2 * ‖z - p‖ ^ 2 := by
        have : σ / 2 ≤ 0 := by linarith
        nlinarith [sq_nonneg (t * ‖z - p‖)]
      have h_direct : t * (f' z - f' p) ≥ t * inner ℝ (a • (u - p) + b • (v - p)) (z - p) := by nlinarith
      have h_result : f' z - f' p ≥ inner ℝ (a • (u - p) + b • (v - p)) (z - p) :=
        le_of_mul_le_mul_left h_direct htpos
      linarith

private lemma subgrad_to_ine_f {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f : H → ℝ} {xbar ybar : H} {β : ℝ} (hβpos : β > 0)
    (hsubgrad : ∀ z, f z ≥ f xbar + inner ℝ (β • (ybar - xbar)) (z - xbar)) :
    ∀ ξ, f xbar + (β / 2) * ‖xbar - ybar‖ ^ 2 ≤ f ξ + (β / 2) * ‖ξ - ybar‖ ^ 2 := by
  intro ξ
  have hξ := hsubgrad ξ
  have h_inner : inner ℝ (β • (ybar - xbar)) (ξ - xbar) = β * inner ℝ (ybar - xbar) (ξ - xbar) := by
    simp [inner_smul_left]
  rw [h_inner] at hξ
  have h_sq_diff : (β / 2) * ‖ξ - ybar‖ ^ 2 - (β / 2) * ‖xbar - ybar‖ ^ 2 =
      - β * inner ℝ (ybar - xbar) (ξ - xbar) + (β / 2) * ‖ξ - xbar‖ ^ 2 := by
    calc
      (β / 2) * ‖ξ - ybar‖ ^ 2 - (β / 2) * ‖xbar - ybar‖ ^ 2 =
          (β / 2) * (‖ξ - ybar‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by ring
      _ = (β / 2) * (‖(ξ - xbar) + (xbar - ybar)‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
        rw [show ξ - ybar = (ξ - xbar) + (xbar - ybar) by abel]
      _ = (β / 2) * (‖ξ - xbar‖ ^ 2 + 2 * inner ℝ (ξ - xbar) (xbar - ybar) + ‖xbar - ybar‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
        rw [norm_add_sq_real]
      _ = (β / 2) * (‖ξ - xbar‖ ^ 2 + 2 * inner ℝ (ξ - xbar) (xbar - ybar)) := by ring
      _ = (β / 2) * ‖ξ - xbar‖ ^ 2 + β * inner ℝ (ξ - xbar) (xbar - ybar) := by ring
      _ = (β / 2) * ‖ξ - xbar‖ ^ 2 - β * inner ℝ (ybar - xbar) (ξ - xbar) := by
        have hinner : inner ℝ (ξ - xbar) (xbar - ybar) =
            -inner ℝ (ybar - xbar) (ξ - xbar) := by
          calc
            inner ℝ (ξ - xbar) (xbar - ybar) =
                inner ℝ (xbar - ybar) (ξ - xbar) := real_inner_comm _ _
            _ = inner ℝ (-(ybar - xbar)) (ξ - xbar) := by
              rw [show xbar - ybar = -(ybar - xbar) by abel]
            _ = -inner ℝ (ybar - xbar) (ξ - xbar) := by rw [inner_neg_left]
        rw [hinner]
        ring_nf
      _ = - β * inner ℝ (ybar - xbar) (ξ - xbar) + (β / 2) * ‖ξ - xbar‖ ^ 2 := by
        ring
  have h_nonneg : (β / 2) * ‖ξ - xbar‖ ^ 2 ≥ 0 := by nlinarith [sq_nonneg ‖ξ - xbar‖]
  linarith

private lemma subgrad_to_ine_g {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {g : H → ℝ} {xbar ybar : H} {μ : ℝ} (hμpos : μ > 0)
    (hsubgrad : ∀ z, g z ≥ g ybar + inner ℝ (μ • (xbar - ybar)) (z - ybar)) :
    ∀ η, g ybar + (μ / 2) * ‖xbar - ybar‖ ^ 2 ≤ g η + (μ / 2) * ‖xbar - η‖ ^ 2 := by
  intro η
  have hη := hsubgrad η
  have h_inner : inner ℝ (μ • (xbar - ybar)) (η - ybar) = μ * inner ℝ (xbar - ybar) (η - ybar) := by
    simp [inner_smul_left]
  rw [h_inner] at hη
  have h_sq_diff : (μ / 2) * ‖xbar - η‖ ^ 2 - (μ / 2) * ‖xbar - ybar‖ ^ 2 =
      - μ * inner ℝ (xbar - ybar) (η - ybar) + (μ / 2) * ‖η - ybar‖ ^ 2 := by
    calc
      (μ / 2) * ‖xbar - η‖ ^ 2 - (μ / 2) * ‖xbar - ybar‖ ^ 2 =
          (μ / 2) * (‖xbar - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by ring
      _ = (μ / 2) * (‖(xbar - ybar) + (ybar - η)‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
        rw [show xbar - η = (xbar - ybar) + (ybar - η) by abel]
      _ = (μ / 2) * (‖xbar - ybar‖ ^ 2 + 2 * inner ℝ (xbar - ybar) (ybar - η) + ‖ybar - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
        rw [norm_add_sq_real]
      _ = (μ / 2) * (2 * inner ℝ (xbar - ybar) (ybar - η) + ‖η - ybar‖ ^ 2) := by
        rw [norm_sub_rev ybar η]
        ring
      _ = (μ / 2) * ‖η - ybar‖ ^ 2 + μ * inner ℝ (xbar - ybar) (ybar - η) := by ring_nf
      _ = (μ / 2) * ‖η - ybar‖ ^ 2 - μ * inner ℝ (xbar - ybar) (η - ybar) := by
        rw [show ybar - η = -(η - ybar) by abel, inner_neg_right]
        ring_nf
      _ = - μ * inner ℝ (xbar - ybar) (η - ybar) + (μ / 2) * ‖η - ybar‖ ^ 2 := by
        ring
  have h_nonneg : (μ / 2) * ‖η - ybar‖ ^ 2 ≥ 0 := by nlinarith [sq_nonneg ‖η - ybar‖]
  linarith

/- Boundedness of α, ν from H47 (summable positive variations) -/
private lemma bounded_of_H47_posPart {s : ℕ → ℝ} (h_nonneg : ∀ n, s n ≥ 0)
    (h_summable : Summable (fun n => max (s (n+1) - s n) 0)) : ∃ C, ∀ n, s n ≤ C := by
  set total := ∑' n, max (s (n+1) - s n) 0
  have h_nonneg_term : ∀ n, 0 ≤ max (s (n+1) - s n) 0 := by
    intro n; exact le_max_right _ _
  refine ⟨s 0 + total, λ n => ?_⟩
  have h_telescope : s n = s 0 + (Finset.sum (Finset.range n) fun k => s (k+1) - s k) := by
    induction' n with m ih
    · simp
    · rw [Finset.sum_range_succ]
      nlinarith
  rw [h_telescope]
  have h_partial_le_total :
      (Finset.sum (Finset.range n) fun k => max (s (k+1) - s k) 0) ≤ total := by
    simpa [total] using h_summable.sum_le_tsum (Finset.range n) (fun k hk => h_nonneg_term k)
  have h_diff_le : ∀ k, s (k+1) - s k ≤ max (s (k+1) - s k) 0 := by
    intro k; exact le_max_left _ _
  have h_sum_le : (Finset.sum (Finset.range n) fun k => s (k+1) - s k) ≤
      (Finset.sum (Finset.range n) fun k => max (s (k+1) - s k) 0) :=
    Finset.sum_le_sum (fun k hk => h_diff_le k)
  linarith

/- Weak sequential lower semicontinuity of a convex, norm-lsc function on a Hilbert space.
   If xₙ ⇀ x weakly, then ∀ ε>0, eventually f(xₙ n) ≥ f x - ε.
   Proof: sublevel sets of convex lsc f are closed and convex, hence weakly sequentially closed
   (Foundation Corollary 3.35). If the conclusion failed, a subsequence would lie in a sublevel
   set {z | f z ≤ f x - ε}, and by weak sequential closedness the weak limit x would belong to
   the same set, giving f x ≤ f x - ε, contradiction. -/
private lemma weakly_seq_lsc_of_convex_lsc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hf_lsc : LowerSemicontinuous f) (xn : ℕ → H) (x : H)
    (h_weak : Tendsto (fun n => toWeakSpace ℝ H (xn n)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    ∀ ε > 0, ∀ᶠ n in atTop, f (xn n) ≥ f x - ε := by
  intro ε hε
  by_contra! h_not
  have h_freq : ∃ᶠ n in atTop, f (xn n) < f x - ε := by
    simpa [not_eventually] using h_not
  have h_exists : ∀ N : ℕ, ∃ n ≥ N, f (xn n) < f x - ε := by
    intro N
    exact (Filter.frequently_atTop.mp h_freq) N
  set ψ : ℕ → ℕ := fun k =>
    Nat.recOn k (Nat.find (h_exists 0))
      (fun _ prev => Nat.find (h_exists (prev + 1))) with hψ_def
  have hψ_val : ∀ k, f (xn (ψ k)) < f x - ε := by
    intro k
    induction k with
    | zero =>
        simpa [hψ_def] using (Nat.find_spec (h_exists 0)).2
    | succ k ih =>
        simpa [hψ_def] using (Nat.find_spec (h_exists (ψ k + 1))).2
  have hψ_step : ∀ k, ψ k < ψ (k + 1) := by
    intro k
    have hle : ψ k + 1 ≤ ψ (k + 1) := by
      simpa [hψ_def] using (Nat.find_spec (h_exists (ψ k + 1))).1
    exact Nat.lt_of_succ_le hle
  have hψ_mono : StrictMono ψ := strictMono_nat_of_lt_succ hψ_step
  have h_subseq_weak : Tendsto (fun k => toWeakSpace ℝ H (xn (ψ k))) atTop (𝓝 (toWeakSpace ℝ H x)) :=
    h_weak.comp (StrictMono.tendsto_atTop hψ_mono)
  set C : Set H := {z | f z ≤ f x - ε} with hC_def
  have hC_closed : IsClosed C := by
    have h_open : IsOpen (f⁻¹' Set.Ioi (f x - ε)) := hf_lsc.isOpen_preimage (f x - ε)
    have hC_eq : C = (f⁻¹' Set.Ioi (f x - ε))ᶜ := by
      ext z; simp [hC_def]
    rw [hC_eq]
    exact isClosed_compl_iff.mpr h_open
  have hC_convex : Convex ℝ C := by
    rw [hC_def]
    intro a ha b hb a' b' ha'_nonneg hb'_nonneg hab
    have h_conv_raw := hf_conv.2 (mem_univ a) (mem_univ b) ha'_nonneg hb'_nonneg hab
    replace h_conv_raw : f (a' • a + b' • b) ≤ a' * f a + b' * f b := by
      simpa [smul_eq_mul] using h_conv_raw
    have ha_val : f a ≤ f x - ε := ha
    have hb_val : f b ≤ f x - ε := hb
    have h_sum : a' * f a + b' * f b ≤ f x - ε := by
      have ha_mul : a' * f a ≤ a' * (f x - ε) :=
        mul_le_mul_of_nonneg_left ha_val ha'_nonneg
      have hb_mul : b' * f b ≤ b' * (f x - ε) :=
        mul_le_mul_of_nonneg_left hb_val hb'_nonneg
      have hcoeff : a' * (f x - ε) + b' * (f x - ε) = f x - ε := by
        calc
          a' * (f x - ε) + b' * (f x - ε) = (a' + b') * (f x - ε) := by ring
          _ = 1 * (f x - ε) := by rw [hab]
          _ = f x - ε := by ring
      nlinarith
    exact le_trans h_conv_raw h_sum
  have h_mem : ∀ k, xn (ψ k) ∈ C := by
    intro k; rw [hC_def]; exact (hψ_val k).le
  have hx_mem_C : x ∈ C :=
    mem_of_tendsto_weakly_of_isClosed_convex hC_closed hC_convex h_mem h_subseq_weak
  rw [hC_def] at hx_mem_C
  change f x ≤ f x - ε at hx_mem_C
  linarith

private lemma tendsto_of_tendsto_nat_succ {α : Type*} [TopologicalSpace α]
    {a : ℕ → α} {l : α}
    (h : Tendsto (fun n => a (n + 1)) atTop (𝓝 l)) :
    Tendsto a atTop (𝓝 l) := by
  intro s hs
  rcases (eventually_atTop.1 (h hs)) with ⟨N, hN⟩
  exact eventually_atTop.2 ⟨N + 1, fun n hn => by
    cases n with
    | zero => omega
    | succ m =>
        exact hN m (by omega)⟩

private lemma bounded_range_of_succ_distance_tendsto
    {H : Type*} [NormedAddCommGroup H] {x : ℕ → H} {z : H} {l : ℝ}
    (h : Tendsto (fun n => ‖x (n + 1) - z‖) atTop (𝓝 l)) :
    Bornology.IsBounded (Set.range x) := by
  have hdist : Tendsto (fun n => ‖x n - z‖) atTop (𝓝 l) :=
    tendsto_of_tendsto_nat_succ h
  have hb_dist : Bornology.IsBounded (Set.range (fun n => ‖x n - z‖)) :=
    Metric.isBounded_range_of_tendsto _ hdist
  rcases isBounded_iff_forall_norm_le.mp hb_dist with ⟨M, hM⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M + ‖z‖, ?_⟩
  rintro w ⟨n, rfl⟩
  have hdist_le : ‖x n - z‖ ≤ M := by
    have := hM (‖x n - z‖) (Set.mem_range_self n)
    simpa [Real.norm_eq_abs] using this
  calc
    ‖x n‖ = ‖(x n - z) + z‖ := by
      congr 1
      abel
    _ ≤ ‖x n - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ M + ‖z‖ := by linarith

private lemma tendsto_inner_zero_of_tendsto_zero_of_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u w : ℕ → H}
    (hu : Tendsto u atTop (𝓝 (0 : H)))
    (hw : Bornology.IsBounded (Set.range w)) :
    Tendsto (fun n => inner ℝ (u n) (w n)) atTop (𝓝 0) := by
  rcases isBounded_iff_forall_norm_le.mp hw with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := by
    exact le_trans (norm_nonneg (w 0)) (hM _ (Set.mem_range_self 0))
  have hu_norm : Tendsto (fun n => ‖u n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hu.norm
  have hprod : Tendsto (fun n => ‖u n‖ * M) atTop (𝓝 (0 : ℝ)) := by
    simpa [mul_zero, zero_mul] using hu_norm.mul_const M
  have h_abs : Tendsto (fun n => |inner ℝ (u n) (w n)|) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hprod
    · intro n
      exact abs_nonneg _
    · intro n
      calc
        |inner ℝ (u n) (w n)| ≤ ‖u n‖ * ‖w n‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖u n‖ * M :=
          mul_le_mul_of_nonneg_left (hM _ (Set.mem_range_self n)) (norm_nonneg _)
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

private lemma subdifferential_demiclosed_real_valued
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hf_lsc : LowerSemicontinuous f)
    {x_seq u_seq : ℕ → H} {x u : H}
    (hx_weak : Tendsto (fun n => toWeakSpace ℝ H (x_seq n)) atTop
      (𝓝 (toWeakSpace ℝ H x)))
    (hu_strong : Tendsto u_seq atTop (𝓝 u))
    (hsub : ∀ n z, f z ≥ f (x_seq n) + inner ℝ (u_seq n) (z - x_seq n)) :
    ∀ z, f z ≥ f x + inner ℝ u (z - x) := by
  intro z
  have htarget_weak :
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (z - x_seq n)) atTop
        (𝓝 (toWeakSpace ℝ H (z - x))) := by
    simpa [sub_eq_add_neg] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => toWeakSpace ℝ H z) atTop
        (𝓝 (toWeakSpace ℝ H z))).sub hx_weak)
  have htarget_bdd : Bornology.IsBounded (Set.range (fun n : ℕ => z - x_seq n)) :=
    bounded_range_of_tendsto_weakly htarget_weak
  have hcoeff_zero : Tendsto (fun n : ℕ => u_seq n - u) atTop (𝓝 (0 : H)) := by
    simpa [sub_self] using
      hu_strong.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))
  have hinner1 :
      Tendsto (fun n : ℕ => inner ℝ (u_seq n - u) (z - x_seq n)) atTop
        (𝓝 (0 : ℝ)) :=
    tendsto_inner_zero_of_tendsto_zero_of_bounded hcoeff_zero htarget_bdd
  have hx_zero_weak :
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (x - x_seq n)) atTop
        (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    simpa [sub_self] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => toWeakSpace ℝ H x) atTop
        (𝓝 (toWeakSpace ℝ H x))).sub hx_weak)
  have hinner2 : Tendsto (fun n : ℕ => inner ℝ u (x - x_seq n)) atTop
      (𝓝 (0 : ℝ)) := by
    have h := (weakConvergence_iff_forall_tendsto_inner_right
      (fun n : ℕ => x - x_seq n) 0).mp hx_zero_weak u
    simpa [real_inner_comm, inner_zero_right] using h
  have hinner_conv :
      Tendsto (fun n : ℕ => inner ℝ (u_seq n) (z - x_seq n)) atTop
        (𝓝 (inner ℝ u (z - x))) := by
    have hdecomp : ∀ n,
        inner ℝ (u_seq n) (z - x_seq n) - inner ℝ u (z - x) =
          inner ℝ (u_seq n - u) (z - x_seq n) + inner ℝ u (x - x_seq n) := by
      intro n
      have hzx : z - x_seq n = (z - x) + (x - x_seq n) := by abel
      have hu_seq_expand :
          inner ℝ (u_seq n) (z - x_seq n) =
            inner ℝ (u_seq n) (z - x) + inner ℝ (u_seq n) (x - x_seq n) := by
        rw [hzx, inner_add_right]
      have hu_expand :
          inner ℝ u (z - x_seq n) =
            inner ℝ u (z - x) + inner ℝ u (x - x_seq n) := by
        rw [hzx, inner_add_right]
      have hdiff_expand :
          inner ℝ (u_seq n - u) (z - x_seq n) =
            inner ℝ (u_seq n) (z - x_seq n) - inner ℝ u (z - x_seq n) := by
        simp [inner_sub_left]
      rw [hdiff_expand, hu_seq_expand, hu_expand]
      ring
    have hdiff :
        Tendsto (fun n : ℕ =>
          inner ℝ (u_seq n) (z - x_seq n) - inner ℝ u (z - x)) atTop
          (𝓝 (0 : ℝ)) := by
      simpa [hdecomp] using hinner1.add hinner2
    have hconst : Tendsto (fun _ : ℕ => inner ℝ u (z - x)) atTop
        (𝓝 (inner ℝ u (z - x))) := tendsto_const_nhds
    simpa [sub_add_cancel] using hdiff.add hconst
  apply le_of_forall_pos_le_add
  intro ε hεpos
  have hlsc : ∀ᶠ n in atTop, f (x_seq n) ≥ f x - ε / 2 :=
    weakly_seq_lsc_of_convex_lsc hf_conv hf_lsc x_seq x hx_weak (ε / 2) (by linarith)
  have hinner_ev : ∀ᶠ n in atTop,
      inner ℝ (u_seq n) (z - x_seq n) ≥ inner ℝ u (z - x) - ε / 2 := by
    filter_upwards [hinner_conv
      (Metric.ball_mem_nhds (inner ℝ u (z - x)) (by linarith : ε / 2 > 0))] with n hn
    have hdist : |inner ℝ (u_seq n) (z - x_seq n) - inner ℝ u (z - x)| < ε / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hn
    rw [abs_lt] at hdist
    linarith
  rcases (hlsc.and hinner_ev).exists with ⟨n, hfn, hin⟩
  have hz := hsub n z
  linarith

private lemma tendsto_smul_of_abs_bounded_of_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {c : ℕ → ℝ} {v : ℕ → H} {C : ℝ}
    (hc : ∀ n, |c n| ≤ C)
    (hv : Tendsto v atTop (𝓝 (0 : H))) :
    Tendsto (fun n : ℕ => c n • v n) atTop (𝓝 (0 : H)) := by
  have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg (c 0)) (hc 0)
  have hv_norm : Tendsto (fun n : ℕ => ‖v n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using hv.norm
  have hprod : Tendsto (fun n : ℕ => C * ‖v n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa [mul_zero] using (tendsto_const_nhds.mul hv_norm : Tendsto (fun n : ℕ => C * ‖v n‖) atTop (𝓝 (C * 0)))
  have hnorm : Tendsto (fun n : ℕ => ‖c n • v n‖) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hprod
    · intro n
      exact norm_nonneg _
    · intro n
      calc
        ‖c n • v n‖ = |c n| * ‖v n‖ := norm_smul _ _
        _ ≤ C * ‖v n‖ := mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

private lemma weak_subseq_succ_of_step_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {x : ℕ → H} {χ : ℕ → ℕ} {xbar : H}
    (hχ_mono : StrictMono χ)
    (hxχ_weak : Tendsto (fun k : ℕ => toWeakSpace ℝ H (x (χ k))) atTop
      (𝓝 (toWeakSpace ℝ H xbar)))
    (hdiff : Tendsto (fun n : ℕ => x (n + 1) - x n) atTop (𝓝 (0 : H))) :
    Tendsto (fun k : ℕ => toWeakSpace ℝ H (x (χ k + 1))) atTop
      (𝓝 (toWeakSpace ℝ H xbar)) := by
  have hdiff_comp : Tendsto (fun k : ℕ => x (χ k + 1) - x (χ k)) atTop (𝓝 (0 : H)) := by
    simpa using hdiff.comp hχ_mono.tendsto_atTop
  have hdiff_weak : Tendsto (fun k : ℕ => toWeakSpace ℝ H (x (χ k + 1) - x (χ k))) atTop
      (𝓝 (toWeakSpace ℝ H (0 : H))) := by
    have := ((toWeakSpaceCLM ℝ H).continuous.tendsto (0 : H)).comp hdiff_comp
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using this
  have hsum : Tendsto (fun k : ℕ => toWeakSpace ℝ H ((x (χ k + 1) - x (χ k)) + x (χ k))) atTop
      (𝓝 (toWeakSpace ℝ H ((0 : H) + xbar))) := hdiff_weak.add hxχ_weak
  simpa [add_zero, sub_add_cancel] using hsum

private lemma tendsto_of_lower_bound_and_eventual_upper
    {s : ℕ → ℝ} {a : ℝ}
    (h_lower : ∀ n, a ≤ s n)
    (h_upper : ∀ ε > 0, ∀ᶠ n in atTop, s n ≤ a + ε) :
    Tendsto s atTop (𝓝 a) := by
  rw [tendsto_order]
  constructor
  · intro a' ha'
    exact eventually_atTop.2 ⟨0, fun n _ => lt_of_lt_of_le ha' (h_lower n)⟩
  · intro a' ha'
    have hε : 0 < (a' - a) / 2 := by linarith
    filter_upwards [h_upper ((a' - a) / 2) hε] with n hn
    linarith

private lemma ine_minimizes_L_beta_mu
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ}
    (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hg_conv : ConvexOn ℝ (Set.univ : Set H) g)
    (hβpos : β > 0) (hμpos : μ > 0)
    {xbar ybar : H}
    (hine : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar) :
    ∀ ξ η : H, L_beta_mu f g β μ xbar ybar ≤ L_beta_mu f g β μ ξ η := by
  rintro ξ η
  rcases hine with ⟨hx_opt, hy_opt⟩
  have hx_simp : ∀ ξ' : H, f xbar + β * (‖xbar - ybar‖ ^ 2 / 2) ≤
      f ξ' + β * (‖ξ' - ybar‖ ^ 2 / 2) := by
    intro ξ'
    simpa using hx_opt ξ'
  have hy_simp : ∀ η' : H, g ybar + μ * (‖xbar - ybar‖ ^ 2 / 2) ≤
      g η' + μ * (‖xbar - η'‖ ^ 2 / 2) := by
    intro η'
    simpa using hy_opt η'
  have hmin_x : ∀ ξ' : H,
      f xbar + ((0 : ℝ) / 2) * ‖xbar - xbar‖ ^ 2 +
        (β / 2) * ‖xbar - ybar‖ ^ 2 ≤
      f ξ' + ((0 : ℝ) / 2) * ‖xbar - ξ'‖ ^ 2 +
        (β / 2) * ‖ξ' - ybar‖ ^ 2 := by
    intro ξ'
    have h := hx_simp ξ'
    simp
    nlinarith
  have hmin_y : ∀ η' : H,
      g ybar + ((0 : ℝ) / 2) * ‖ybar - ybar‖ ^ 2 +
        (μ / 2) * ‖ybar - xbar‖ ^ 2 ≤
      g η' + ((0 : ℝ) / 2) * ‖ybar - η'‖ ^ 2 +
        (μ / 2) * ‖η' - xbar‖ ^ 2 := by
    intro η'
    have h := hy_simp η'
    simp [norm_sub_rev]
    nlinarith
  have hf_sub : f ξ ≥ f xbar + inner ℝ (β • (ybar - xbar)) (ξ - xbar) := by
    have h := subgrad_of_min_quadratic hf_conv hmin_x ξ
    simpa using h
  have hg_sub : g η ≥ g ybar + inner ℝ (μ • (xbar - ybar)) (η - ybar) := by
    have h := subgrad_of_min_quadratic hg_conv hmin_y η
    simpa using h
  set p := ξ - xbar with hp_def
  set q := η - ybar with hq_def
  set d := xbar - ybar with hd_def
  have hsum : μ * f ξ + β * g η ≥ μ * f xbar + β * g ybar +
      (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) := by
    have h1 : μ * f ξ ≥ μ * f xbar + μ * inner ℝ (β • (ybar - xbar)) (ξ - xbar) := by
      nlinarith
    have h2 : β * g η ≥ β * g ybar + β * inner ℝ (μ • (xbar - ybar)) (η - ybar) := by
      nlinarith
    have h_inner1 : μ * inner ℝ (β • (ybar - xbar)) (ξ - xbar) =
        (β * μ) * inner ℝ (ybar - xbar) p := by
      rw [inner_smul_left]
      simp [hp_def]
      ring
    have h_inner2 : β * inner ℝ (μ • (xbar - ybar)) (η - ybar) =
        (β * μ) * inner ℝ d q := by
      rw [inner_smul_left]
      simp [hd_def, hq_def]
      ring
    nlinarith
  have h_decomp : ‖ξ - η‖ ^ 2 = ‖d‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 +
      2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
    calc
      ‖ξ - η‖ ^ 2 = ‖(p + d) - q‖ ^ 2 := by
        dsimp [p, d, q]
        abel
      _ = ‖p + d‖ ^ 2 - 2 * inner ℝ (p + d) q + ‖q‖ ^ 2 :=
        norm_sub_sq_real (p + d) q
      _ = (‖p‖ ^ 2 + 2 * inner ℝ p d + ‖d‖ ^ 2) -
          2 * (inner ℝ p q + inner ℝ d q) + ‖q‖ ^ 2 := by
        rw [norm_add_sq_real p d, inner_add_left]
      _ = ‖d‖ ^ 2 + ‖p‖ ^ 2 + ‖q‖ ^ 2 +
          2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
        rw [real_inner_comm p d]
        ring
  have hLpre : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
      (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
      (β * μ / 2) * (‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := by
    dsimp [L_beta_mu]
    nlinarith
  have h_norm_diff : ‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2 =
      ‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q := by
    rw [h_decomp]
    dsimp [d]
    nlinarith
  have hLmid : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
      (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
      (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) := by
    calc
      L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
          (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
          (β * μ / 2) * (‖ξ - η‖ ^ 2 - ‖xbar - ybar‖ ^ 2) := hLpre
      _ = L_beta_mu f g β μ xbar ybar +
          (β * μ) * (inner ℝ (ybar - xbar) p + inner ℝ d q) +
          (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) := by
        rw [h_norm_diff]
  have h_inner_yp : inner ℝ (ybar - xbar) p = -inner ℝ d p := by
    calc
      inner ℝ (ybar - xbar) p = inner ℝ (-(xbar - ybar)) p := by simp
      _ = -inner ℝ (xbar - ybar) p := by rw [inner_neg_left]
      _ = -inner ℝ d p := by simp [hd_def]
  rw [h_inner_yp] at hLmid
  have h_key : (β * μ) * (-inner ℝ d p + inner ℝ d q) +
      (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q) =
      (β * μ / 2) * ‖p - q‖ ^ 2 := by
    calc
      (β * μ) * (-inner ℝ d p + inner ℝ d q) +
          (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 + 2 * inner ℝ d p - 2 * inner ℝ p q - 2 * inner ℝ d q)
          = (β * μ / 2) * (‖p‖ ^ 2 + ‖q‖ ^ 2 - 2 * inner ℝ p q) := by
        ring
      _ = (β * μ / 2) * ‖p - q‖ ^ 2 := by
        rw [norm_sub_sq_real p q]
        ring
  have hLfinal : L_beta_mu f g β μ ξ η ≥ L_beta_mu f g β μ xbar ybar +
      (β * μ / 2) * ‖p - q‖ ^ 2 := by
    linarith
  have h_nonneg : (β * μ / 2) * ‖p - q‖ ^ 2 ≥ 0 := by
    have h_coeff : 0 ≤ β * μ / 2 := by nlinarith
    nlinarith [sq_nonneg ‖p - q‖]
  nlinarith

private lemma L_beta_mu_perturbation_ineq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hg_conv : ConvexOn ℝ (Set.univ : Set H) g)
    (hβ_pos : β > 0) (hμ_pos : μ > 0)
    {x y : ℕ → H}
    (h_x_min : ∀ n ξ,
      f (x (n+1)) + (α n / 2) * ‖x n - x (n+1)‖ ^ 2 +
          (β / 2) * ‖x (n+1) - y n‖ ^ 2 ≤
        f ξ + (α n / 2) * ‖x n - ξ‖ ^ 2 + (β / 2) * ‖ξ - y n‖ ^ 2)
    (h_y_min : ∀ n η,
      g (y (n+1)) + (μ / 2) * ‖x (n+1) - y (n+1)‖ ^ 2 +
          (ν n / 2) * ‖y n - y (n+1)‖ ^ 2 ≤
        g η + (μ / 2) * ‖x (n+1) - η‖ ^ 2 + (ν n / 2) * ‖y n - η‖ ^ 2)
    (n : ℕ) (ξ η : H) :
      L_beta_mu f g β μ (x (n+1)) (y (n+1)) ≤
        L_beta_mu f g β μ ξ η +
          inner ℝ (μ • (α n • (x (n+1) - x n) + β • (y (n+1) - y n)))
            (ξ - x (n+1)) +
          inner ℝ (β • (ν n • (y (n+1) - y n))) (η - y (n+1)) := by
  set xn := x n
  set xn1 := x (n+1)
  set yn := y n
  set yn1 := y (n+1)
  set dx := ξ - xn1
  set dy := η - yn1
  set p := xn1 - yn1
  set cx := α n • (xn - xn1) + β • (yn - xn1)
  set cy := μ • (xn1 - yn1) + ν n • (yn - yn1)
  have hxsub : f ξ ≥ f xn1 + inner ℝ cx dx := by
    have h := subgrad_of_min_quadratic hf_conv (h_x_min n) ξ
    simpa [xn, xn1, yn, dx, cx] using h
  have hymin_n : ∀ ζ : H,
      g yn1 + (μ / 2) * ‖xn1 - yn1‖ ^ 2 + (ν n / 2) * ‖yn1 - yn‖ ^ 2 ≤
        g ζ + (μ / 2) * ‖xn1 - ζ‖ ^ 2 + (ν n / 2) * ‖ζ - yn‖ ^ 2 := by
    intro ζ
    have h := h_y_min n ζ
    simpa [xn1, yn1, yn, norm_sub_rev] using h
  have hysub : g η ≥ g yn1 + inner ℝ cy dy := by
    have h := subgrad_of_min_quadratic hg_conv hymin_n η
    simpa [xn1, yn1, yn, dy, cy] using h
  have hf_part : μ * f xn1 ≤ μ * f ξ - inner ℝ (μ • cx) dx := by
    have hmul : μ * f xn1 + μ * inner ℝ cx dx ≤ μ * f ξ := by
      have := mul_le_mul_of_nonneg_left hxsub (le_of_lt hμ_pos)
      nlinarith
    have hinner : μ * inner ℝ cx dx = inner ℝ (μ • cx) dx := by
      simp [inner_smul_left]
    rw [hinner] at hmul
    linarith
  have hg_part : β * g yn1 ≤ β * g η - inner ℝ (β • cy) dy := by
    have hmul : β * g yn1 + β * inner ℝ cy dy ≤ β * g η := by
      have := mul_le_mul_of_nonneg_left hysub (le_of_lt hβ_pos)
      nlinarith
    have hinner : β * inner ℝ cy dy = inner ℝ (β • cy) dy := by
      simp [inner_smul_left]
    rw [hinner] at hmul
    linarith
  have hnorm_conv : ‖ξ - η‖ ^ 2 ≥ ‖p‖ ^ 2 + 2 * inner ℝ p ((ξ - η) - p) := by
    have hsq := norm_sub_sq_real (ξ - η) p
    have hinner : inner ℝ p ((ξ - η) - p) = inner ℝ (ξ - η) p - ‖p‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm p (ξ - η)]
    rw [hinner]
    nlinarith [sq_nonneg ‖(ξ - η) - p‖]
  have hdiff : (ξ - η) - p = dx - dy := by
    dsimp [dx, dy, p, xn1, yn1]
    abel
  have hinner_diff : inner ℝ p ((ξ - η) - p) = inner ℝ p dx - inner ℝ p dy := by
    rw [hdiff, inner_sub_right]
  have hquad : (β * μ / 2) * ‖p‖ ^ 2 ≤
      (β * μ / 2) * ‖ξ - η‖ ^ 2 -
        inner ℝ (μ • (β • p)) dx + inner ℝ (β • (μ • p)) dy := by
    rw [hinner_diff] at hnorm_conv
    have hix : inner ℝ (μ • (β • p)) dx = (β * μ) * inner ℝ p dx := by
      simp [inner_smul_left]
      ring
    have hiy : inner ℝ (β • (μ • p)) dy = (β * μ) * inner ℝ p dy := by
      simp [inner_smul_left]
      ring
    rw [hix, hiy]
    have hβμ_nonneg : 0 ≤ β * μ / 2 := by positivity
    nlinarith
  have hcoefx :
      -inner ℝ (μ • cx) dx - inner ℝ (μ • (β • p)) dx =
        inner ℝ (μ • (α n • (xn1 - xn) + β • (yn1 - yn))) dx := by
    have hvec : -(μ • cx) - μ • (β • p) =
        μ • (α n • (xn1 - xn) + β • (yn1 - yn)) := by
      dsimp [cx, p, xn, xn1, yn, yn1]
      module
    calc
      -inner ℝ (μ • cx) dx - inner ℝ (μ • (β • p)) dx
          = inner ℝ (-(μ • cx) - μ • (β • p)) dx := by
            simp [inner_sub_left, inner_neg_left]
      _ = inner ℝ (μ • (α n • (xn1 - xn) + β • (yn1 - yn))) dx := by
            rw [hvec]
  have hcoefy :
      -inner ℝ (β • cy) dy + inner ℝ (β • (μ • p)) dy =
        inner ℝ (β • (ν n • (yn1 - yn))) dy := by
    have hvec : -(β • cy) + β • (μ • p) = β • (ν n • (yn1 - yn)) := by
      dsimp [cy, p, xn1, yn1, yn]
      module
    calc
      -inner ℝ (β • cy) dy + inner ℝ (β • (μ • p)) dy
          = inner ℝ (-(β • cy) + β • (μ • p)) dy := by
            simp [inner_add_left, inner_neg_left]
      _ = inner ℝ (β • (ν n • (yn1 - yn))) dy := by
            rw [hvec]
  dsimp [L_beta_mu]
  dsimp [xn, xn1, yn, yn1, dx, dy, p] at *
  nlinarith [hf_part, hg_part, hquad, hcoefx, hcoefy]

private lemma first_value_tendsto_of_weighted_sum_and_lsc
    {a b : ℕ → ℝ} {a0 b0 μ β : ℝ}
    (hμ_pos : μ > 0) (hβ_pos : β > 0)
    (hsum : Tendsto (fun n => μ * a n + β * b n) atTop
      (𝓝 (μ * a0 + β * b0)))
    (ha_lsc : ∀ ε > 0, ∀ᶠ n in atTop, a n ≥ a0 - ε)
    (hb_lsc : ∀ ε > 0, ∀ᶠ n in atTop, b n ≥ b0 - ε) :
    Tendsto a atTop (𝓝 a0) := by
  rw [tendsto_order]
  constructor
  · intro r hr
    have hε : 0 < (a0 - r) / 2 := by linarith
    filter_upwards [ha_lsc ((a0 - r) / 2) hε] with n hn
    linarith
  · intro r hr
    set δ := r - a0 with hδ_def
    have hδ_pos : δ > 0 := by dsimp [δ]; linarith
    have hsum_rad_pos : μ * δ / 4 > 0 := by positivity
    have hb_eps_pos : μ * δ / (4 * β) > 0 := by positivity
    have hsum_ev : ∀ᶠ n in atTop,
        μ * a n + β * b n < μ * a0 + β * b0 + μ * δ / 4 := by
      filter_upwards [hsum (Metric.ball_mem_nhds (μ * a0 + β * b0) hsum_rad_pos)] with n hn
      have habs : |(μ * a n + β * b n) - (μ * a0 + β * b0)| < μ * δ / 4 := by
        simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hn
      rw [abs_lt] at habs
      linarith
    have hb_ev : ∀ᶠ n in atTop, b n ≥ b0 - μ * δ / (4 * β) :=
      hb_lsc (μ * δ / (4 * β)) hb_eps_pos
    filter_upwards [hsum_ev, hb_ev] with n hsum_n hb_n
    have hb_scaled : β * b n ≥ β * (b0 - μ * δ / (4 * β)) := by
      exact mul_le_mul_of_nonneg_left hb_n (le_of_lt hβ_pos)
    have hb_scaled' : β * b n ≥ β * b0 - μ * δ / 4 := by
      calc
        β * b n ≥ β * (b0 - μ * δ / (4 * β)) := hb_scaled
        _ = β * b0 - μ * δ / 4 := by
          field_simp [hβ_pos.ne']
    have hμa : μ * a n < μ * a0 + μ * δ / 2 := by
      nlinarith
    have ha_lt : a n < a0 + δ := by
      nlinarith [hμ_pos]
    dsimp [δ] at ha_lt
    linarith

theorem theorem_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f g : H → ℝ} {β μ : ℝ} {α ν : ℕ → ℝ}
    (x_seq y_seq : ℕ → H)
    (hf_conv : ConvexOn ℝ (Set.univ : Set H) f) (hg_conv : ConvexOn ℝ (Set.univ : Set H) g)
    (hf_lsc : LowerSemicontinuous f) (hg_lsc : LowerSemicontinuous g)
    (hf_bdd_below : ∃ Mf : ℝ, ∀ x : H, f x ≥ Mf)
    (hg_bdd_below : ∃ Mg : ℝ, ∀ y : H, g y ≥ Mg)
    (hα_nonneg : ∀ n, α n ≥ 0) (hν_nonneg : ∀ n, ν n ≥ 0)
    (hβ_pos : β > 0) (hμ_pos : μ > 0)
    (h46 : Nonempty {p : H × H |
      IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
        (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 p.1 p.2})
    (hα_var_summable : Summable (fun n : ℕ => max (α (n+1) - α n) 0))
    (hν_var_summable : Summable (fun n : ℕ => max (ν (n+1) - ν n) 0))
    (h_step_x : ∀ n ξ, f (x_seq (n+1)) + α n * (‖x_seq (n+1) - x_seq n‖ ^ 2 / 2) +
      β * (‖x_seq (n+1) - y_seq n‖ ^ 2 / 2) ≤
      f ξ + α n * (‖x_seq n - ξ‖ ^ 2 / 2) + β * (‖ξ - y_seq n‖ ^ 2 / 2))
    (h_step_y : ∀ n η, g (y_seq (n+1)) + μ * (‖y_seq (n+1) - x_seq (n+1)‖ ^ 2 / 2) +
      ν n * (‖y_seq (n+1) - y_seq n‖ ^ 2 / 2) ≤
      g η + μ * (‖x_seq (n+1) - η‖ ^ 2 / 2) + ν n * (‖y_seq n - η‖ ^ 2 / 2)) :
    (∃ (xbar ybar : H),
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (x_seq n)) atTop (𝓝 (toWeakSpace ℝ H xbar)) ∧
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (y_seq n)) atTop (𝓝 (toWeakSpace ℝ H ybar)) ∧
      IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
        (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar ∧
      (∀ ξ η : H, L_beta_mu f g β μ xbar ybar ≤ L_beta_mu f g β μ ξ η) ∧
      Tendsto (fun n : ℕ => L_beta_mu f g β μ (x_seq n) (y_seq n)) atTop
        (𝓝 (L_beta_mu f g β μ xbar ybar)) ∧
      Tendsto (fun n => y_seq n - x_seq n) atTop (𝓝 (ybar - xbar)) ∧
      Tendsto (fun n => f (x_seq n)) atTop (𝓝 (f xbar)) ∧
      Tendsto (fun n => g (y_seq n)) atTop (𝓝 (g ybar))) := by
  have h46_saved := h46
  rcases h46_saved with ⟨⟨x₀, y₀⟩, hine₀⟩
  set x := x_seq with hx_def
  set y := y_seq with hy_def
  have hxpos : β > 0 := hβ_pos
  have hmupos : μ > 0 := hμ_pos
  have hβμ_pos : β * μ > 0 := mul_pos hxpos hmupos
  -- Step-wise minimization helpers.
  have h_x_min : ∀ (n : ℕ) (ξ : H), f (x (n+1)) + ((α n) / 2) * ‖x n - x (n+1)‖ ^ 2 + (β / 2) * ‖x (n+1) - y n‖ ^ 2 ≤
      f ξ + ((α n) / 2) * ‖x n - ξ‖ ^ 2 + (β / 2) * ‖ξ - y n‖ ^ 2 := by
    intro n ξ; have hstep := h_step_x n ξ; rw [hx_def, hy_def] at hstep ⊢; simp [norm_sub_rev] at hstep ⊢; nlinarith
  have h_y_min : ∀ (n : ℕ) (η : H), g (y (n+1)) + (μ / 2) * ‖x (n+1) - y (n+1)‖ ^ 2 + ((ν n) / 2) * ‖y n - y (n+1)‖ ^ 2 ≤
      g η + (μ / 2) * ‖x (n+1) - η‖ ^ 2 + ((ν n) / 2) * ‖y n - η‖ ^ 2 := by
    intro n η; have hstep := h_step_y n η; rw [hx_def, hy_def] at hstep ⊢; simp [norm_sub_rev] at hstep ⊢; nlinarith
  have h_ine_x : ∀ (xbar ybar : H), IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar → ∀ (ξ : H),
      f xbar + (β / 2) * ‖xbar - ybar‖ ^ 2 ≤ f ξ + (β / 2) * ‖ξ - ybar‖ ^ 2 := by
    intro xbar ybar hine ξ; rcases hine with ⟨hine_f, _⟩; have h := hine_f ξ; nlinarith
  have h_ine_y : ∀ (xbar ybar : H), IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar → ∀ (η : H),
      g ybar + (μ / 2) * ‖xbar - ybar‖ ^ 2 ≤ g η + (μ / 2) * ‖xbar - η‖ ^ 2 := by
    intro xbar ybar hine η; rcases hine with ⟨_, hine_g⟩; have h := hine_g η; nlinarith

  -- Lemma 4.3(a): Firm nonexpansiveness.
  have ha : ∀ (xbar ybar : H), IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar → ∀ (n : ℕ),
      ‖x (n+1) - xbar‖ ^ 2 ≤
      (1 / (α n + β)) * (α n * ‖x n - xbar‖ ^ 2 + β * ‖y n - ybar‖ ^ 2 -
        α n * ‖x (n+1) - x n‖ ^ 2 - β * ‖y n - x (n+1) - ybar + xbar‖ ^ 2) := by
    intro xbar ybar hine n
    set xn1 := x (n+1); set xn := x n; set yn := y n; set γ := α n + β
    have hγpos : γ > 0 := by linarith [hα_nonneg n]
    have h_x_min_n : ∀ ξ : H, f xn1 + ((α n) / 2) * ‖xn - xn1‖ ^ 2 + (β / 2) * ‖xn1 - yn‖ ^ 2 ≤
        f ξ + ((α n) / 2) * ‖xn - ξ‖ ^ 2 + (β / 2) * ‖ξ - yn‖ ^ 2 := by
      intro ξ; have h := h_x_min n ξ; simpa [xn1, xn, yn] using h
    have hsubgrad_xn1 : ∀ z : H, f z ≥ f xn1 + inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (z - xn1) :=
      subgrad_of_min_quadratic hf_conv h_x_min_n
    have hine_x' : ∀ ξ : H, f xbar + (β / 2) * ‖xbar - ybar‖ ^ 2 ≤ f ξ + (β / 2) * ‖ξ - ybar‖ ^ 2 :=
      h_ine_x xbar ybar hine
    have hmin_xbar : ∀ ξ : H, f xbar + ((0 : ℝ) / 2) * ‖xbar - xbar‖ ^ 2 + (β / 2) * ‖xbar - ybar‖ ^ 2 ≤
        f ξ + ((0 : ℝ) / 2) * ‖xbar - ξ‖ ^ 2 + (β / 2) * ‖ξ - ybar‖ ^ 2 := by
      intro ξ; have h := hine_x' ξ; simp; nlinarith
    have hsubgrad_xbar : ∀ z : H, f z ≥ f xbar + β * inner ℝ (ybar - xbar) (z - xbar) := by
      intro z; have h := subgrad_of_min_quadratic hf_conv hmin_xbar z
      simpa [inner_smul_left] using h
    have h1 : f xbar ≥ f xn1 + inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (xbar - xn1) := hsubgrad_xn1 xbar
    have h2 : f xn1 ≥ f xbar + β * inner ℝ (ybar - xbar) (xn1 - xbar) := hsubgrad_xbar xn1
    have hkey : α n * inner ℝ (xn - xn1) (xbar - xn1) + β * inner ℝ (yn - xn1) (xbar - xn1) -
        β * inner ℝ (ybar - xbar) (xbar - xn1) ≤ 0 := by
      have hfx_upper : f xbar - f xn1 ≤ β * inner ℝ (ybar - xbar) (xbar - xn1) := by
        have htemp : f xn1 - f xbar ≥ β * inner ℝ (ybar - xbar) (xn1 - xbar) := by linarith
        have : inner ℝ (ybar - xbar) (xn1 - xbar) = -inner ℝ (ybar - xbar) (xbar - xn1) := by
          have hx_xbar : xbar - xn1 = -(xn1 - xbar) := by abel
          rw [hx_xbar, inner_neg_right, neg_neg]
        rw [this] at htemp; linarith
      have hfx_lower : inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (xbar - xn1) ≤ f xbar - f xn1 := by linarith
      have h_expand : inner ℝ ((α n) • (xn - xn1) + β • (yn - xn1)) (xbar - xn1) =
          α n * inner ℝ (xn - xn1) (xbar - xn1) + β * inner ℝ (yn - xn1) (xbar - xn1) := by
        simp [inner_add_left, inner_smul_left]
      rw [h_expand] at hfx_lower; linarith
    have hx_inner : inner ℝ (xn - xn1) (xbar - xn1) = -inner ℝ (xn - xbar) (xn1 - xbar) + ‖xn1 - xbar‖ ^ 2 := by
      calc
        inner ℝ (xn - xn1) (xbar - xn1) = -inner ℝ (xn - xn1) (xn1 - xbar) := by
          rw [show xbar - xn1 = -(xn1 - xbar) by abel, inner_neg_right]
        _ = -inner ℝ ((xn - xbar) - (xn1 - xbar)) (xn1 - xbar) := by abel
        _ = -(inner ℝ (xn - xbar) (xn1 - xbar) - inner ℝ (xn1 - xbar) (xn1 - xbar)) := by rw [inner_sub_left]
        _ = -inner ℝ (xn - xbar) (xn1 - xbar) + ‖xn1 - xbar‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]; ring
    have hy_inner : inner ℝ (yn - xn1) (xbar - xn1) = inner ℝ (ybar - xbar) (xbar - xn1) - inner ℝ (yn - ybar) (xn1 - xbar) + ‖xn1 - xbar‖ ^ 2 := by
      have hsum : yn - xn1 = (yn - ybar) + (ybar - xbar) + (xbar - xn1) := by abel
      rw [hsum]
      calc
        inner ℝ ((yn - ybar) + (ybar - xbar) + (xbar - xn1)) (xbar - xn1) =
            inner ℝ (yn - ybar) (xbar - xn1) + inner ℝ (ybar - xbar) (xbar - xn1) + inner ℝ (xbar - xn1) (xbar - xn1) := by
          rw [inner_add_left, inner_add_left]
        _ = -inner ℝ (yn - ybar) (xn1 - xbar) + inner ℝ (ybar - xbar) (xbar - xn1) + ‖xbar - xn1‖ ^ 2 := by
          rw [show xbar - xn1 = -(xn1 - xbar) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
        _ = inner ℝ (ybar - xbar) (xbar - xn1) - inner ℝ (yn - ybar) (xn1 - xbar) + ‖xn1 - xbar‖ ^ 2 := by
          rw [norm_sub_rev]; ring
    rw [hx_inner, hy_inner] at hkey
    have h_firm : γ * ‖xn1 - xbar‖ ^ 2 ≤ (α n) * inner ℝ (xn1 - xbar) (xn - xbar) + β * inner ℝ (xn1 - xbar) (yn - ybar) := by
      have htemp : -α n * inner ℝ (xn - xbar) (xn1 - xbar) - β * inner ℝ (yn - ybar) (xn1 - xbar) + γ * ‖xn1 - xbar‖ ^ 2 ≤ 0 := by nlinarith
      have htemp2 : γ * ‖xn1 - xbar‖ ^ 2 ≤ α n * inner ℝ (xn - xbar) (xn1 - xbar) + β * inner ℝ (yn - ybar) (xn1 - xbar) := by nlinarith
      simpa [real_inner_comm (xn1 - xbar) (xn - xbar), real_inner_comm (xn1 - xbar) (yn - ybar)] using htemp2
    have h_inner_ident : ∀ (u v : H), inner ℝ u v = (1/2 : ℝ) * (‖u‖ ^ 2 + ‖v‖ ^ 2 - ‖u - v‖ ^ 2) := by
      intro u v; have := norm_sub_sq_real u v; linarith
    have h_inner1 : inner ℝ (xn1 - xbar) (xn - xbar) = (1/2 : ℝ) * (‖xn1 - xbar‖ ^ 2 + ‖xn - xbar‖ ^ 2 - ‖xn1 - xn‖ ^ 2) := by
      have : (xn1 - xbar) - (xn - xbar) = xn1 - xn := by abel
      rw [h_inner_ident (xn1 - xbar) (xn - xbar), this]
    have h_inner2 : inner ℝ (xn1 - xbar) (yn - ybar) = (1/2 : ℝ) * (‖xn1 - xbar‖ ^ 2 + ‖yn - ybar‖ ^ 2 - ‖yn - xn1 - ybar + xbar‖ ^ 2) := by
      have hsub : (xn1 - xbar) - (yn - ybar) = xn1 - yn - xbar + ybar := by abel
      rw [h_inner_ident (xn1 - xbar) (yn - ybar), hsub]
      have hnorm_eq : ‖xn1 - yn - xbar + ybar‖ ^ 2 = ‖yn - xn1 - ybar + xbar‖ ^ 2 := by
        rw [show xn1 - yn - xbar + ybar = -(yn - xn1 - ybar + xbar) by abel, norm_neg]
      rw [hnorm_eq]
    rw [h_inner1, h_inner2] at h_firm
    have h_rearr : γ * ‖xn1 - xbar‖ ^ 2 ≤
        (α n * ‖xn - xbar‖ ^ 2 + β * ‖yn - ybar‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - ybar + xbar‖ ^ 2) := by nlinarith
    have h_div : ‖xn1 - xbar‖ ^ 2 ≤
        (α n * ‖xn - xbar‖ ^ 2 + β * ‖yn - ybar‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - ybar + xbar‖ ^ 2) / γ := by
      calc
        ‖xn1 - xbar‖ ^ 2 = (γ * ‖xn1 - xbar‖ ^ 2) / γ := by field_simp [hγpos.ne']
        _ ≤ (α n * ‖xn - xbar‖ ^ 2 + β * ‖yn - ybar‖ ^ 2 - α n * ‖xn1 - xn‖ ^ 2 - β * ‖yn - xn1 - ybar + xbar‖ ^ 2) / γ :=
          (div_le_div_of_nonneg_right h_rearr (by linarith))
    simpa [div_eq_inv_mul, γ, xn1, xn, yn] using h_div

  -- Construct structures for Proposition 4.5.
  have h41toh46 : H41toH46 H f g β μ := {
    f_conv := hf_conv
    g_conv := hg_conv
    f_lsc := hf_lsc
    g_lsc := hg_lsc
    f_bdd_below := hf_bdd_below
    g_bdd_below := hg_bdd_below
    beta_pos := hβ_pos
    mu_pos := hμ_pos
    ine_nonempty := by
      rcases h46 with ⟨⟨x₀', y₀'⟩, hine⟩
      exact ⟨x₀', y₀', hine⟩
  }
  have h47_val : H47 α ν := by
    dsimp [H47, positivePart]
    exact ⟨hα_var_summable, hν_var_summable⟩
  let alg : CA2 H H f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) α (fun _ => β) (fun _ => μ) ν := {
    x := x_seq
    y := y_seq
    step_x := by
      intro n ξ
      have h := h_step_x n ξ
      simpa [norm_sub_rev] using h
    step_y := by
      intro n η
      have h := h_step_y n η
      simpa [norm_sub_rev] using h
  }
  have h_prop45 := proposition_4_5 h41toh46 hα_nonneg hν_nonneg h47_val alg x₀ y₀ hine₀
  rcases h_prop45 with ⟨⟨h_yn_xn_conv, h_xdiff_conv, h_ydiff_conv⟩, ⟨h_xnorm_conv, h_ynorm_conv⟩⟩

  -- Boundedness of α, ν from H47.
  rcases bounded_of_H47_posPart hα_nonneg hα_var_summable with ⟨Cα, hα_bdd⟩
  rcases bounded_of_H47_posPart hν_nonneg hν_var_summable with ⟨Cν, hν_bdd⟩
  have hα_abs_bdd : ∀ n, |α n| ≤ Cα := by
    intro n; rw [abs_of_nonneg (hα_nonneg n)]; exact hα_bdd n
  have hν_abs_bdd : ∀ n, |ν n| ≤ Cν := by
    intro n; rw [abs_of_nonneg (hν_nonneg n)]; exact hν_bdd n

  -- Part (a): componentwise Opial. The product-space route below is kept in a
  -- block comment because `H × H` does not synthesize the Hilbert structure
  -- required by `opial_lemma` in this project.
  set Sx : Set H := {xbar | ∃ ybar : H,
    IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar} with hSx_def
  set Sy : Set H := {ybar | ∃ xbar : H,
    IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar} with hSy_def

  have hSx_nonempty : Sx.Nonempty := by
    exact ⟨x₀, y₀, hine₀⟩
  have hSy_nonempty : Sy.Nonempty := by
    exact ⟨y₀, x₀, hine₀⟩

  have hSx_dist : ∀ z ∈ Sx, ∃ l : ℝ,
      Tendsto (fun n : ℕ => ‖x_seq n - z‖) atTop (𝓝 l) := by
    intro z hz
    rw [hSx_def] at hz
    rcases hz with ⟨yz, hz_ine⟩
    have h45z := proposition_4_5 h41toh46 hα_nonneg hν_nonneg h47_val alg z yz hz_ine
    rcases h45z with ⟨⟨_, _, _⟩, ⟨hxnorm_z, _⟩⟩
    rcases hxnorm_z with ⟨lx, _hxlx⟩
    exact ⟨lx, tendsto_of_tendsto_nat_succ _hxlx⟩

  have hSy_dist : ∀ z ∈ Sy, ∃ l : ℝ,
      Tendsto (fun n : ℕ => ‖y_seq n - z‖) atTop (𝓝 l) := by
    intro z hz
    rw [hSy_def] at hz
    rcases hz with ⟨xz, hz_ine⟩
    have h45z := proposition_4_5 h41toh46 hα_nonneg hν_nonneg h47_val alg xz z hz_ine
    rcases h45z with ⟨⟨_, _, _⟩, ⟨_, hynorm_z⟩⟩
    rcases hynorm_z with ⟨ly, _hyly⟩
    exact ⟨ly, tendsto_of_tendsto_nat_succ _hyly⟩

  have hSx_cluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n : ℕ => toWeakSpace ℝ H (x_seq n)) (toWeakSpace ℝ H z) →
          z ∈ Sx := by
    intro z hz_cluster
    rw [hSx_def]
    rcases hz_cluster.exists_subseq_tendsto with ⟨φ, hφ_mono, hxφ_weak_raw⟩
    have hxφ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (x_seq (φ k))) atTop
          (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [Function.comp] using hxφ_weak_raw
    rcases h_ynorm_conv with ⟨ly₀, hy_succ_dist⟩
    have hy_range_bdd : Bornology.IsBounded (Set.range y_seq) :=
      bounded_range_of_succ_distance_tendsto hy_succ_dist
    have hyφ_range_bdd : Bornology.IsBounded (Set.range (fun k : ℕ => y_seq (φ k))) := by
      rcases isBounded_iff_forall_norm_le.mp hy_range_bdd with ⟨M, hM⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨M, ?_⟩
      rintro w ⟨k, rfl⟩
      exact hM _ ⟨φ k, rfl⟩
    rcases bounded_sequence_has_weakly_convergent_subsequence (fun k : ℕ => y_seq (φ k))
        hyφ_range_bdd with ⟨ytilde, ψ, hψ_mono, hyφψ_weak⟩
    let χ : ℕ → ℕ := φ ∘ ψ
    have hχ_mono : StrictMono χ := hφ_mono.comp hψ_mono
    have hxχ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (x_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [χ, Function.comp] using hxφ_weak.comp hψ_mono.tendsto_atTop
    have hyχ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H ytilde)) := by
      simpa [χ, Function.comp] using hyφψ_weak
    have hxχ_succ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (x_seq (χ k + 1))) atTop
          (𝓝 (toWeakSpace ℝ H z)) :=
      weak_subseq_succ_of_step_tendsto_zero hχ_mono hxχ_weak h_xdiff_conv
    have hyχ_succ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k + 1))) atTop
          (𝓝 (toWeakSpace ℝ H ytilde)) :=
      weak_subseq_succ_of_step_tendsto_zero hχ_mono hyχ_weak h_ydiff_conv
    have hdiffχ_strong :
        Tendsto (fun k : ℕ => y_seq (χ k) - x_seq (χ k)) atTop (𝓝 (y₀ - x₀)) :=
      h_yn_xn_conv.comp hχ_mono.tendsto_atTop
    have hdiffχ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k) - x_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H (ytilde - z))) := by
      simpa using hyχ_weak.sub hxχ_weak
    have hdiffχ_strong_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k) - x_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H (y₀ - x₀))) := by
      have := ((toWeakSpaceCLM ℝ H).continuous.tendsto (y₀ - x₀)).comp hdiffχ_strong
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using this
    have hdiffχ_eq : y₀ - x₀ = ytilde - z := by
      have hweak : toWeakSpace ℝ H (y₀ - x₀) = toWeakSpace ℝ H (ytilde - z) :=
        tendsto_nhds_unique hdiffχ_strong_weak hdiffχ_weak
      exact (toWeakSpace ℝ H).injective hweak
    -- The remaining step is the demiclosedness argument for the two coordinate
    -- subdifferentials along `χ`, producing `IsINE ... z ytilde`.
    exact ⟨ytilde, by
      have hxstepχ : Tendsto (fun k : ℕ => x_seq (χ k + 1) - x_seq (χ k))
          atTop (𝓝 (0 : H)) := h_xdiff_conv.comp hχ_mono.tendsto_atTop
      have hxstepχ_neg : Tendsto (fun k : ℕ => x_seq (χ k) - x_seq (χ k + 1))
          atTop (𝓝 (0 : H)) := by
        simpa [sub_eq_add_neg] using hxstepχ.neg
      have hystepχ : Tendsto (fun k : ℕ => y_seq (χ k + 1) - y_seq (χ k))
          atTop (𝓝 (0 : H)) := h_ydiff_conv.comp hχ_mono.tendsto_atTop
      have hystepχ_neg : Tendsto (fun k : ℕ => y_seq (χ k) - y_seq (χ k + 1))
          atTop (𝓝 (0 : H)) := by
        simpa [sub_eq_add_neg] using hystepχ.neg
      let cx : ℕ → H := fun k =>
        (α (χ k)) • (x_seq (χ k) - x_seq (χ k + 1)) +
          β • (y_seq (χ k) - x_seq (χ k + 1))
      have hcx_sub : ∀ k w,
          f w ≥ f (x_seq (χ k + 1)) + inner ℝ (cx k) (w - x_seq (χ k + 1)) := by
        intro k w
        dsimp [cx]
        simpa [hx_def, hy_def] using subgrad_of_min_quadratic hf_conv (h_x_min (χ k)) w
      have hcx_tendsto : Tendsto cx atTop (𝓝 (β • (ytilde - z))) := by
        have hterm1 : Tendsto
            (fun k : ℕ => (α (χ k)) • (x_seq (χ k) - x_seq (χ k + 1)))
            atTop (𝓝 (0 : H)) :=
          tendsto_smul_of_abs_bounded_of_tendsto_zero (fun k => hα_abs_bdd (χ k))
            hxstepχ_neg
        have hyx_succ : Tendsto (fun k : ℕ => y_seq (χ k) - x_seq (χ k + 1))
            atTop (𝓝 (ytilde - z)) := by
          have hsum := hdiffχ_strong.add hxstepχ_neg
          have hfun :
              (fun k : ℕ => (y_seq (χ k) - x_seq (χ k)) +
                (x_seq (χ k) - x_seq (χ k + 1))) =
              (fun k : ℕ => y_seq (χ k) - x_seq (χ k + 1)) := by
            ext k; abel
          simpa [hfun, hdiffχ_eq] using hsum
        have hterm2 : Tendsto
            (fun k : ℕ => β • (y_seq (χ k) - x_seq (χ k + 1)))
            atTop (𝓝 (β • (ytilde - z))) := hyx_succ.const_smul β
        simpa [cx] using hterm1.add hterm2
      have hf_lim : ∀ w, f w ≥ f z + inner ℝ (β • (ytilde - z)) (w - z) :=
        subdifferential_demiclosed_real_valued hf_conv hf_lsc hxχ_succ_weak
          hcx_tendsto hcx_sub
      have hine_f : ∀ ξ,
          f z + (β / 2) * ‖z - ytilde‖ ^ 2 ≤
            f ξ + (β / 2) * ‖ξ - ytilde‖ ^ 2 :=
        subgrad_to_ine_f hβ_pos hf_lim
      let cy : ℕ → H := fun k =>
        μ • (x_seq (χ k + 1) - y_seq (χ k + 1)) +
          (ν (χ k)) • (y_seq (χ k) - y_seq (χ k + 1))
      have hcy_sub : ∀ k w,
          g w ≥ g (y_seq (χ k + 1)) + inner ℝ (cy k) (w - y_seq (χ k + 1)) := by
        intro k w
        have hymin_k : ∀ η : H,
            g (y_seq (χ k + 1)) +
                (μ / 2) * ‖x_seq (χ k + 1) - y_seq (χ k + 1)‖ ^ 2 +
                ((ν (χ k)) / 2) * ‖y_seq (χ k + 1) - y_seq (χ k)‖ ^ 2 ≤
              g η + (μ / 2) * ‖x_seq (χ k + 1) - η‖ ^ 2 +
                ((ν (χ k)) / 2) * ‖η - y_seq (χ k)‖ ^ 2 := by
          intro η
          have h := h_y_min (χ k) η
          simpa [hx_def, hy_def, norm_sub_rev] using h
        dsimp [cy]
        simpa using subgrad_of_min_quadratic hg_conv hymin_k w
      have hcy_tendsto : Tendsto cy atTop (𝓝 (μ • (z - ytilde))) := by
        have hdiffχ_succ_strong :
            Tendsto (fun k : ℕ => y_seq (χ k + 1) - x_seq (χ k + 1))
              atTop (𝓝 (y₀ - x₀)) :=
          h_yn_xn_conv.comp ((tendsto_add_atTop_nat 1).comp hχ_mono.tendsto_atTop)
        have hxy_succ : Tendsto (fun k : ℕ => x_seq (χ k + 1) - y_seq (χ k + 1))
            atTop (𝓝 (z - ytilde)) := by
          have hlim : x₀ - y₀ = z - ytilde := by
            calc
              x₀ - y₀ = -(y₀ - x₀) := by abel
              _ = -(ytilde - z) := by rw [hdiffχ_eq]
              _ = z - ytilde := by abel
          have hlim' : x₀ + -y₀ = z + -ytilde := by
            simpa [sub_eq_add_neg] using hlim
          simpa [sub_eq_add_neg, hlim'] using hdiffχ_succ_strong.neg
        have hterm1 : Tendsto
            (fun k : ℕ => μ • (x_seq (χ k + 1) - y_seq (χ k + 1)))
            atTop (𝓝 (μ • (z - ytilde))) := hxy_succ.const_smul μ
        have hterm2 : Tendsto
            (fun k : ℕ => (ν (χ k)) • (y_seq (χ k) - y_seq (χ k + 1)))
            atTop (𝓝 (0 : H)) :=
          tendsto_smul_of_abs_bounded_of_tendsto_zero (fun k => hν_abs_bdd (χ k))
            hystepχ_neg
        simpa [cy] using hterm1.add hterm2
      have hg_lim : ∀ w, g w ≥ g ytilde + inner ℝ (μ • (z - ytilde)) (w - ytilde) :=
        subdifferential_demiclosed_real_valued hg_conv hg_lsc hyχ_succ_weak
          hcy_tendsto hcy_sub
      have hine_g : ∀ η,
          g ytilde + (μ / 2) * ‖z - ytilde‖ ^ 2 ≤
            g η + (μ / 2) * ‖z - η‖ ^ 2 :=
        subgrad_to_ine_g hμ_pos hg_lim
      exact ⟨by
        intro ξ
        have h := hine_f ξ
        simp
        nlinarith
      , by
        intro η
        have h := hine_g η
        simp
        nlinarith⟩⟩

  have hSy_cluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n : ℕ => toWeakSpace ℝ H (y_seq n)) (toWeakSpace ℝ H z) →
          z ∈ Sy := by
    intro z hz_cluster
    rw [hSy_def]
    rcases hz_cluster.exists_subseq_tendsto with ⟨φ, hφ_mono, hyφ_weak_raw⟩
    have hyφ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (φ k))) atTop
          (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [Function.comp] using hyφ_weak_raw
    rcases h_xnorm_conv with ⟨lx₀, hx_succ_dist⟩
    have hx_range_bdd : Bornology.IsBounded (Set.range x_seq) :=
      bounded_range_of_succ_distance_tendsto hx_succ_dist
    have hxφ_range_bdd : Bornology.IsBounded (Set.range (fun k : ℕ => x_seq (φ k))) := by
      rcases isBounded_iff_forall_norm_le.mp hx_range_bdd with ⟨M, hM⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨M, ?_⟩
      rintro w ⟨k, rfl⟩
      exact hM _ ⟨φ k, rfl⟩
    rcases bounded_sequence_has_weakly_convergent_subsequence (fun k : ℕ => x_seq (φ k))
        hxφ_range_bdd with ⟨xtilde, ψ, hψ_mono, hxφψ_weak⟩
    let χ : ℕ → ℕ := φ ∘ ψ
    have hχ_mono : StrictMono χ := hφ_mono.comp hψ_mono
    have hyχ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H z)) := by
      simpa [χ, Function.comp] using hyφ_weak.comp hψ_mono.tendsto_atTop
    have hxχ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (x_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H xtilde)) := by
      simpa [χ, Function.comp] using hxφψ_weak
    have hyχ_succ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k + 1))) atTop
          (𝓝 (toWeakSpace ℝ H z)) :=
      weak_subseq_succ_of_step_tendsto_zero hχ_mono hyχ_weak h_ydiff_conv
    have hxχ_succ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (x_seq (χ k + 1))) atTop
          (𝓝 (toWeakSpace ℝ H xtilde)) :=
      weak_subseq_succ_of_step_tendsto_zero hχ_mono hxχ_weak h_xdiff_conv
    have hdiffχ_strong :
        Tendsto (fun k : ℕ => y_seq (χ k) - x_seq (χ k)) atTop (𝓝 (y₀ - x₀)) :=
      h_yn_xn_conv.comp hχ_mono.tendsto_atTop
    have hdiffχ_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k) - x_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H (z - xtilde))) := by
      simpa using hyχ_weak.sub hxχ_weak
    have hdiffχ_strong_weak :
        Tendsto (fun k : ℕ => toWeakSpace ℝ H (y_seq (χ k) - x_seq (χ k))) atTop
          (𝓝 (toWeakSpace ℝ H (y₀ - x₀))) := by
      have := ((toWeakSpaceCLM ℝ H).continuous.tendsto (y₀ - x₀)).comp hdiffχ_strong
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using this
    have hdiffχ_eq : y₀ - x₀ = z - xtilde := by
      have hweak : toWeakSpace ℝ H (y₀ - x₀) = toWeakSpace ℝ H (z - xtilde) :=
        tendsto_nhds_unique hdiffχ_strong_weak hdiffχ_weak
      exact (toWeakSpace ℝ H).injective hweak
    -- Symmetric demiclosedness along `χ` should produce `IsINE ... xtilde z`.
    exact ⟨xtilde, by
      have hxstepχ : Tendsto (fun k : ℕ => x_seq (χ k + 1) - x_seq (χ k))
          atTop (𝓝 (0 : H)) := h_xdiff_conv.comp hχ_mono.tendsto_atTop
      have hxstepχ_neg : Tendsto (fun k : ℕ => x_seq (χ k) - x_seq (χ k + 1))
          atTop (𝓝 (0 : H)) := by
        simpa [sub_eq_add_neg] using hxstepχ.neg
      have hystepχ : Tendsto (fun k : ℕ => y_seq (χ k + 1) - y_seq (χ k))
          atTop (𝓝 (0 : H)) := h_ydiff_conv.comp hχ_mono.tendsto_atTop
      have hystepχ_neg : Tendsto (fun k : ℕ => y_seq (χ k) - y_seq (χ k + 1))
          atTop (𝓝 (0 : H)) := by
        simpa [sub_eq_add_neg] using hystepχ.neg
      let cx : ℕ → H := fun k =>
        (α (χ k)) • (x_seq (χ k) - x_seq (χ k + 1)) +
          β • (y_seq (χ k) - x_seq (χ k + 1))
      have hcx_sub : ∀ k w,
          f w ≥ f (x_seq (χ k + 1)) + inner ℝ (cx k) (w - x_seq (χ k + 1)) := by
        intro k w
        dsimp [cx]
        simpa [hx_def, hy_def] using subgrad_of_min_quadratic hf_conv (h_x_min (χ k)) w
      have hcx_tendsto : Tendsto cx atTop (𝓝 (β • (z - xtilde))) := by
        have hterm1 : Tendsto
            (fun k : ℕ => (α (χ k)) • (x_seq (χ k) - x_seq (χ k + 1)))
            atTop (𝓝 (0 : H)) :=
          tendsto_smul_of_abs_bounded_of_tendsto_zero (fun k => hα_abs_bdd (χ k))
            hxstepχ_neg
        have hyx_succ : Tendsto (fun k : ℕ => y_seq (χ k) - x_seq (χ k + 1))
            atTop (𝓝 (z - xtilde)) := by
          have hsum := hdiffχ_strong.add hxstepχ_neg
          have hfun :
              (fun k : ℕ => (y_seq (χ k) - x_seq (χ k)) +
                (x_seq (χ k) - x_seq (χ k + 1))) =
              (fun k : ℕ => y_seq (χ k) - x_seq (χ k + 1)) := by
            ext k; abel
          simpa [hfun, hdiffχ_eq] using hsum
        have hterm2 : Tendsto
            (fun k : ℕ => β • (y_seq (χ k) - x_seq (χ k + 1)))
            atTop (𝓝 (β • (z - xtilde))) := hyx_succ.const_smul β
        simpa [cx] using hterm1.add hterm2
      have hf_lim : ∀ w, f w ≥ f xtilde + inner ℝ (β • (z - xtilde)) (w - xtilde) :=
        subdifferential_demiclosed_real_valued hf_conv hf_lsc hxχ_succ_weak
          hcx_tendsto hcx_sub
      have hine_f : ∀ ξ,
          f xtilde + (β / 2) * ‖xtilde - z‖ ^ 2 ≤
            f ξ + (β / 2) * ‖ξ - z‖ ^ 2 :=
        subgrad_to_ine_f hβ_pos hf_lim
      let cy : ℕ → H := fun k =>
        μ • (x_seq (χ k + 1) - y_seq (χ k + 1)) +
          (ν (χ k)) • (y_seq (χ k) - y_seq (χ k + 1))
      have hcy_sub : ∀ k w,
          g w ≥ g (y_seq (χ k + 1)) + inner ℝ (cy k) (w - y_seq (χ k + 1)) := by
        intro k w
        have hymin_k : ∀ η : H,
            g (y_seq (χ k + 1)) +
                (μ / 2) * ‖x_seq (χ k + 1) - y_seq (χ k + 1)‖ ^ 2 +
                ((ν (χ k)) / 2) * ‖y_seq (χ k + 1) - y_seq (χ k)‖ ^ 2 ≤
              g η + (μ / 2) * ‖x_seq (χ k + 1) - η‖ ^ 2 +
                ((ν (χ k)) / 2) * ‖η - y_seq (χ k)‖ ^ 2 := by
          intro η
          have h := h_y_min (χ k) η
          simpa [hx_def, hy_def, norm_sub_rev] using h
        dsimp [cy]
        simpa using subgrad_of_min_quadratic hg_conv hymin_k w
      have hcy_tendsto : Tendsto cy atTop (𝓝 (μ • (xtilde - z))) := by
        have hdiffχ_succ_strong :
            Tendsto (fun k : ℕ => y_seq (χ k + 1) - x_seq (χ k + 1))
              atTop (𝓝 (y₀ - x₀)) :=
          h_yn_xn_conv.comp ((tendsto_add_atTop_nat 1).comp hχ_mono.tendsto_atTop)
        have hxy_succ : Tendsto (fun k : ℕ => x_seq (χ k + 1) - y_seq (χ k + 1))
            atTop (𝓝 (xtilde - z)) := by
          have hlim : x₀ - y₀ = xtilde - z := by
            calc
              x₀ - y₀ = -(y₀ - x₀) := by abel
              _ = -(z - xtilde) := by rw [hdiffχ_eq]
              _ = xtilde - z := by abel
          have hlim' : x₀ + -y₀ = xtilde + -z := by
            simpa [sub_eq_add_neg] using hlim
          simpa [sub_eq_add_neg, hlim'] using hdiffχ_succ_strong.neg
        have hterm1 : Tendsto
            (fun k : ℕ => μ • (x_seq (χ k + 1) - y_seq (χ k + 1)))
            atTop (𝓝 (μ • (xtilde - z))) := hxy_succ.const_smul μ
        have hterm2 : Tendsto
            (fun k : ℕ => (ν (χ k)) • (y_seq (χ k) - y_seq (χ k + 1)))
            atTop (𝓝 (0 : H)) :=
          tendsto_smul_of_abs_bounded_of_tendsto_zero (fun k => hν_abs_bdd (χ k))
            hystepχ_neg
        simpa [cy] using hterm1.add hterm2
      have hg_lim : ∀ w, g w ≥ g z + inner ℝ (μ • (xtilde - z)) (w - z) :=
        subdifferential_demiclosed_real_valued hg_conv hg_lsc hyχ_succ_weak
          hcy_tendsto hcy_sub
      have hine_g : ∀ η,
          g z + (μ / 2) * ‖xtilde - z‖ ^ 2 ≤
            g η + (μ / 2) * ‖xtilde - η‖ ^ 2 :=
        subgrad_to_ine_g hμ_pos hg_lim
      exact ⟨by
        intro ξ
        have h := hine_f ξ
        simp
        nlinarith
      , by
        intro η
        have h := hine_g η
        simp
        nlinarith⟩⟩

  have h_opial_x := opial_lemma hSx_nonempty x_seq hSx_dist hSx_cluster
  rcases h_opial_x with ⟨xbar, hxbarS, h_weak_x⟩
  have h_opial_y := opial_lemma hSy_nonempty y_seq hSy_dist hSy_cluster
  rcases h_opial_y with ⟨ybar, hybarS, h_weak_y⟩

  have hine_xbar_ybar : IsINE f g (fun ξ η => ‖ξ - η‖ ^ 2 / 2) (fun ξ η => ‖ξ - η‖ ^ 2 / 2)
      (fun ξ η => ‖ξ - η‖ ^ 2 / 2) 0 β μ 0 xbar ybar := by
    rw [hSx_def] at hxbarS
    rcases hxbarS with ⟨yx, hine_xyx⟩
    have h_prop45_yx := proposition_4_5 h41toh46 hα_nonneg hν_nonneg h47_val alg xbar yx hine_xyx
    rcases h_prop45_yx with ⟨⟨h_diff_to_yx, _, _⟩, _⟩
    have hdiff_weak :
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (y_seq n - x_seq n)) atTop
          (𝓝 (toWeakSpace ℝ H (ybar - xbar))) := by
      simpa using h_weak_y.sub h_weak_x
    have hdiff_to_yx_weak :
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (y_seq n - x_seq n)) atTop
          (𝓝 (toWeakSpace ℝ H (yx - xbar))) := by
      have := ((toWeakSpaceCLM ℝ H).continuous.tendsto (yx - xbar)).comp h_diff_to_yx
      simpa [toWeakSpaceCLM_eq_toWeakSpace] using this
    have hdiff_eq : yx - xbar = ybar - xbar := by
      have hweak_eq : toWeakSpace ℝ H (yx - xbar) = toWeakSpace ℝ H (ybar - xbar) :=
        tendsto_nhds_unique hdiff_to_yx_weak hdiff_weak
      exact (toWeakSpace ℝ H).injective hweak_eq
    have hyx_eq : yx = ybar := by
      calc
        yx = (yx - xbar) + xbar := by abel
        _ = (ybar - xbar) + xbar := by rw [hdiff_eq]
        _ = ybar := by abel
    simpa [hyx_eq] using hine_xyx

  have h_prop45_xbar := proposition_4_5 h41toh46 hα_nonneg hν_nonneg h47_val alg xbar ybar hine_xbar_ybar
  rcases h_prop45_xbar with ⟨⟨h_yn_xn_conv_final, _, _⟩, ⟨_, _⟩⟩
  have h_strong_diff : Tendsto (fun n => y_seq n - x_seq n) atTop (𝓝 (ybar - xbar)) := h_yn_xn_conv_final

  have h_minimizing : ∀ ξ η : H, L_beta_mu f g β μ xbar ybar ≤ L_beta_mu f g β μ ξ η := by
    exact ine_minimizes_L_beta_mu hf_conv hg_conv hβ_pos hμ_pos hine_xbar_ybar

  have h_xy_diff : Tendsto (fun n : ℕ => x_seq n - y_seq n) atTop (𝓝 (xbar - ybar)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_strong_diff.neg
  have h_quad_term :
      Tendsto (fun n : ℕ => (β * μ / 2) * ‖x_seq n - y_seq n‖ ^ 2) atTop
        (𝓝 ((β * μ / 2) * ‖xbar - ybar‖ ^ 2)) := by
    have h_norm_sq : Tendsto (fun n : ℕ => ‖x_seq n - y_seq n‖ ^ 2) atTop
        (𝓝 (‖xbar - ybar‖ ^ 2)) := h_xy_diff.norm.pow 2
    simpa using
      (tendsto_const_nhds.mul h_norm_sq :
        Tendsto (fun n : ℕ => (β * μ / 2) * ‖x_seq n - y_seq n‖ ^ 2) atTop
          (𝓝 ((β * μ / 2) * ‖xbar - ybar‖ ^ 2)))

  have h_L_val : Tendsto (fun n : ℕ => L_beta_mu f g β μ (x_seq n) (y_seq n)) atTop
      (𝓝 (L_beta_mu f g β μ xbar ybar)) := by
    let uerr : ℕ → H := fun n =>
      μ • (α n • (x_seq (n+1) - x_seq n) + β • (y_seq (n+1) - y_seq n))
    let verr : ℕ → H := fun n =>
      β • (ν n • (y_seq (n+1) - y_seq n))
    have h_alpha_x : Tendsto (fun n : ℕ => α n • (x_seq (n+1) - x_seq n))
        atTop (𝓝 (0 : H)) :=
      by simpa using tendsto_smul_of_abs_bounded_of_tendsto_zero hα_abs_bdd h_xdiff_conv
    have h_beta_y : Tendsto (fun n : ℕ => β • (y_seq (n+1) - y_seq n))
        atTop (𝓝 (0 : H)) := by
      simpa using h_ydiff_conv.const_smul β
    have huerr : Tendsto uerr atTop (𝓝 (0 : H)) := by
      simpa [uerr] using (h_alpha_x.add h_beta_y).const_smul μ
    have h_nu_y : Tendsto (fun n : ℕ => ν n • (y_seq (n+1) - y_seq n))
        atTop (𝓝 (0 : H)) :=
      by simpa using tendsto_smul_of_abs_bounded_of_tendsto_zero hν_abs_bdd h_ydiff_conv
    have hverr : Tendsto verr atTop (𝓝 (0 : H)) := by
      simpa [verr] using h_nu_y.const_smul β
    have hx_succ_weak :
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (x_seq (n+1))) atTop
          (𝓝 (toWeakSpace ℝ H xbar)) :=
      h_weak_x.comp (tendsto_add_atTop_nat 1)
    have hy_succ_weak :
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (y_seq (n+1))) atTop
          (𝓝 (toWeakSpace ℝ H ybar)) :=
      h_weak_y.comp (tendsto_add_atTop_nat 1)
    have hx_target_weak :
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (xbar - x_seq (n+1))) atTop
          (𝓝 (toWeakSpace ℝ H (0 : H))) := by
      simpa [sub_self] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => toWeakSpace ℝ H xbar) atTop
          (𝓝 (toWeakSpace ℝ H xbar))).sub hx_succ_weak)
    have hy_target_weak :
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (ybar - y_seq (n+1))) atTop
          (𝓝 (toWeakSpace ℝ H (0 : H))) := by
      simpa [sub_self] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => toWeakSpace ℝ H ybar) atTop
          (𝓝 (toWeakSpace ℝ H ybar))).sub hy_succ_weak)
    have hx_target_bdd : Bornology.IsBounded
        (Set.range (fun n : ℕ => xbar - x_seq (n+1))) :=
      bounded_range_of_tendsto_weakly hx_target_weak
    have hy_target_bdd : Bornology.IsBounded
        (Set.range (fun n : ℕ => ybar - y_seq (n+1))) :=
      bounded_range_of_tendsto_weakly hy_target_weak
    have hu_inner : Tendsto (fun n : ℕ => inner ℝ (uerr n) (xbar - x_seq (n+1)))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_inner_zero_of_tendsto_zero_of_bounded huerr hx_target_bdd
    have hv_inner : Tendsto (fun n : ℕ => inner ℝ (verr n) (ybar - y_seq (n+1)))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_inner_zero_of_tendsto_zero_of_bounded hverr hy_target_bdd
    have h_lower_succ : ∀ n : ℕ,
        L_beta_mu f g β μ xbar ybar ≤
          L_beta_mu f g β μ (x_seq (n+1)) (y_seq (n+1)) := by
      intro n
      exact h_minimizing (x_seq (n+1)) (y_seq (n+1))
    have h_upper_succ : ∀ ε > 0, ∀ᶠ n in atTop,
        L_beta_mu f g β μ (x_seq (n+1)) (y_seq (n+1)) ≤
          L_beta_mu f g β μ xbar ybar + ε := by
      intro ε hε
      have hε2 : ε / 2 > 0 := by linarith
      have hu_ev : ∀ᶠ n in atTop,
          inner ℝ (uerr n) (xbar - x_seq (n+1)) ≤ ε / 2 := by
        filter_upwards [hu_inner (Metric.ball_mem_nhds 0 hε2)] with n hn
        have habs : |inner ℝ (uerr n) (xbar - x_seq (n+1))| < ε / 2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] using hn
        rw [abs_lt] at habs
        linarith
      have hv_ev : ∀ᶠ n in atTop,
          inner ℝ (verr n) (ybar - y_seq (n+1)) ≤ ε / 2 := by
        filter_upwards [hv_inner (Metric.ball_mem_nhds 0 hε2)] with n hn
        have habs : |inner ℝ (verr n) (ybar - y_seq (n+1))| < ε / 2 := by
          simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] using hn
        rw [abs_lt] at habs
        linarith
      filter_upwards [hu_ev, hv_ev] with n hu hv
      have hpert := L_beta_mu_perturbation_ineq hf_conv hg_conv hβ_pos hμ_pos
        h_x_min h_y_min n xbar ybar
      have hpert' :
          L_beta_mu f g β μ (x_seq (n+1)) (y_seq (n+1)) ≤
            L_beta_mu f g β μ xbar ybar +
              inner ℝ (uerr n) (xbar - x_seq (n+1)) +
              inner ℝ (verr n) (ybar - y_seq (n+1)) := by
        simpa [hx_def, hy_def, uerr, verr] using hpert
      linarith
    have hsucc : Tendsto
        (fun n : ℕ => L_beta_mu f g β μ (x_seq (n+1)) (y_seq (n+1))) atTop
        (𝓝 (L_beta_mu f g β μ xbar ybar)) :=
      tendsto_of_lower_bound_and_eventual_upper h_lower_succ h_upper_succ
    exact tendsto_of_tendsto_nat_succ hsucc

  have h_weighted :
      Tendsto (fun n : ℕ => μ * f (x_seq n) + β * g (y_seq n)) atTop
        (𝓝 (μ * f xbar + β * g ybar)) := by
    have hdiff := h_L_val.sub h_quad_term
    simpa [L_beta_mu, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff
  have hf_lsc_events : ∀ ε > 0, ∀ᶠ n in atTop, f (x_seq n) ≥ f xbar - ε := by
    intro ε hε
    exact weakly_seq_lsc_of_convex_lsc hf_conv hf_lsc x_seq xbar h_weak_x ε hε
  have hg_lsc_events : ∀ ε > 0, ∀ᶠ n in atTop, g (y_seq n) ≥ g ybar - ε := by
    intro ε hε
    exact weakly_seq_lsc_of_convex_lsc hg_conv hg_lsc y_seq ybar h_weak_y ε hε

  have h_f_val : Tendsto (fun n => f (x_seq n)) atTop (𝓝 (f xbar)) := by
    exact first_value_tendsto_of_weighted_sum_and_lsc hμ_pos hβ_pos h_weighted
      hf_lsc_events hg_lsc_events
  have h_g_val : Tendsto (fun n => g (y_seq n)) atTop (𝓝 (g ybar)) := by
    have h_weighted_swap :
        Tendsto (fun n : ℕ => β * g (y_seq n) + μ * f (x_seq n)) atTop
          (𝓝 (β * g ybar + μ * f xbar)) := by
      simpa [add_comm] using h_weighted
    exact first_value_tendsto_of_weighted_sum_and_lsc hβ_pos hμ_pos h_weighted_swap
      hg_lsc_events hf_lsc_events

  exact ⟨xbar, ybar, h_weak_x, h_weak_y, hine_xbar_ybar, h_minimizing, h_L_val, h_strong_diff, h_f_val, h_g_val⟩
