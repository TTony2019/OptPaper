import Mathlib
import Foundation.Hilbert.WeakConvergence
import Foundation.Convex.WeakClosed

/-!
# Demiclosedness of Subdifferential (Brézis)

Let f : H → ℝ ∪ {+∞} be a convex, proper, lower semicontinuous function on a Hilbert space H.
Then the subdifferential operator ∂f : H ⇉ H is demiclosed (weakly-strongly closed):
if x_n ⇀ x weakly in H and ∂f(x_n) ∋ u_n → u strongly in H, then ∂f(x) ∋ u.

Source: H. Brézis, Opérateurs Maximaux Monotones et Semi-groupes de Contractions
dans les Espaces de Hilbert, North-Holland Math. Stud. 5, 1973.
-/

open Set
open Filter
open scoped Topology
open scoped InnerProductSpace

/- EXTERNAL DEPENDENCY: Demiclosedness of Subdifferential (Brézis)
   Source: H. Brézis, Opérateurs Maximaux Monotones, North-Holland Math. Stud. 5, 1973.
   Status: resolved — proof blueprint available from external_refs.json.
   The proof uses maximal monotonicity of ∂f for convex lsc proper f on Hilbert space.
-/

/-- The subdifferential of a convex function f on a Hilbert space H as a set-valued map.
For x ∈ H, ∂f(x) = {u ∈ H | ∀ y ∈ H, f(y) ≥ f(x) + ⟨u, y - x⟩}. -/
def subdifferential {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (x : H) : Set H :=
  {u : H | ∀ y : H, f y ≥ f x + inner ℝ u (y - x)}

private lemma weakly_seq_lsc_of_convex_lsc {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hf_lsc : LowerSemicontinuous f) (xn : ℕ → H) (x : H)
    (h_weak : Tendsto (fun n => toWeakSpace ℝ H (xn n)) atTop
      (𝓝 (toWeakSpace ℝ H x))) :
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
  have h_subseq_weak :
      Tendsto (fun k => toWeakSpace ℝ H (xn (ψ k))) atTop
        (𝓝 (toWeakSpace ℝ H x)) :=
    h_weak.comp (StrictMono.tendsto_atTop hψ_mono)
  set C : Set H := {z | f z ≤ f x - ε} with hC_def
  have hC_closed : IsClosed C := by
    have h_open : IsOpen (f ⁻¹' Set.Ioi (f x - ε)) := hf_lsc.isOpen_preimage (f x - ε)
    have hC_eq : C = (f ⁻¹' Set.Ioi (f x - ε))ᶜ := by
      ext z
      simp [hC_def]
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
    intro k
    rw [hC_def]
    exact (hψ_val k).le
  have hx_mem_C : x ∈ C :=
    mem_of_tendsto_weakly_of_isClosed_convex hC_closed hC_convex h_mem h_subseq_weak
  rw [hC_def] at hx_mem_C
  change f x ≤ f x - ε at hx_mem_C
  linarith

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

/-- Demiclosedness of the subdifferential (Brézis).
If f is convex, proper, and lower semicontinuous on a real Hilbert space H, and
x_n ⇀ x weakly, ∂f(x_n) ∋ u_n → u strongly, then ∂f(x) ∋ u. -/
theorem subdifferential_demiclosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hf_conv : ConvexOn ℝ (Set.univ : Set H) f)
    (hf_lsc : LowerSemicontinuous f)
    (x_seq : ℕ → H) (u_seq : ℕ → H) (x u : H)
    (hx_weak : Tendsto (fun n : ℕ => toWeakSpace ℝ H (x_seq n)) atTop (𝓝 (toWeakSpace ℝ H x)))
    (hu_strong : Tendsto u_seq atTop (𝓝 u))
    (hu_sub : ∀ n, u_seq n ∈ subdifferential f (x_seq n)) :
    u ∈ subdifferential f x := by
  rw [subdifferential, Set.mem_setOf_eq]
  exact subdifferential_demiclosed_real_valued hf_conv hf_lsc hx_weak hu_strong (by
    intro n z
    have h := hu_sub n
    rw [subdifferential, Set.mem_setOf_eq] at h
    exact h z)
