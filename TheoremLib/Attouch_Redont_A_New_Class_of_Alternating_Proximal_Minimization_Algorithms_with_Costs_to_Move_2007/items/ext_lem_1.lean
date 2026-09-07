import Mathlib
import Foundation.Hilbert.WeakConvergence

/-!
# Opial's Lemma

Let z_n be a sequence in a Hilbert space H such that there exists a nonvoid set S ⊂ H satisfying:
(i) any weak limit point of z_n belongs to S;
(ii) ∀ ζ ∈ S, lim_{n→∞} ‖z_n - ζ‖ exists.

Then z_n weakly converges to some element of S.

Source: Z. Opial, Bull. Amer. Math. Soc. 73 (1967), pp. 591–597.
-/

open Set
open Filter
open scoped Topology
open scoped InnerProductSpace

noncomputable section

/-! ### Helper lemmas -/

/-- Weak convergence in `WeakSpace ℝ H` is equivalent to convergence of inner products
against all test vectors. This uses the Riesz representation theorem. -/
private theorem weakConvergence_iff_forall_tendsto_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {x : ℕ → H} {x₀ : H} :
    Tendsto (fun n : ℕ => toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H x₀)) ↔
      ∀ u : H, Tendsto (fun n : ℕ => inner ℝ (x n) u) atTop (𝓝 (inner ℝ x₀ u)) := by
  have hinj : Function.Injective ((topDualPairing ℝ H).flip) := by
    intro y z hyz
    exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ) (V := H)).2 fun l => DFunLike.congr_fun hyz l
  constructor
  · intro hx u
    have hcont : Continuous fun (w : WeakSpace ℝ H) =>
        inner ℝ ((toWeakSpace ℝ H).symm w) u := by
      have := WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
        (InnerProductSpace.toDual ℝ H u)
      simpa [InnerProductSpace.toDual_apply_apply, real_inner_comm] using this
    simpa using hcont.tendsto (toWeakSpace ℝ H x₀) |>.comp hx
  · intro h
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto
      ((topDualPairing ℝ H).flip) hinj).2 ?_
    intro f
    let u : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f)
    have hu := h u
    have h_app (v : H) : (WeakDual.toStrongDual f) v = inner ℝ v u := by
      calc
        (WeakDual.toStrongDual f) v = (InnerProductSpace.toDual ℝ H u) v := by
          simp [u]
        _ = inner ℝ u v := by rw [InnerProductSpace.toDual_apply_apply]
        _ = inner ℝ v u := by rw [real_inner_comm]
    have h_fn (n : ℕ) : f ((toWeakSpace ℝ H) (x n)) = inner ℝ (x n) u := by
      calc
        f ((toWeakSpace ℝ H) (x n)) = (WeakDual.toStrongDual f) (x n) := rfl
        _ = inner ℝ (x n) u := h_app (x n)
    have h_target : f ((toWeakSpace ℝ H) x₀) = inner ℝ x₀ u := by
      calc
        f ((toWeakSpace ℝ H) x₀) = (WeakDual.toStrongDual f) x₀ := rfl
        _ = inner ℝ x₀ u := h_app x₀
    simpa [h_fn, h_target] using hu

/-- If ‖z n - ζ‖ converges (as ℝ-valued), then the sequence z is norm-bounded. -/
private theorem bounded_range_of_convergent_distance {H : Type*} [NormedAddCommGroup H]
    {z : ℕ → H} {ζ : H} (hconv : ∃ l : ℝ, Tendsto (fun n : ℕ => ‖z n - ζ‖) atTop (𝓝 l)) :
    Bornology.IsBounded (Set.range z) := by
  rcases hconv with ⟨l, hl⟩
  have hbounded_dist : Bornology.IsBounded (Set.range (fun n : ℕ => ‖z n - ζ‖)) :=
    Metric.isBounded_range_of_tendsto _ hl
  rcases isBounded_iff_forall_norm_le.mp hbounded_dist with ⟨R, hR⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R + ‖ζ‖, ?_⟩
  rintro y ⟨n, rfl⟩
  have hz : ‖‖z n - ζ‖‖ ≤ R := hR _ (Set.mem_range_self n)
  -- In ℝ, ‖x‖ = |x|
  have hz' : ‖z n - ζ‖ ≤ R := by simpa [Real.norm_eq_abs] using hz
  calc
    ‖z n‖ = ‖(z n - ζ) + ζ‖ := by abel
    _ ≤ ‖z n - ζ‖ + ‖ζ‖ := norm_add_le _ _
    _ ≤ R + ‖ζ‖ := by gcongr

/-- Polarization identity: convergence of ‖z n - a‖ and ‖z n - b‖ implies convergence
of inner ℝ (z n) (a - b). -/
private theorem inner_tendsto_of_dist_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {z : ℕ → H} {a b : H}
    (ha : ∃ l : ℝ, Tendsto (fun n : ℕ => ‖z n - a‖) atTop (𝓝 l))
    (hb : ∃ l : ℝ, Tendsto (fun n : ℕ => ‖z n - b‖) atTop (𝓝 l)) :
    ∃ l : ℝ, Tendsto (fun n : ℕ => inner ℝ (z n) (a - b)) atTop (𝓝 l) := by
  rcases ha with ⟨la, hla⟩
  rcases hb with ⟨lb, hlb⟩
  refine ⟨(lb ^ 2 - la ^ 2 + ‖a‖ ^ 2 - ‖b‖ ^ 2) / 2, ?_⟩
  have h_two_inner_eq : (fun n : ℕ => (2 : ℝ) * inner ℝ (z n) (a - b)) =
      (fun n : ℕ => ‖z n - b‖ ^ 2 - ‖z n - a‖ ^ 2 + ‖a‖ ^ 2 - ‖b‖ ^ 2) := by
    ext n
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring_nf
  have h_two_inner_tendsto : Tendsto (fun n : ℕ => (2 : ℝ) * inner ℝ (z n) (a - b)) atTop
      (𝓝 (lb ^ 2 - la ^ 2 + ‖a‖ ^ 2 - ‖b‖ ^ 2)) := by
    rw [h_two_inner_eq]
    have h_const : Tendsto (fun _ : ℕ => ‖a‖ ^ 2 - ‖b‖ ^ 2) atTop (𝓝 (‖a‖ ^ 2 - ‖b‖ ^ 2)) :=
      tendsto_const_nhds
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (((hlb.pow 2).sub (hla.pow 2)).add h_const)
  -- Divide by 2: if 2*f(n) → L, then f(n) → L/2
  have h : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) * ((2 : ℝ) * inner ℝ (z n) (a - b))) atTop
      (𝓝 (((2 : ℝ)⁻¹) * (lb ^ 2 - la ^ 2 + ‖a‖ ^ 2 - ‖b‖ ^ 2))) :=
    h_two_inner_tendsto.const_mul ((2 : ℝ)⁻¹)
  -- Simplify the expression
  have h_simp (n : ℕ) : ((2 : ℝ)⁻¹) * ((2 : ℝ) * inner ℝ (z n) (a - b)) =
      inner ℝ (z n) (a - b) := by ring
  have h_limit_simp : ((2 : ℝ)⁻¹) * (lb ^ 2 - la ^ 2 + ‖a‖ ^ 2 - ‖b‖ ^ 2) =
      (lb ^ 2 - la ^ 2 + ‖a‖ ^ 2 - ‖b‖ ^ 2) / 2 := by ring
  simpa [h_simp, h_limit_simp] using h

/-- If a and b are both weak subsequential limits of z and belong to S, then a = b.
This is the core Opial polarization argument. -/
private theorem weak_subseq_limits_equal {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {S : Set H} {z : ℕ → H}
    (h_dist : ∀ ζ ∈ S, ∃ l : ℝ, Tendsto (fun n : ℕ => ‖z n - ζ‖) atTop (𝓝 l))
    {a b : H} (haS : a ∈ S) (hbS : b ∈ S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hφ_tendsto : Tendsto (fun k : ℕ => toWeakSpace ℝ H (z (φ k))) atTop (𝓝 (toWeakSpace ℝ H a)))
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (hψ_tendsto : Tendsto (fun k : ℕ => toWeakSpace ℝ H (z (ψ k))) atTop (𝓝 (toWeakSpace ℝ H b))) :
    a = b := by
  -- Get inner product convergence from distance convergence via polarization
  rcases inner_tendsto_of_dist_convergence (h_dist a haS) (h_dist b hbS) with ⟨l, hl⟩
  -- Under weak convergence, inner products against a fixed vector converge
  have h_inner (w : H) (k : ℕ → ℕ) (hk_tendsto : Tendsto (fun n : ℕ =>
      toWeakSpace ℝ H (z (k n))) atTop (𝓝 (toWeakSpace ℝ H w))) :
      Tendsto (fun n : ℕ => inner ℝ (z (k n)) (a - b)) atTop (𝓝 (inner ℝ w (a - b))) := by
    have h_iff := weakConvergence_iff_forall_tendsto_inner (x := fun n => z (k n)) (x₀ := w)
    have h_conv := (h_iff.mp hk_tendsto) (a - b)
    simpa using h_conv
  -- Along φ: inner → inner ℝ a (a - b)
  have hφ_inner := h_inner a φ hφ_tendsto
  -- Along ψ: inner → inner ℝ b (a - b)
  have hψ_inner := h_inner b ψ hψ_tendsto
  -- Both subsequence limits of ⟨z_n, a-b⟩ must equal the full sequence limit l
  have ha_eq : inner ℝ a (a - b) = l := tendsto_nhds_unique hφ_inner (hl.comp hφ.tendsto_atTop)
  have hb_eq : inner ℝ b (a - b) = l := tendsto_nhds_unique hψ_inner (hl.comp hψ.tendsto_atTop)
  -- Hence inner ℝ (a - b) (a - b) = 0, so a = b
  have hzero_sq : ‖a - b‖ ^ 2 = 0 := by
    calc
      ‖a - b‖ ^ 2 = inner ℝ (a - b) (a - b) := by rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ a (a - b) - inner ℝ b (a - b) := by rw [inner_sub_left]
      _ = l - l := by rw [ha_eq, hb_eq]
      _ = 0 := by ring
  have hzero : ‖a - b‖ = 0 := by
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Every bounded sequence in a Hilbert space has a weakly convergent subsequence.
This is the Eberlein-Smulian / Banach-Alaoglu theorem for Hilbert spaces. -/
private theorem exists_weakly_convergent_subseq_of_bounded {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {z : ℕ → H}
    (_hz_bounded : Bornology.IsBounded (Set.range z)) :
    ∃ (w : H) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ n))) atTop (𝓝 (toWeakSpace ℝ H w)) :=
  bounded_sequence_has_weakly_convergent_subsequence z _hz_bounded

/-- Given `ns : ℕ → ℕ` with `Tendsto ns atTop atTop`, there exists a strictly monotone
subsequence extraction `ms` such that `ns ∘ ms` is strictly monotone. -/
private lemma exists_strictMono_subseq_of_tendsto_atTop {ns : ℕ → ℕ}
    (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ StrictMono (ns ∘ ms) := by
  -- At each step k, we can find m > k with ns m > ns k because ns → ∞
  have h_exists_next : ∀ k, ∃ m, m > k ∧ ns m > ns k := by
    intro k
    have h_event_ns : ∀ᶠ n in atTop, ns k < ns n :=
      hns (eventually_gt_atTop (ns k))
    have h_event_gt : ∀ᶠ n in atTop, k < n := eventually_gt_atTop k
    rcases (h_event_ns.and h_event_gt).exists with ⟨m, hm_ns, hm_gt⟩
    exact ⟨m, hm_gt, hm_ns⟩
  -- Build ms by recursion: ms 0 = 0, ms (k+1) = some m > ms k with ns m > ns (ms k)
  let ms : ℕ → ℕ := Nat.rec 0 (fun k m_k => Classical.choose (h_exists_next m_k))
  have hms_succ_gt : ∀ k, ms k < ms (k + 1) := by
    intro k
    dsimp [ms]
    exact (Classical.choose_spec (h_exists_next (ms k))).1
  have hns_succ_gt : ∀ k, ns (ms k) < ns (ms (k + 1)) := by
    intro k
    dsimp [ms]
    exact (Classical.choose_spec (h_exists_next (ms k))).2
  have hms_strictMono : StrictMono ms :=
    strictMono_nat_of_lt_succ hms_succ_gt
  have hns_ms_strictMono : StrictMono (ns ∘ ms) := by
    refine strictMono_nat_of_lt_succ (fun k => ?_)
    simpa [Function.comp] using hns_succ_gt k
  exact ⟨ms, hms_strictMono, hns_ms_strictMono⟩

end

namespace ItemExtLem1

/-- Opial's lemma: In a Hilbert space, if every weak subsequential limit of z_n lies in a
nonempty set S, and distance to each point of S converges, then z_n converges weakly
to some point of S. -/
theorem opial_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {S : Set H} (hS_nonempty : S.Nonempty) (z : ℕ → H)
    (h_cluster : ∀ (w : H) (φ : ℕ → ℕ), StrictMono φ →
      (Tendsto (fun k : ℕ => toWeakSpace ℝ H (z (φ k))) atTop (𝓝 (toWeakSpace ℝ H w))) → w ∈ S)
    (h_dist : ∀ ζ ∈ S, ∃ l : ℝ, Tendsto (fun n : ℕ => ‖z n - ζ‖) atTop (𝓝 l)) :
    ∃ zstar ∈ S, Tendsto (fun n : ℕ => toWeakSpace ℝ H (z n)) atTop (𝓝 (toWeakSpace ℝ H zstar)) := by
  rcases hS_nonempty with ⟨ζ₀, hζ₀⟩
  -- Step 1: z is bounded
  have hz_bounded : Bornology.IsBounded (Set.range z) :=
    bounded_range_of_convergent_distance (h_dist ζ₀ hζ₀)
  -- Step 2: Every strictly monotone subsequence has a weakly convergent sub-subsequence
  have h_weak_subseq : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ (w : H) (ψ : ℕ → ℕ), StrictMono ψ ∧
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ (ψ n)))) atTop
          (𝓝 (toWeakSpace ℝ H w)) := by
    intro φ hφ
    have hzφ_bounded : Bornology.IsBounded (Set.range (z ∘ φ)) := by
      apply Bornology.IsBounded.subset hz_bounded
      rintro y ⟨n, rfl⟩
      exact Set.mem_range_self (φ n)
    rcases exists_weakly_convergent_subseq_of_bounded hzφ_bounded with ⟨w, ψ, hψ, h_tendsto⟩
    refine ⟨w, ψ, hψ, ?_⟩
    simpa [Function.comp] using h_tendsto
  -- Step 3: All weak subsequential limits are unique (Opial's polarization argument)
  have h_unique_limit : ∀ (w₁ w₂ : H) (φ₁ φ₂ : ℕ → ℕ),
      StrictMono φ₁ → StrictMono φ₂ →
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ₁ n))) atTop (𝓝 (toWeakSpace ℝ H w₁)) →
      Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ₂ n))) atTop (𝓝 (toWeakSpace ℝ H w₂)) →
      w₁ = w₂ := by
    intro w₁ w₂ φ₁ φ₂ hφ₁ hφ₂ h_tendsto₁ h_tendsto₂
    have hw₁S : w₁ ∈ S := h_cluster w₁ φ₁ hφ₁ h_tendsto₁
    have hw₂S : w₂ ∈ S := h_cluster w₂ φ₂ hφ₂ h_tendsto₂
    exact weak_subseq_limits_equal h_dist hw₁S hw₂S φ₁ hφ₁ h_tendsto₁ φ₂ hφ₂ h_tendsto₂
  -- Step 4: Get one weak cluster point
  rcases exists_weakly_convergent_subseq_of_bounded hz_bounded with ⟨a, φ₀, hφ₀, h_tendsto₀⟩
  have haS : a ∈ S := h_cluster a φ₀ hφ₀ h_tendsto₀
  -- Step 5: Every strictly monotone subsequence has a sub-subsequence converging to a
  have h_all_to_a : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        Tendsto (fun n : ℕ => toWeakSpace ℝ H (z (φ (ψ n)))) atTop
          (𝓝 (toWeakSpace ℝ H a)) := by
    intro φ hφ
    rcases h_weak_subseq φ hφ with ⟨w, ψ, hψ, h_tendsto⟩
    have hw_eq_a : w = a := h_unique_limit w a (φ ∘ ψ) φ₀
      (hφ.comp hψ) hφ₀ h_tendsto h_tendsto₀
    subst hw_eq_a
    exact ⟨ψ, hψ, h_tendsto⟩
  -- Step 6: Use `tendsto_of_subseq_tendsto` to conclude full sequence converges
  refine ⟨a, haS, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns_tendsto
  -- hns_tendsto : Tendsto ns atTop atTop
  -- Extract strictly monotone subsequence from ns
  rcases exists_strictMono_subseq_of_tendsto_atTop hns_tendsto with ⟨ms, hms_mono, hns_ms_mono⟩
  -- hns_ms_mono : StrictMono (ns ∘ ms)
  -- Now apply h_all_to_a to the strictly monotone subsequence ns ∘ ms
  rcases h_all_to_a (ns ∘ ms) hns_ms_mono with ⟨ψ, hψ, h_tendstoψ⟩
  -- h_tendstoψ : Tendsto (fun n => toWeakSpace ℝ H (z ((ns ∘ ms) (ψ n)))) atTop (𝓝 (toWeakSpace ℝ H a))
  -- This is: Tendsto (fun n => toWeakSpace ℝ H (z (ns (ms (ψ n))))) atTop (𝓝 (toWeakSpace ℝ H a))
  -- tendsto_of_subseq_tendsto expects: ∃ ms', Tendsto (fun n => x (ns (ms' n))) atTop f
  -- where x = fun n => toWeakSpace ℝ H (z n)
  -- So we need to produce ms' : ℕ → ℕ such that
  -- Tendsto (fun n => toWeakSpace ℝ H (z (ns (ms' n)))) atTop (𝓝 (toWeakSpace ℝ H a))
  -- Take ms' := ms ∘ ψ, then:
  -- z (ns ((ms ∘ ψ) n)) = z ((ns ∘ ms) (ψ n))
  -- This converges to a by h_tendstoψ
  refine ⟨ms ∘ ψ, ?_⟩
  -- `z (ns ((ms ∘ ψ) n)) = z ((ns ∘ ms) (ψ n))` by associativity
  have h_eq : (fun n : ℕ => toWeakSpace ℝ H (z (ns ((ms ∘ ψ) n)))) =
      (fun n : ℕ => toWeakSpace ℝ H (z ((ns ∘ ms) (ψ n)))) := by
    ext n
    simp [Function.comp]
  simpa [h_eq] using h_tendstoψ

end ItemExtLem1
