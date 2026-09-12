import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_3
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_1
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_2
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_thm_1
import TheoremLib.Attouch_Inertial_Proximal_Method_2000.items.ext_thm_2

/-!
# Proposition 2.1
Assume that $A: H \Rightarrow H$ and $B: H \Rightarrow H$ are maximal monotone operators
satisfying respectively $\operatorname{dom} A = H$ and $\operatorname{dom} B \neq \emptyset$.
Given $x_0, x_1 \in H$ and a sequence $(\lambda_n)$ of positive numbers, the sequence
$(x_n)$ is uniquely defined by the algorithm $(\mathcal{A})$ and the initial data $x_0, x_1$.
-/
open SetValuedOperator
open scoped Pointwise
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem maximalMonotone_affine_precomp
    (B : SetValuedOperator H H) (hB : IsMaximalMonotone B) (lam : ℝ) (hlam : 0 < lam)
    (c : H) : IsMaximalMonotone (fun x : H => B (lam • x + c)) := by
  constructor
  · intro x y u hu v hv
    have hmono := hB.1 (x := lam • x + c) (y := lam • y + c) u hu v hv
    have hscale : inner ℝ (u - v) (lam • x + c - (lam • y + c)) =
        lam * inner ℝ (u - v) (x - y) := by
      rw [show lam • x + c - (lam • y + c) = lam • (x - y) by module]
      rw [real_inner_smul_right]
    rw [hscale] at hmono
    nlinarith
  · intro C hC hsubset xu hxu
    let B' : SetValuedOperator H H := fun z => C (lam⁻¹ • (z - c))
    have hB'_mono : IsMonotone B' := by
      intro x y u hu v hv
      dsimp [B'] at hu hv
      have hCmono := hC u hu v hv
      have hscale : inner ℝ (u - v) (lam⁻¹ • (x - c) - lam⁻¹ • (y - c)) =
          lam⁻¹ * inner ℝ (u - v) (x - y) := by
        rw [show lam⁻¹ • (x - c) - lam⁻¹ • (y - c) = lam⁻¹ • (x - y) by module]
        rw [real_inner_smul_right]
      rw [hscale] at hCmono
      have hlinv : 0 < lam⁻¹ := inv_pos.mpr hlam
      nlinarith
    have hB_subset_B' : B.graph ⊆ B'.graph := by
      intro xu hxu
      rcases xu with ⟨z, u⟩
      rw [SetValuedOperator.mem_graph_iff] at hxu ⊢
      dsimp [B']
      have hx : lam • (lam⁻¹ • (z - c)) + c = z := by
        calc
          lam • (lam⁻¹ • (z - c)) + c = (lam * lam⁻¹) • (z - c) + c := by
            rw [smul_smul]
          _ = z - c + c := by rw [mul_inv_cancel₀ (ne_of_gt hlam)]; simp
          _ = z := sub_add_cancel z c
      have hg : (lam⁻¹ • (z - c), u) ∈ C.graph := hsubset (by
        rw [SetValuedOperator.mem_graph_iff]
        simpa [hx] using hxu)
      simpa [SetValuedOperator.mem_graph_iff] using hg
    have hB'_subset_B : B'.graph ⊆ B.graph := hB.2 B' hB'_mono hB_subset_B'
    rcases xu with ⟨x, u⟩
    rw [SetValuedOperator.mem_graph_iff] at hxu ⊢
    have hx : lam⁻¹ • (lam • x + c - c) = x := by
      calc
        lam⁻¹ • (lam • x + c - c) = lam⁻¹ • (lam • x) := by
          rw [add_sub_cancel_right]
        _ = (lam⁻¹ * lam) • x := by rw [smul_smul]
        _ = x := by rw [inv_mul_cancel₀ (ne_of_gt hlam)]; simp
    have hg : (lam • x + c, u) ∈ B.graph := hB'_subset_B (by
      rw [SetValuedOperator.mem_graph_iff]
      dsimp [B']
      rw [hx]
      exact hxu)
    simpa [SetValuedOperator.mem_graph_iff] using hg

private def VelocityStep (A B : SetValuedOperator H H) (lam : ℝ) (y z v : H) : Prop :=
  (0 : H) ∈ ({lam⁻¹ • (v - lam⁻¹ • (z - y))} : Set H) + A v + B (lam • v + z)

private theorem velocityStep_exists_unique (A B : SetValuedOperator H H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B) (hdomA : A.dom = Set.univ)
    (hdomB : B.dom.Nonempty) (lam : ℝ) (hlam : 0 < lam) (y z : H) :
    ∃! v : H, VelocityStep A B lam y z v := by
  let Baff : SetValuedOperator H H := fun v => B (lam • v + z)
  let C : SetValuedOperator H H := A + Baff
  have hBaff : IsMaximalMonotone Baff := maximalMonotone_affine_precomp B hB lam hlam z
  have hdom : (interior A.dom ∩ Baff.dom).Nonempty := by
    rcases hdomB with ⟨b, hb⟩
    refine ⟨lam⁻¹ • (b - z), ?_, ?_⟩
    · rw [hdomA]
      simp
    · rw [SetValuedOperator.mem_dom_iff]
      dsimp [Baff]
      have hx : lam • (lam⁻¹ • (b - z)) + z = b := by
        calc
          lam • (lam⁻¹ • (b - z)) + z = (lam * lam⁻¹) • (b - z) + z := by
            rw [smul_smul]
          _ = b - z + z := by rw [mul_inv_cancel₀ (ne_of_gt hlam)]; simp
          _ = b := sub_add_cancel b z
      simpa [hx] using hb
  have hC : IsMaximalMonotone C := sum_maximal_monotone A Baff hA hBaff hdom
  let u : H := lam⁻¹ • (z - y)
  rcases minty_resolvent_existence (A := C) hC u hlam with ⟨v, hv, hvuniq⟩
  refine ⟨v, ?_, ?_⟩
  · rcases hv with ⟨q, hq, hu⟩
    dsimp [C, Baff] at hq
    rw [Set.mem_add] at hq
    rcases hq with ⟨a, ha, b, hb, hqeq⟩
    rw [VelocityStep]
    rw [Set.mem_add]
    refine ⟨lam⁻¹ • (v - u) + a, ?_, b, hb, ?_⟩
    · rw [Set.mem_add]
      refine ⟨lam⁻¹ • (v - u), by simp [u], a, ha, rfl⟩
    · rw [← hqeq] at hu
      have hcalc : lam⁻¹ • (v - u) + (a + b) = 0 := by
        calc
          lam⁻¹ • (v - u) + (a + b) =
              lam⁻¹ • (v - (v + lam • (a + b))) + (a + b) := by rw [hu]
          _ = lam⁻¹ • (-(lam • (a + b))) + (a + b) := by
            rw [show v - (v + lam • (a + b)) = -(lam • (a + b)) by module]
          _ = -(lam⁻¹ • (lam • (a + b))) + (a + b) := by rw [smul_neg]
          _ = -((lam⁻¹ * lam) • (a + b)) + (a + b) := by rw [smul_smul]
          _ = 0 := by simp [inv_mul_cancel₀ (ne_of_gt hlam)]
      simpa [add_assoc] using hcalc
  · intro v' hv'
    apply hvuniq
    rw [VelocityStep] at hv'
    rw [Set.mem_add] at hv'
    rcases hv' with ⟨sa, hsa, b, hb, hzero⟩
    rw [Set.mem_add] at hsa
    rcases hsa with ⟨s, hs, a, ha, hsaeq⟩
    rw [Set.mem_singleton_iff] at hs
    subst s
    refine ⟨a + b, ?_, ?_⟩
    · dsimp [C, Baff]
      rw [Set.mem_add]
      exact ⟨a, ha, b, hb, rfl⟩
    · rw [← hsaeq] at hzero
      have hzero' : lam⁻¹ • (v' - u) + (a + b) = 0 := by
        simpa [u, add_assoc] using hzero
      have hab : a + b = -(lam⁻¹ • (v' - u)) := by
        calc
          a + b = (lam⁻¹ • (v' - u) + (a + b)) - lam⁻¹ • (v' - u) := by
            module
          _ = 0 - lam⁻¹ • (v' - u) := by rw [hzero']
          _ = -(lam⁻¹ • (v' - u)) := by simp
      calc
        u = v' + lam • (a + b) := by
          rw [hab]
          rw [smul_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam)]
          module

omit [CompleteSpace H] in
private theorem velocityStep_to_algorithmStep (A B : SetValuedOperator H H)
    {lam : ℝ} (hlam : 0 < lam) {y z v w : H} (hw : w = z + lam • v)
    (hv : VelocityStep A B lam y z v) :
    (0 : H) ∈ ({(lam ^ 2)⁻¹ • (w - 2 • z + y)} : Set H) +
      A (lam⁻¹ • (w - z)) + B w := by
  subst w
  have hAarg : lam⁻¹ • (lam • v) = v := by
    calc
      lam⁻¹ • (lam • v) = (lam⁻¹ * lam) • v := by rw [smul_smul]
      _ = v := by rw [inv_mul_cancel₀ (ne_of_gt hlam)]; simp
  have hvarg : lam⁻¹ • (z + lam • v - z) = v := by
    calc
      lam⁻¹ • (z + lam • v - z) = lam⁻¹ • (lam • v) := by rw [add_sub_cancel_left]
      _ = v := hAarg
  have hBarg : lam • v + z = z + lam • v := by abel
  have hinertial : (lam ^ 2)⁻¹ • (z + lam • v - 2 • z + y) =
      lam⁻¹ • (v - lam⁻¹ • (z - y)) := by
    have hsq : (lam ^ 2)⁻¹ * lam = lam⁻¹ := by
      field_simp [pow_two, ne_of_gt hlam]
    have hsqinv : (lam ^ 2)⁻¹ = lam⁻¹ * lam⁻¹ := by
      field_simp [pow_two, ne_of_gt hlam]
    calc
      (lam ^ 2)⁻¹ • (z + lam • v - 2 • z + y)
          = (lam ^ 2)⁻¹ • (lam • v - (z - y)) := by
              congr 1
              module
      _ = (lam ^ 2)⁻¹ • (lam • v) - (lam ^ 2)⁻¹ • (z - y) := by rw [smul_sub]
      _ = ((lam ^ 2)⁻¹ * lam) • v - (lam ^ 2)⁻¹ • (z - y) := by
        rw [smul_smul]
      _ = lam⁻¹ • v - (lam⁻¹ * lam⁻¹) • (z - y) := by rw [hsq, hsqinv]
      _ = lam⁻¹ • (v - lam⁻¹ • (z - y)) := by module
  simpa [VelocityStep, hvarg, hAarg, hBarg, hinertial] using hv

omit [CompleteSpace H] in
private theorem algorithmStep_to_velocityStep (A B : SetValuedOperator H H)
    {lam : ℝ} (hlam : 0 < lam) {y z w : H}
    (hstep : (0 : H) ∈ ({(lam ^ 2)⁻¹ • (w - 2 • z + y)} : Set H) +
      A (lam⁻¹ • (w - z)) + B w) :
    VelocityStep A B lam y z (lam⁻¹ • (w - z)) := by
  have hBarg : lam • (lam⁻¹ • (w - z)) + z = w := by
    calc
      lam • (lam⁻¹ • (w - z)) + z = (lam * lam⁻¹) • (w - z) + z := by
        rw [smul_smul]
      _ = w - z + z := by rw [mul_inv_cancel₀ (ne_of_gt hlam)]; simp
      _ = w := sub_add_cancel w z
  have hinertial : lam⁻¹ • (lam⁻¹ • (w - z) - lam⁻¹ • (z - y)) =
      (lam ^ 2)⁻¹ • (w - 2 • z + y) := by
    have hsqinv : (lam ^ 2)⁻¹ = lam⁻¹ * lam⁻¹ := by
      field_simp [pow_two, ne_of_gt hlam]
    calc
      lam⁻¹ • (lam⁻¹ • (w - z) - lam⁻¹ • (z - y))
          = lam⁻¹ • (lam⁻¹ • ((w - z) - (z - y))) := by
              congr 1
              rw [← smul_sub]
      _ = (lam⁻¹ * lam⁻¹) • ((w - z) - (z - y)) := by rw [smul_smul]
      _ = (lam ^ 2)⁻¹ • (w - 2 • z + y) := by
          rw [← hsqinv]
          congr 1
          module
  simpa [VelocityStep, hBarg, hinertial] using hstep

/-- Proposition 2.1: the sequence generated by Algorithm A is uniquely determined by
the initial data. -/
theorem prop_2_1 (A B : SetValuedOperator H H) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hdomA : A.dom = Set.univ) (hdomB : B.dom.Nonempty) (x0 x1 : H) (lam : ℕ → ℝ)
    (hlam : ∀ n, lam n > 0) : ∃! x : ℕ → H, x 0 = x0 ∧ x 1 = x1 ∧ AlgorithmA A B x lam := by
  classical
  let stepEU := fun (n : ℕ) (y z : H) =>
    velocityStep_exists_unique A B hA hB hdomA hdomB (lam n) (hlam n) y z
  let nextV : ℕ → H → H → H := fun n y z => Classical.choose (stepEU n y z)
  let next : ℕ → H → H → H := fun n y z => z + lam n • nextV n y z
  let state : ℕ → H × H := fun n =>
    Nat.rec (x0, x1) (fun n p => (p.2, next n p.1 p.2)) n
  let x : ℕ → H := fun n => (state n).1
  have hx0 : x 0 = x0 := by simp [x, state]
  have hx1 : x 1 = x1 := by simp [x, state]
  have hstate_succ (k : ℕ) :
      state (k + 1) = ((state k).2, next k (state k).1 (state k).2) := by
    simp [state]
  have hx_next (n : ℕ) : x (n + 2) = next n (x n) (x (n + 1)) := by
    change (state (n + 2)).1 = next n (state n).1 (state (n + 1)).1
    rw [hstate_succ (n + 1), hstate_succ n]
  refine ⟨x, ?_, ?_⟩
  · refine ⟨hx0, hx1, ?_⟩
    refine ⟨hlam, ?_⟩
    intro n
    have hv : VelocityStep A B (lam n) (x n) (x (n + 1)) (nextV n (x n) (x (n + 1))) :=
      (Classical.choose_spec (stepEU n (x n) (x (n + 1)))).1
    exact velocityStep_to_algorithmStep A B (hlam n) (hx_next n) hv
  · intro y hy
    rcases hy with ⟨hy0, hy1, hyalg⟩
    funext m
    have hy_eq : ∀ n, y n = x n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        cases n with
        | zero => simpa [hx0] using hy0
        | succ n =>
          cases n with
          | zero => simpa [hx1] using hy1
          | succ n =>
            have hyn : y n = x n := ih n (by omega)
            have hyn1 : y (n + 1) = x (n + 1) := ih (n + 1) (by omega)
            let vy : H := (lam n)⁻¹ • (y (n + 2) - y (n + 1))
            have hyvel : VelocityStep A B (lam n) (y n) (y (n + 1)) vy := by
              dsimp [vy]
              exact algorithmStep_to_velocityStep A B (hlam n) (hyalg.step n)
            have hyvelx : VelocityStep A B (lam n) (x n) (x (n + 1)) vy := by
              simpa [hyn, hyn1] using hyvel
            have hvuniq :=
              (Classical.choose_spec (stepEU n (x n) (x (n + 1)))).2 vy hyvelx
            have hrecon : y (n + 1) + lam n • vy = y (n + 2) := by
              dsimp [vy]
              calc
                y (n + 1) + lam n • ((lam n)⁻¹ • (y (n + 2) - y (n + 1)))
                    = y (n + 1) +
                        (lam n * (lam n)⁻¹) • (y (n + 2) - y (n + 1)) := by
                      rw [smul_smul]
                _ = y (n + 1) + (y (n + 2) - y (n + 1)) := by
                  rw [mul_inv_cancel₀ (ne_of_gt (hlam n))]
                  simp
                _ = y (n + 2) := by abel
            calc
              y (n + 2) = y (n + 1) + lam n • vy := hrecon.symm
              _ = x (n + 1) + lam n • nextV n (x n) (x (n + 1)) := by
                rw [hyn1, hvuniq]
              _ = x (n + 2) := by rw [hx_next n]
    exact hy_eq m
