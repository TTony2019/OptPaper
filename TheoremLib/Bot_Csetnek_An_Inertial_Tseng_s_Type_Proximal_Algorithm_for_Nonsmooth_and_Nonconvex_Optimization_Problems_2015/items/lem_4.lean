import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_lem_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_3

open Filter
open scoped Topology BigOperators

namespace BotCsetnek2015

theorem m2_nonneg {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    {nu mu : Real} (hnu : 0 < nu) (hmu : 0 < mu) :
    0 <= A.M2 nu mu := by
  have hLh : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
  have hLu : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
  have hlower : 0 <= A.lambdaLower := le_of_lt A.lambdaLower_pos
  have hupper : 0 <= A.lambdaUpper := le_of_lt A.lambdaUpper_pos
  have halpha : 0 <= A.alpha := A.alpha_nonneg
  unfold AlgorithmData.M2 M2Value
  have hnu_nonneg : 0 <= nu := le_of_lt hnu
  have hmu_nonneg : 0 <= mu := le_of_lt hmu
  have htwo_nu : 0 <= 2 * nu := mul_nonneg (by norm_num) hnu_nonneg
  have htwo_mu : 0 <= 2 * mu := mul_nonneg (by norm_num) hmu_nonneg
  have htwo_lower : 0 <= 2 * A.lambdaLower := mul_nonneg (by norm_num) hlower
  have hbr1 :
      0 <=
        P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
          A.Lgrad_u / (2 * A.lambdaLower) := by
    have h1 : 0 <= P.Lgrad_h ^ 2 / (2 * nu) :=
      div_nonneg (sq_nonneg _) htwo_nu
    have h4 : 0 <= A.Lgrad_u / (2 * A.lambdaLower) :=
      div_nonneg hLu htwo_lower
    nlinarith
  have hbr2 :
      0 <=
        mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu) := by
    have hleft : 0 <= mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 :=
      mul_nonneg (mul_nonneg hmu_nonneg (sq_nonneg _)) (sq_nonneg _)
    have hright : 0 <= (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu) :=
      div_nonneg (sq_nonneg _) htwo_mu
    nlinarith
  exact add_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbr1)
    (mul_nonneg (div_nonneg halpha hlower) hbr2)

private noncomputable def algorithmStepSmoothPart_local {m : Nat} (P : ProblemData m)
    (u : EuclideanSpace m -> Real) (lambda alphaSeq : Nat -> Real)
    (x : Nat -> EuclideanSpace m) (n : Nat) : EuclideanSpace m -> Real :=
  fun y =>
    (1 / lambda n) * bregmanDistance u y (x n) +
      inner Real y (gradient P.h (x n)) +
      (alphaSeq n / lambda n) * inner Real y (x (n - 1) - x n)

private theorem algorithmStepObjective_eq_objectiveSum_smoothPart_local {m : Nat}
    (P : ProblemData m) (u : EuclideanSpace m -> Real)
    (lambda alphaSeq : Nat -> Real) (x : Nat -> EuclideanSpace m) (n : Nat) :
    algorithmStepObjective P u lambda alphaSeq x n =
      objectiveSum P.f (algorithmStepSmoothPart_local P u lambda alphaSeq x n) := by
  rfl

private theorem objectiveSum_effectiveDom_iff_local {m : Nat}
    (f : EuclideanSpace m -> EReal) (phi : EuclideanSpace m -> Real)
    (x : EuclideanSpace m) :
    x ∈ ERealFunction.effectiveDom (objectiveSum f phi) ↔
      x ∈ ERealFunction.effectiveDom f := by
  rw [ERealFunction.mem_effectiveDom_iff_exists_real,
    ERealFunction.mem_effectiveDom_iff_exists_real]
  unfold objectiveSum erealAddReal
  rw [EReal.exists_real_eq_sumWithTopBotAsTop_iff]
  constructor
  · rintro ⟨hfx, _⟩
    exact hfx
  · intro hfx
    exact ⟨hfx, ⟨phi x, rfl⟩⟩

private theorem erealAddReal_ne_bot_local (a : EReal) (r : Real) (ha : a ≠ ⊥) :
    erealAddReal a r ≠ ⊥ := by
  cases a with
  | bot => contradiction
  | coe s =>
      change ((s : EReal) + (r : EReal) ≠ ⊥)
      rw [← EReal.coe_add]
      exact EReal.coe_ne_bot (s + r)
  | top =>
      change ((⊤ : EReal) + (r : EReal) ≠ ⊥)
      simp

private theorem algorithmStep_argmin_effectiveDom_local {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) (n : Nat) (_hn : 1 <= n)
    (hargmin : A.p n ∈ argminSet
      (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n)) :
    A.p n ∈ ERealFunction.effectiveDom
      (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n) := by
  classical
  let phi := algorithmStepSmoothPart_local P A.u A.lambda A.alphaSeq A.x n
  let G := algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n
  rcases P.f_proper.2 with ⟨z, hz_dom⟩
  have hz_f_ne_top : P.f z ≠ ⊤ :=
    lt_top_iff_ne_top.mp ((ERealFunction.mem_dom_iff P.f z).mp hz_dom)
  have hz_f_ne_bot : P.f z ≠ ⊥ := P.f_proper.1 z
  have hz_eff_f : z ∈ ERealFunction.effectiveDom P.f := by
    rw [ERealFunction.mem_effectiveDom_iff]
    exact ⟨hz_f_ne_top, hz_f_ne_bot⟩
  have hz_eff_sum : z ∈ ERealFunction.effectiveDom (objectiveSum P.f phi) :=
    (objectiveSum_effectiveDom_iff_local P.f phi z).2 hz_eff_f
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real (objectiveSum P.f phi) z).mp
      hz_eff_sum with ⟨rz, hrz⟩
  have hG_eq : G = objectiveSum P.f phi := by
    dsimp [G, phi]
    exact algorithmStepObjective_eq_objectiveSum_smoothPart_local P A.u A.lambda A.alphaSeq A.x n
  have hargmin_eq : G (A.p n) = sInf (Set.range G) :=
    (mem_argminSet_iff G (A.p n)).mp hargmin
  have hGpn_le_Gz : G (A.p n) <= G z := by
    rw [hargmin_eq]
    exact sInf_le (s := Set.range G) (Set.mem_range_self z)
  have hGz_real : G z = (rz : EReal) := by
    rw [hG_eq]
    exact hrz
  have hne_top : G (A.p n) ≠ ⊤ := by
    intro htop
    rw [htop, hGz_real] at hGpn_le_Gz
    have hcoe_top : (rz : EReal) = ⊤ := top_le_iff.mp hGpn_le_Gz
    exact EReal.coe_ne_top rz hcoe_top
  have hne_bot : G (A.p n) ≠ ⊥ := by
    rw [hG_eq]
    dsimp [objectiveSum]
    exact erealAddReal_ne_bot_local (P.f (A.p n)) (phi (A.p n)) (P.f_proper.1 (A.p n))
  rw [ERealFunction.mem_effectiveDom_iff]
  exact ⟨hne_top, hne_bot⟩

theorem p_objective_effectiveDom {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {n : Nat} (hn : 1 <= n) :
    A.p n ∈ ERealFunction.effectiveDom P.objective := by
  let phi := algorithmStepSmoothPart_local P A.u A.lambda A.alphaSeq A.x n
  have hp_alg := algorithmStep_argmin_effectiveDom_local A n hn (A.p_argmin n hn)
  have hp_alg' : A.p n ∈ ERealFunction.effectiveDom (objectiveSum P.f phi) := by
    simpa [phi, algorithmStepObjective_eq_objectiveSum_smoothPart_local]
      using hp_alg
  have hp_f : A.p n ∈ ERealFunction.effectiveDom P.f :=
    (objectiveSum_effectiveDom_iff_local P.f phi (A.p n)).1 hp_alg'
  change A.p n ∈ ERealFunction.effectiveDom (objectiveSum P.f P.h)
  exact (objectiveSum_effectiveDom_iff_local P.f P.h (A.p n)).2 hp_f

theorem objectiveWithQuadratic_toReal_eq {m : Nat} {P : ProblemData m}
    {M : Real} {x y : EuclideanSpace m}
    (hx : x ∈ ERealFunction.effectiveDom P.objective) :
    (objectiveWithQuadratic P M x y).toReal =
      (P.objective x).toReal + M * ‖x - y‖ ^ 2 := by
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real P.objective x).mp hx with ⟨r, hr⟩
  unfold objectiveWithQuadratic erealAddReal
  rw [hr]
  let q : Real := ‖x - y‖ ^ 2
  change (((r : EReal) + (M : EReal) * (q : EReal)).toReal = r + M * q)
  have hmul : ((M * q : Real) : EReal) = (M : EReal) * (q : EReal) := EReal.coe_mul M q
  rw [← hmul]
  have hadd : ((r + M * q : Real) : EReal) =
      (r : EReal) + ((M * q : Real) : EReal) :=
    EReal.coe_add r (M * q)
  rw [← hadd]
  exact EReal.toReal_coe (r + M * q)

theorem objectiveWithQuadratic_eq_coe {m : Nat} {P : ProblemData m}
    {M : Real} {x y : EuclideanSpace m}
    (hx : x ∈ ERealFunction.effectiveDom P.objective) :
    objectiveWithQuadratic P M x y =
      (((P.objective x).toReal + M * ‖x - y‖ ^ 2 : Real) : EReal) := by
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real P.objective x).mp hx with ⟨r, hr⟩
  unfold objectiveWithQuadratic erealAddReal
  rw [hr]
  change ((r : EReal) + ((M * ‖x - y‖ ^ 2 : Real) : EReal) =
    ((r + M * ‖x - y‖ ^ 2 : Real) : EReal))
  rw [← EReal.coe_add]

theorem relation14_norm_step {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) :
    ∀ n, 1 <= n ->
      ‖A.x (n + 1) - A.x n‖ <=
        (1 + A.lambda n * P.Lgrad_h) * ‖A.x n - A.p n‖ := by
  intro n hn
  have hlam := A.lambda_bounds n hn
  have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam.1
  have hx_update := A.x_update n hn
  have hx_sub :
      A.x (n + 1) - A.p n =
        A.lambda n • (gradient P.h (A.x n) - gradient P.h (A.p n)) := by
    rw [hx_update]
    abel
  have h13 :
      ‖A.x (n + 1) - A.p n‖ <=
        A.lambda n * P.Lgrad_h * ‖A.x n - A.p n‖ := by
    have hLip := P.h_lipschitz_gradient.2.2 (A.x n) (A.p n)
    calc
      ‖A.x (n + 1) - A.p n‖
          = ‖A.lambda n •
              (gradient P.h (A.x n) - gradient P.h (A.p n))‖ := by
              rw [hx_sub]
      _ = A.lambda n *
            ‖gradient P.h (A.x n) - gradient P.h (A.p n)‖ := by
              rw [norm_smul]
              simp [Real.norm_eq_abs, abs_of_pos hlam_pos]
      _ <= A.lambda n * (P.Lgrad_h * ‖A.x n - A.p n‖) := by
              exact mul_le_mul_of_nonneg_left hLip (le_of_lt hlam_pos)
      _ = A.lambda n * P.Lgrad_h * ‖A.x n - A.p n‖ := by
              ring
  calc
    ‖A.x (n + 1) - A.x n‖
        = ‖(A.x (n + 1) - A.p n) + (A.p n - A.x n)‖ := by
            congr 1
            abel
    _ <= ‖A.x (n + 1) - A.p n‖ + ‖A.p n - A.x n‖ := norm_add_le _ _
    _ <= A.lambda n * P.Lgrad_h * ‖A.x n - A.p n‖ +
          ‖A.x n - A.p n‖ := by
            exact add_le_add h13 (by rw [norm_sub_rev])
    _ = (1 + A.lambda n * P.Lgrad_h) * ‖A.x n - A.p n‖ := by
            ring

theorem summable_of_tail3_summable {f : Nat -> Real}
    (hf : Summable (fun k : Nat => f (k + 3))) : Summable f := by
  exact (summable_nat_add_iff (G := Real) 3).mp hf

theorem tendsto_of_tail2_tendsto {α : Type*} [TopologicalSpace α]
    {u : Nat -> α} {l : α}
    (h : Tendsto (fun k : Nat => u (k + 2)) atTop (nhds l)) :
    Tendsto u atTop (nhds l) := by
  exact (Filter.tendsto_add_atTop_iff_nat 2).mp h

/-- Lemma 3.4: square-summability and convergence of the objective sequence. -/
theorem lemma_3_4_decrease {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hchosen : chosenAsInLemma33 A nu mu)
    (hbounded : ∃ C : Real, ∀ x : EuclideanSpace m, (C : EReal) <= P.objective x) :
    Summable (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) ∧
      Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖ ^ 2) ∧
      ∃ l : EReal,
        Tendsto (fun n : Nat => P.objective (A.p n)) atTop (nhds l) := by
  rcases hchosen with ⟨hnu, hmu, _hstrict, hM2ltM1⟩
  let M1 : Real := A.M1 nu mu
  let M2 : Real := A.M2 nu mu
  let D : Real := M1 - M2
  have hDpos : 0 < D := by
    dsimp [D, M1, M2]
    nlinarith [hM2ltM1]
  have hM2_nonneg : 0 <= M2 := by
    dsimp [M2]
    exact m2_nonneg A hnu hmu
  let a : Nat -> Real := fun k =>
    (objectiveWithQuadratic P M2 (A.p (k + 2)) (A.x (k + 2))).toReal
  let b : Nat -> Real := fun k =>
    D * ‖A.x (k + 3) - A.p (k + 3)‖ ^ 2
  have hb_nonneg : ∀ k, 0 <= b k := by
    intro k
    dsimp [b]
    exact mul_nonneg (le_of_lt hDpos) (sq_nonneg _)
  have h32 :
      ∀ n, 2 <= n ->
        objectiveWithQuadratic P M1 (A.p n) (A.x n) <=
          objectiveWithQuadratic P M2 (A.p (n - 1)) (A.x (n - 1)) := by
    intro n hn
    dsimp [M1, M2]
    exact lemma_3_2_descent A nu mu hnu hmu n hn
  have ha_bddBelow : BddBelow (Set.range a) := by
    rcases hbounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro y ⟨k, rfl⟩
    have hp_eff : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom A (by omega)
    have hobj_coe :
        P.objective (A.p (k + 2)) =
          (((P.objective (A.p (k + 2))).toReal : Real) : EReal) := by
      exact (EReal.coe_toReal
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).1
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).2).symm
    have hobj_lower_real : C <= (P.objective (A.p (k + 2))).toReal := by
      have h := hC (A.p (k + 2))
      rw [hobj_coe] at h
      exact EReal.coe_le_coe_iff.mp h
    have hquad_nonneg : 0 <= M2 * ‖A.p (k + 2) - A.x (k + 2)‖ ^ 2 :=
      mul_nonneg hM2_nonneg (sq_nonneg _)
    dsimp [a]
    rw [objectiveWithQuadratic_toReal_eq hp_eff]
    nlinarith
  have hdesc : ∀ k, a (k + 1) + b k <= a k := by
    intro k
    have hk : 2 <= k + 3 := by omega
    have hd := h32 (k + 3) hk
    have hpred : k + 3 - 1 = k + 2 := by omega
    rw [hpred] at hd
    have hp_eff_new : A.p (k + 3) ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom A (by omega)
    have hp_eff_old : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom A (by omega)
    have hleft_coe :=
      objectiveWithQuadratic_eq_coe (P := P) (M := M1)
        (x := A.p (k + 3)) (y := A.x (k + 3)) hp_eff_new
    have hright_coe :=
      objectiveWithQuadratic_eq_coe (P := P) (M := M2)
        (x := A.p (k + 2)) (y := A.x (k + 2)) hp_eff_old
    rw [hleft_coe, hright_coe] at hd
    have hd_real :
        (P.objective (A.p (k + 3))).toReal +
            M1 * ‖A.p (k + 3) - A.x (k + 3)‖ ^ 2
          <=
          (P.objective (A.p (k + 2))).toReal +
            M2 * ‖A.p (k + 2) - A.x (k + 2)‖ ^ 2 :=
      EReal.coe_le_coe_iff.mp hd
    dsimp [a, b]
    rw [objectiveWithQuadratic_toReal_eq hp_eff_new,
      objectiveWithQuadratic_toReal_eq hp_eff_old]
    rw [norm_sub_rev (A.x (k + 3)) (A.p (k + 3))]
    dsimp [D] at *
    nlinarith [hd_real]
  rcases lemma_2_2_descent_summable a b hb_nonneg ha_bddBelow hdesc with
    ⟨_ha_anti, ⟨la, ha_tendsto⟩, hb_summable⟩
  have htail_xp : Summable (fun k : Nat => ‖A.x (k + 3) - A.p (k + 3)‖ ^ 2) := by
    have hb_div := hb_summable.mul_left D⁻¹
    convert hb_div using 1
    ext k
    dsimp [b]
    field_simp [ne_of_gt hDpos]
  have hxp : Summable (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) :=
    summable_of_tail3_summable htail_xp
  have hinc : Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖ ^ 2) := by
    have hinc_tail :
        Summable (fun k : Nat => ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2) := by
      let Cstep : Real := (1 + A.lambdaUpper * P.Lgrad_h) ^ 2
      have hdom :
          ∀ k : Nat,
            ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2
              <= Cstep * ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2 := by
        intro k
        have hn : 1 <= k + 1 := by omega
        have h14 := relation14_norm_step A (k + 1) hn
        have hlam := A.lambda_bounds (k + 1) hn
        have hLh_nonneg : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
        have hfactor_nonneg :
            0 <= 1 + A.lambda (k + 1) * P.Lgrad_h := by
          have hlam_nonneg : 0 <= A.lambda (k + 1) :=
            le_trans (le_of_lt A.lambdaLower_pos) hlam.1
          nlinarith [mul_nonneg hlam_nonneg hLh_nonneg]
        have hfactor_upper_nonneg :
            0 <= 1 + A.lambdaUpper * P.Lgrad_h := by
          nlinarith [mul_nonneg (le_of_lt A.lambdaUpper_pos) hLh_nonneg]
        have hfactor_le :
            1 + A.lambda (k + 1) * P.Lgrad_h <=
              1 + A.lambdaUpper * P.Lgrad_h := by
          have hmul := mul_le_mul_of_nonneg_right hlam.2 hLh_nonneg
          nlinarith
        have hsquare1 :
            ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2 <=
              ((1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := by
          have hprod_nonneg :
              0 <= (1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖ := by
            nlinarith [h14, norm_nonneg (A.x ((k + 1) + 1) - A.x (k + 1))]
          exact sq_le_sq'
            (le_trans (neg_nonpos.mpr hprod_nonneg)
              (norm_nonneg (A.x ((k + 1) + 1) - A.x (k + 1))))
            h14
        have hsquare2 :
            ((1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 <=
              ((1 + A.lambdaUpper * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := by
          have hmul_le := mul_le_mul_of_nonneg_right hfactor_le
            (norm_nonneg (A.x (k + 1) - A.p (k + 1)))
          have hprod_upper_nonneg :
              0 <= (1 + A.lambdaUpper * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖ :=
            mul_nonneg hfactor_upper_nonneg
              (norm_nonneg (A.x (k + 1) - A.p (k + 1)))
          have hprod_nonneg :
              0 <= (1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖ :=
            mul_nonneg hfactor_nonneg
              (norm_nonneg (A.x (k + 1) - A.p (k + 1)))
          exact sq_le_sq'
            (le_trans (neg_nonpos.mpr hprod_upper_nonneg) hprod_nonneg)
            hmul_le
        calc
          ‖A.x ((k + 1) + 1) - A.x (k + 1)‖ ^ 2
              <= ((1 + A.lambda (k + 1) * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := hsquare1
          _ <= ((1 + A.lambdaUpper * P.Lgrad_h) *
                ‖A.x (k + 1) - A.p (k + 1)‖) ^ 2 := hsquare2
          _ = Cstep * ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2 := by
                dsimp [Cstep]
                ring
      have hmajor :
          Summable (fun k : Nat => Cstep * ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2) := by
        have hxp_tail : Summable (fun k : Nat => ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2) :=
          (summable_nat_add_iff (G := Real) 1).mpr hxp
        exact hxp_tail.mul_left Cstep
      exact Summable.of_nonneg_of_le
        (fun k => sq_nonneg _)
        hdom
        hmajor
    exact (summable_nat_add_iff (G := Real) 1).mp hinc_tail
  have hobj :
      ∃ l : EReal, Tendsto (fun n : Nat => P.objective (A.p n)) atTop (nhds l) := by
    have hxpto0 :
        Tendsto (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) atTop (nhds 0) :=
      hxp.tendsto_atTop_zero
    have hxpto0_tail :
        Tendsto (fun k : Nat => ‖A.x (k + 2) - A.p (k + 2)‖ ^ 2) atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat 2).mpr hxpto0
    have hquad_to0 :
        Tendsto (fun k : Nat => M2 * ‖A.p (k + 2) - A.x (k + 2)‖ ^ 2) atTop (nhds 0) := by
      have htmp :
          Tendsto (fun k : Nat => M2 * ‖A.x (k + 2) - A.p (k + 2)‖ ^ 2) atTop
            (nhds (M2 * 0)) :=
        tendsto_const_nhds.mul hxpto0_tail
      simpa [norm_sub_rev] using htmp
    have hobjReal_tail :
        Tendsto (fun k : Nat => (P.objective (A.p (k + 2))).toReal) atTop (nhds la) := by
      have hsub := ha_tendsto.sub hquad_to0
      have hsub' :
          Tendsto (fun x => a x - M2 * ‖A.p (x + 2) - A.x (x + 2)‖ ^ 2) atTop
            (nhds la) := by
        simpa using hsub
      convert hsub' using 1
      ext k
      have hp_eff : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
        p_objective_effectiveDom A (by omega)
      dsimp [a]
      rw [objectiveWithQuadratic_toReal_eq hp_eff]
      rw [norm_sub_rev (A.p (k + 2)) (A.x (k + 2))]
      ring
    have hobjEReal_tail :
        Tendsto (fun k : Nat => P.objective (A.p (k + 2))) atTop (nhds (la : EReal)) := by
      have hcoe :
          Tendsto (fun k : Nat => ((P.objective (A.p (k + 2))).toReal : EReal))
            atTop (nhds (la : EReal)) :=
        EReal.tendsto_coe.2 hobjReal_tail
      convert hcoe using 1
      ext k
      have hp_eff : A.p (k + 2) ∈ ERealFunction.effectiveDom P.objective :=
        p_objective_effectiveDom A (by omega)
      exact (EReal.coe_toReal
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).1
        ((ERealFunction.mem_effectiveDom_iff P.objective (A.p (k + 2))).mp hp_eff).2).symm
    exact ⟨(la : EReal), tendsto_of_tail2_tendsto hobjEReal_tail⟩
  exact ⟨hxp, hinc, hobj⟩

end BotCsetnek2015
