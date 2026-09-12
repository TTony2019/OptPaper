import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.algo_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_lem_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_thm_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_4
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_5
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_6
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_7

open Filter
open scoped Topology BigOperators

namespace BotCsetnek2015

set_option maxHeartbeats 800000

theorem summable_norm_of_summable_norm_sq_nonneg {u : Nat -> Real}
    (hu_nonneg : ∀ n, 0 <= u n)
    (hsq : Summable (fun n : Nat => u n ^ 2))
    (hcompare : ∀ n, u n <= u n ^ 2) :
    Summable u := by
  exact Summable.of_nonneg_of_le hu_nonneg hcompare hsq

theorem cluster_limit_self_mem {m : Nat}
    (u : Nat -> EuclideanSpace m)
    {x : EuclideanSpace m} (hx : Tendsto u atTop (nhds x)) :
    x ∈ omega u := by
  refine ⟨fun n => n, strictMono_id, ?_⟩
  simpa using hx

theorem tendsto_of_summable_successive_norm {m : Nat}
    (u : Nat -> EuclideanSpace m)
    (h : Summable (fun n : Nat => ‖u (n + 1) - u n‖)) :
    ∃ x : EuclideanSpace m, Tendsto u atTop (nhds x) := by
  let d : Nat -> EuclideanSpace m := fun n => u (n + 1) - u n
  have hd : Summable d := by
    rw [← summable_norm_iff]
    simpa [d] using h
  refine ⟨u 0 + tsum d, ?_⟩
  have hsum :
      Tendsto (fun n : Nat => Finset.sum (Finset.range n) d) atTop (nhds (tsum d)) :=
    hd.hasSum.tendsto_sum_nat
  have hid : ∀ n : Nat, u n = u 0 + Finset.sum (Finset.range n) d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          u (n + 1) = u n + d n := by simp [d]
          _ = u 0 + Finset.sum (Finset.range n) d + d n := by rw [ih]
          _ = u 0 + Finset.sum (Finset.range (n + 1)) d := by
              simp [Finset.sum_range_succ, add_assoc]
  have hconst : Tendsto (fun _ : Nat => u 0) atTop (nhds (u 0)) := tendsto_const_nhds
  have hlim :
      Tendsto (fun n : Nat => u 0 + Finset.sum (Finset.range n) d) atTop
        (nhds (u 0 + tsum d)) :=
    hconst.add hsum
  have hfun : u = fun n : Nat => u 0 + Finset.sum (Finset.range n) d := funext hid
  rw [hfun]
  simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hlim

theorem p_tendsto_of_x_tendsto_xp_summable {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {x : EuclideanSpace m}
    (hx : Tendsto A.x atTop (nhds x))
    (hxp : Summable (fun n : Nat => ‖A.x n - A.p n‖)) :
    Tendsto A.p atTop (nhds x) := by
  have hnorm0 :
      Tendsto (fun n : Nat => ‖A.x n - A.p n‖) atTop (nhds 0) :=
    hxp.tendsto_atTop_zero
  have hdiff :
      Tendsto (fun n : Nat => A.x n - A.p n) atTop
        (nhds (0 : EuclideanSpace m)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm0
  have hsub :
      Tendsto (fun n : Nat => A.x n - (A.x n - A.p n)) atTop (nhds (x - 0)) :=
    hx.sub hdiff
  have hfun :
      (fun n : Nat => A.p n) =
        fun n : Nat => A.x n - (A.x n - A.p n) := by
    funext n
    abel
  change Tendsto (fun n : Nat => A.p n) atTop (nhds x)
  rw [hfun]
  simpa using hsub

private noncomputable def algorithmStepSmoothPart_thm {m : Nat} (P : ProblemData m)
    (u : EuclideanSpace m -> Real) (lambda alphaSeq : Nat -> Real)
    (x : Nat -> EuclideanSpace m) (n : Nat) : EuclideanSpace m -> Real :=
  fun y =>
    (1 / lambda n) * bregmanDistance u y (x n) +
      inner Real y (gradient P.h (x n)) +
      (alphaSeq n / lambda n) * inner Real y (x (n - 1) - x n)

private theorem algorithmStepObjective_eq_objectiveSum_smoothPart_thm {m : Nat}
    (P : ProblemData m) (u : EuclideanSpace m -> Real)
    (lambda alphaSeq : Nat -> Real) (x : Nat -> EuclideanSpace m) (n : Nat) :
    algorithmStepObjective P u lambda alphaSeq x n =
      objectiveSum P.f (algorithmStepSmoothPart_thm P u lambda alphaSeq x n) := by
  rfl

private theorem objectiveSum_effectiveDom_iff_thm {m : Nat}
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

private theorem erealAddReal_ne_bot_thm (a : EReal) (r : Real) (ha : a ≠ ⊥) :
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

private theorem algorithmStep_argmin_effectiveDom_thm {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) (n : Nat) (_hn : 1 <= n)
    (hargmin : A.p n ∈ argminSet
      (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n)) :
    A.p n ∈ ERealFunction.effectiveDom
      (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n) := by
  classical
  let phi := algorithmStepSmoothPart_thm P A.u A.lambda A.alphaSeq A.x n
  let G := algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n
  rcases P.f_proper.2 with ⟨z, hz_dom⟩
  have hz_f_ne_top : P.f z ≠ ⊤ :=
    lt_top_iff_ne_top.mp ((ERealFunction.mem_dom_iff P.f z).mp hz_dom)
  have hz_f_ne_bot : P.f z ≠ ⊥ := P.f_proper.1 z
  have hz_eff_f : z ∈ ERealFunction.effectiveDom P.f := by
    rw [ERealFunction.mem_effectiveDom_iff]
    exact ⟨hz_f_ne_top, hz_f_ne_bot⟩
  have hz_eff_sum : z ∈ ERealFunction.effectiveDom (objectiveSum P.f phi) :=
    (objectiveSum_effectiveDom_iff_thm P.f phi z).2 hz_eff_f
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real (objectiveSum P.f phi) z).mp
      hz_eff_sum with ⟨rz, hrz⟩
  have hG_eq : G = objectiveSum P.f phi := by
    dsimp [G, phi]
    exact algorithmStepObjective_eq_objectiveSum_smoothPart_thm P A.u A.lambda A.alphaSeq A.x n
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
    exact erealAddReal_ne_bot_thm (P.f (A.p n)) (phi (A.p n)) (P.f_proper.1 (A.p n))
  rw [ERealFunction.mem_effectiveDom_iff]
  exact ⟨hne_top, hne_bot⟩

private theorem p_objective_effectiveDom_thm {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {n : Nat} (hn : 1 <= n) :
    A.p n ∈ ERealFunction.effectiveDom P.objective := by
  let phi := algorithmStepSmoothPart_thm P A.u A.lambda A.alphaSeq A.x n
  have hp_alg := algorithmStep_argmin_effectiveDom_thm A n hn (A.p_argmin n hn)
  have hp_alg' : A.p n ∈ ERealFunction.effectiveDom (objectiveSum P.f phi) := by
    simpa [phi, algorithmStepObjective_eq_objectiveSum_smoothPart_thm]
      using hp_alg
  have hp_f : A.p n ∈ ERealFunction.effectiveDom P.f :=
    (objectiveSum_effectiveDom_iff_thm P.f phi (A.p n)).1 hp_alg'
  change A.p n ∈ ERealFunction.effectiveDom (objectiveSum P.f P.h)
  exact (objectiveSum_effectiveDom_iff_thm P.f P.h (A.p n)).2 hp_f

private theorem objectiveWithQuadratic_toReal_eq_thm {m : Nat} {P : ProblemData m}
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

private theorem objectiveWithQuadratic_eq_coe_thm {m : Nat} {P : ProblemData m}
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

theorem lyapunov_descent_real {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : Real) (hnu : 0 < nu) (hmu : 0 < mu) :
    ∀ n, 1 <= n ->
      let M1 := A.M1 nu mu
      let M2 := A.M2 nu mu
      let D := M1 - M2
      D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 <=
        (HFunction P M2 (pairSequence A n)).toReal -
          (HFunction P M2 (pairSequence A (n + 1))).toReal := by
  intro n hn
  let M1 : Real := A.M1 nu mu
  let M2 : Real := A.M2 nu mu
  let D : Real := M1 - M2
  have hn2 : 2 <= n + 1 := by omega
  have hd :
      objectiveWithQuadratic P M1 (A.p (n + 1)) (A.x (n + 1)) <=
        objectiveWithQuadratic P M2 (A.p n) (A.x n) := by
    dsimp [M1, M2]
    simpa using lemma_3_2_descent A nu mu hnu hmu (n + 1) hn2
  have hp_new : A.p (n + 1) ∈ ERealFunction.effectiveDom P.objective :=
    p_objective_effectiveDom_thm A (by omega)
  have hp_old : A.p n ∈ ERealFunction.effectiveDom P.objective :=
    p_objective_effectiveDom_thm A hn
  have hleft_coe :=
    objectiveWithQuadratic_eq_coe_thm (P := P) (M := M1)
      (x := A.p (n + 1)) (y := A.x (n + 1)) hp_new
  have hright_coe :=
    objectiveWithQuadratic_eq_coe_thm (P := P) (M := M2)
      (x := A.p n) (y := A.x n) hp_old
  rw [hleft_coe, hright_coe] at hd
  have hd_real :
      (P.objective (A.p (n + 1))).toReal +
          M1 * ‖A.p (n + 1) - A.x (n + 1)‖ ^ 2
        <=
        (P.objective (A.p n)).toReal +
          M2 * ‖A.p n - A.x n‖ ^ 2 :=
    EReal.coe_le_coe_iff.mp hd
  dsimp [HFunction, pairSequence]
  rw [objectiveWithQuadratic_toReal_eq_thm (P := P) (M := M2)
      (x := A.p n) (y := A.x n) hp_old,
    objectiveWithQuadratic_toReal_eq_thm (P := P) (M := M2)
      (x := A.p (n + 1)) (y := A.x (n + 1)) hp_new]
  rw [norm_sub_rev (A.x (n + 1)) (A.p (n + 1))]
  dsimp [D, M1, M2] at *
  nlinarith [hd_real]

private theorem relation14_norm_step_thm {m : Nat} {P : ProblemData m}
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

theorem x_increment_summable_of_xp_summable {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P)
    (hxp : Summable (fun n : Nat => ‖A.x n - A.p n‖)) :
    Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖) := by
  let g : Nat -> Real := fun n => ‖A.x (n + 1) - A.x n‖
  let e : Nat -> Real := fun n => ‖A.x n - A.p n‖
  change Summable g
  refine (_root_.summable_nat_add_iff (f := g) 1).mp ?_
  have he : Summable e := by simpa [e] using hxp
  have hxp_tail : Summable (fun n : Nat => e (n + 1)) :=
    (_root_.summable_nat_add_iff (f := e) 1).mpr he
  let C : Real := 1 + A.lambdaUpper * P.Lgrad_h
  have hC_nonneg : 0 <= C := by
    have hL : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
    have hu : 0 < A.lambdaUpper := A.lambdaUpper_pos
    dsimp [C]
    positivity
  have hscaled : Summable (fun n : Nat => C * e (n + 1)) := hxp_tail.mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hscaled
  intro n
  change ‖A.x ((n + 1) + 1) - A.x (n + 1)‖ <= C * e (n + 1)
  dsimp [e]
  have hstep := relation14_norm_step_thm A (n + 1) (by omega)
  have hlam := (A.lambda_bounds (n + 1) (by omega)).2
  have hL : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
  have hnorm : 0 <= ‖A.x (n + 1) - A.p (n + 1)‖ := norm_nonneg _
  have hcoef :
      1 + A.lambda (n + 1) * P.Lgrad_h <=
        C := by
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_right hlam hL]
  exact le_trans hstep (mul_le_mul_of_nonneg_right hcoef hnorm)

private theorem m2_nonneg_thm {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    {nu mu : Real} (hnu : 0 < nu) (hmu : 0 < mu) :
    0 <= A.M2 nu mu := by
  have hLh : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
  have hLu : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
  have hlower : 0 <= A.lambdaLower := le_of_lt A.lambdaLower_pos
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

theorem pair_limit_mem_omega {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) {x : EuclideanSpace m}
    (hp : Tendsto A.p atTop (nhds x)) (hx : Tendsto A.x atTop (nhds x)) :
    (x, x) ∈ omega (pairSequence A) := by
  refine ⟨fun n => n, strictMono_id, ?_⟩
  rw [Prod.tendsto_iff]
  exact ⟨by simpa [pairSequence] using hp, by simpa [pairSequence] using hx⟩

theorem norm_le_delta_den_add_delta {D delta B Delta r : Real}
    (hD : 0 < D) (hdelta : 0 < delta) (hB : 0 < B) (_hr : 0 <= r)
    (hmain : D * r ^ 2 / B <= Delta) :
    r <= (delta / 2) * B + Delta / (2 * delta * D) := by
  have hdeltaB : 0 < delta * B := mul_pos hdelta hB
  have hden1 : 0 < 2 * delta * B := by nlinarith
  have hden2 : 0 < 2 * delta * D := by nlinarith
  have hsq : 0 <= (delta * B - r) ^ 2 := sq_nonneg _
  have hyoung_mul :
      (2 * delta * B) * r <=
        (2 * delta * B) * ((delta / 2) * B + r ^ 2 / (2 * delta * B)) := by
    field_simp [ne_of_gt hden1]
    nlinarith [hsq]
  have hyoung :
      r <= (delta / 2) * B + r ^ 2 / (2 * delta * B) :=
    le_of_mul_le_mul_left hyoung_mul hden1
  have hmain_scaled :
      r ^ 2 / (2 * delta * B) <= Delta / (2 * delta * D) := by
    have hscale :
        (1 / (2 * delta * D)) * (D * r ^ 2 / B) <=
          (1 / (2 * delta * D)) * Delta := by
      exact mul_le_mul_of_nonneg_left hmain (by positivity)
    field_simp [ne_of_gt hD, ne_of_gt hdelta, ne_of_gt hB, ne_of_gt hden2] at hscale ⊢
    ring_nf at hscale ⊢
    exact hscale
  nlinarith

theorem concave_phi_drop_ge_deriv_mul
    {eta : Real} {phi : Real -> Real}
    (hphi : DesingularizingFunction eta phi)
    {a b : Real} (ha : a ∈ Set.Ioo 0 eta) (hb : b ∈ Set.Icc 0 eta)
    (hba : b <= a) :
    phi a - phi b >= deriv phi a * (a - b) := by
  rcases hphi with ⟨_heta, hconc, _hcont, hdiff, _hzero, _hderiv_pos⟩
  by_cases h_eq : b = a
  · subst b
    nlinarith
  · have hlt : b < a := lt_of_le_of_ne hba h_eq
    have haIcc : a ∈ Set.Icc 0 eta := ⟨le_of_lt ha.1, le_of_lt ha.2⟩
    have hfd : DifferentiableAt Real phi a := by
      exact hdiff.differentiableAt (isOpen_Ioo.mem_nhds ha)
    have hslope : deriv phi a <= slope phi b a :=
      hconc.deriv_le_slope hb haIcc hlt hfd
    have hslope' : deriv phi a <= (phi a - phi b) / (a - b) := by
      simpa [slope, div_eq_mul_inv, vsub_eq_sub, mul_comm] using hslope
    have hpos : 0 < a - b := sub_pos.mpr hlt
    have hmul := mul_le_mul_of_nonneg_right hslope' (le_of_lt hpos)
    field_simp [ne_of_gt hpos] at hmul
    nlinarith

theorem antitone_real_tendsto_sInf {u : Nat -> Real} (hanti : Antitone u)
    (hbdd : BddBelow (Set.range u)) :
    Tendsto u atTop (nhds (sInf (Set.range u))) := by
  exact tendsto_atTop_isGLB hanti (isGLB_csInf (Set.range_nonempty u) hbdd)

private theorem erealAddReal_eq_add_for_bddBelow (a : EReal) (r : Real) :
    erealAddReal a r = a + (r : EReal) := by
  cases a with
  | bot =>
      rw [EReal.bot_add]
      rfl
  | coe s =>
      rw [← EReal.coe_add]
      rfl
  | top =>
      rw [EReal.top_add_coe]
      rfl

private theorem lowerSemicontinuous_add_ereal_for_bddBelow {X : Type*} [TopologicalSpace X]
    {g h : X -> EReal} (hg : LowerSemicontinuous g) (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x => g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y => g y + h y) (nhds x) := by
      simpa using
        (EReal.le_liminf_add :
          Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
            Filter.liminf (g + h) (nhds x))

private theorem objective_isProper_for_bddBelow {m : Nat} (P : ProblemData m) :
    ERealFunction.IsProper P.objective := by
  rcases P.f_proper with ⟨hf_ne_bot, x0, hx0_lt_top⟩
  constructor
  · intro x
    unfold ProblemData.objective objectiveSum erealAddReal
    cases hfx : P.f x with
    | bot =>
        exact (hf_ne_bot x hfx).elim
    | coe r =>
        change ((r : EReal) + (P.h x : EReal)) ≠ ⊥
        rw [← EReal.coe_add]
        exact EReal.coe_ne_bot _
    | top =>
        change ((⊤ : EReal) + (P.h x : EReal)) ≠ ⊥
        rw [EReal.top_add_coe]
        exact top_ne_bot
  · have hx0_ne_top : P.f x0 ≠ ⊤ := ne_of_lt hx0_lt_top
    have hx0_eff : x0 ∈ ERealFunction.effectiveDom P.f := by
      rw [ERealFunction.mem_effectiveDom_iff]
      exact ⟨hx0_ne_top, hf_ne_bot x0⟩
    rcases (ERealFunction.mem_effectiveDom_iff_exists_real P.f x0).mp hx0_eff with
      ⟨r, hr⟩
    refine ⟨x0, ?_⟩
    rw [ERealFunction.mem_dom_iff]
    unfold ProblemData.objective objectiveSum erealAddReal
    rw [hr]
    change ((r : EReal) + (P.h x0 : EReal)) < ⊤
    rw [← EReal.coe_add]
    exact EReal.coe_lt_top _

private theorem objective_lowerSemicontinuous_for_bddBelow {m : Nat} (P : ProblemData m) :
    LowerSemicontinuous P.objective := by
  have hh_cont : Continuous (fun x : EuclideanSpace m => (P.h x : EReal)) :=
    continuous_coe_real_ereal.comp P.h_frechet_differentiable.continuous
  have hh_lsc : LowerSemicontinuous (fun x : EuclideanSpace m => (P.h x : EReal)) :=
    hh_cont.lowerSemicontinuous
  have hsum :
      LowerSemicontinuous
        (fun x : EuclideanSpace m => P.f x + (P.h x : EReal)) :=
    lowerSemicontinuous_add_ereal_for_bddBelow P.f_lsc hh_lsc
  change LowerSemicontinuous (objectiveSum P.f P.h)
  convert hsum using 1
  funext x
  simp [objectiveSum, erealAddReal_eq_add_for_bddBelow]

private theorem objective_bddBelow_of_coercive_local {m : Nat} {P : ProblemData m}
    (hcoercive : CoerciveEReal P.objective) :
    ∃ C : Real, ∀ x : EuclideanSpace m, (C : EReal) <= P.objective x := by
  have hmin :=
    exists_minimizer_of_proper_lsc_coercive P.objective
      (objective_isProper_for_bddBelow P)
      (objective_lowerSemicontinuous_for_bddBelow P) hcoercive
  rcases hmin.1 with ⟨C, hCinf⟩
  rcases hmin.2 with ⟨xmin, hxmin_min, hxmin_eq_inf⟩
  refine ⟨C, ?_⟩
  intro x
  have hmin_all : P.objective xmin <= P.objective x := by
    simpa [IsMinOn, IsMinFilter] using hxmin_min trivial
  rw [← hCinf, ← hxmin_eq_inf]
  exact hmin_all

private theorem sqrt_sq_add_sq_le_add {a b : Real} (ha : 0 <= a) (hb : 0 <= b) :
    Real.sqrt (a ^ 2 + b ^ 2) <= a + b := by
  have hsum : 0 <= a + b := by linarith
  have hrad : 0 <= a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  rw [Real.sqrt_le_left hsum]
  nlinarith [mul_nonneg ha hb]

private theorem denom_algebra_bound
    {S x y C D E U V : Real}
    (hS_nonneg : 0 <= S) (hx : 0 <= x) (hy : 0 <= y)
    (hC : 0 <= C) (hD : 0 <= D) (hE : 0 <= E)
    (hS : S <= C * x + D * y)
    (hU : U = Real.sqrt 2 * Real.sqrt ((C + E) ^ 2 + E ^ 2))
    (hV : V = Real.sqrt 2 * D) :
    Real.sqrt ((S + E * x) ^ 2 + (E * x) ^ 2) <= U * x + V * y := by
  let A0 : Real := (C + E) * x
  let B0 : Real := D * y
  let R : Real := Real.sqrt 2 * Real.sqrt ((C + E) ^ 2 + E ^ 2) * x
  let T : Real := Real.sqrt 2 * D * y
  have hA0_nonneg : 0 <= A0 := by
    dsimp [A0]
    exact mul_nonneg (add_nonneg hC hE) hx
  have hB0_nonneg : 0 <= B0 := by
    dsimp [B0]
    exact mul_nonneg hD hy
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    positivity
  have hT_nonneg : 0 <= T := by
    dsimp [T]
    positivity
  have hSEx_nonneg : 0 <= S + E * x := by
    exact add_nonneg hS_nonneg (mul_nonneg hE hx)
  have hSEx_le : S + E * x <= A0 + B0 := by
    dsimp [A0, B0]
    nlinarith
  have hleft_le :
      Real.sqrt ((S + E * x) ^ 2 + (E * x) ^ 2) <=
        Real.sqrt ((A0 + B0) ^ 2 + (E * x) ^ 2) := by
    exact Real.sqrt_le_sqrt (by
      have hsq1 : (S + E * x) ^ 2 <= (A0 + B0) ^ 2 := by
        exact sq_le_sq'
          (by linarith [hSEx_nonneg, add_nonneg hA0_nonneg hB0_nonneg])
          hSEx_le
      nlinarith)
  have hmiddle_le :
      Real.sqrt ((A0 + B0) ^ 2 + (E * x) ^ 2) <=
        Real.sqrt (R ^ 2 + T ^ 2) := by
    exact Real.sqrt_le_sqrt (by
      have htwo : (A0 + B0) ^ 2 <= 2 * A0 ^ 2 + 2 * B0 ^ 2 := by
        nlinarith [sq_nonneg (A0 - B0)]
      have hR_sq : R ^ 2 = 2 * (((C + E) ^ 2 + E ^ 2) * x ^ 2) := by
        dsimp [R]
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) <= 2),
          Real.sq_sqrt (by nlinarith [sq_nonneg (C + E), sq_nonneg E])]
        ring
      have hT_sq : T ^ 2 = 2 * D ^ 2 * y ^ 2 := by
        dsimp [T]
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
      dsimp [A0, B0] at htwo ⊢
      rw [hR_sq, hT_sq]
      nlinarith)
  calc
    Real.sqrt ((S + E * x) ^ 2 + (E * x) ^ 2)
        <= Real.sqrt ((A0 + B0) ^ 2 + (E * x) ^ 2) := hleft_le
    _ <= Real.sqrt (R ^ 2 + T ^ 2) := hmiddle_le
    _ <= R + T := sqrt_sq_add_sq_le_add hR_nonneg hT_nonneg
    _ = U * x + V * y := by
      subst U
      subst V
      dsimp [R, T]

private theorem desingularizing_nonneg_of_lt
    {eta : Real} {phi : Real -> Real}
    (hphi : DesingularizingFunction eta phi) {s : Real}
    (hs0 : 0 <= s) (hslt : s < eta) : 0 <= phi s := by
  rcases hphi with ⟨_heta, _hconc, hcont, hdiff, hzero, hderiv_pos⟩
  have hsub : Set.Icc 0 s ⊆ Set.Icc 0 eta := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (le_of_lt hslt)⟩
  have hcont' : ContinuousOn phi (Set.Icc 0 s) := hcont.mono hsub
  have hdiff' : DifferentiableOn Real phi (interior (Set.Icc 0 s)) := by
    refine hdiff.mono ?_
    intro t ht
    rw [interior_Icc] at ht
    exact ⟨ht.1, lt_trans ht.2 hslt⟩
  have hderiv_nonneg : ∀ t ∈ interior (Set.Icc 0 s), 0 <= deriv phi t := by
    intro t ht
    rw [interior_Icc] at ht
    exact le_of_lt (hderiv_pos t ⟨ht.1, lt_trans ht.2 hslt⟩)
  have hmono : MonotoneOn phi (Set.Icc 0 s) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont' hdiff' hderiv_nonneg
  have h0mem : (0 : Real) ∈ Set.Icc 0 s := ⟨le_rfl, hs0⟩
  have hsmem : s ∈ Set.Icc 0 s := ⟨hs0, le_rfl⟩
  have hle : phi 0 <= phi s := hmono h0mem hsmem hs0
  linarith

private theorem sum_range_sub_telescope (g : Nat -> Real) :
    ∀ K : Nat, Finset.sum (Finset.range K) (fun k => g k - g (k + 1)) = g 0 - g K
  | 0 => by simp
  | K + 1 => by
      rw [Finset.sum_range_succ, sum_range_sub_telescope g K]
      ring

private theorem summable_scaled_telescope_drops
    {g : Nat -> Real} {c : Real}
    (hc_nonneg : 0 <= c)
    (hdrop_nonneg : ∀ k, 0 <= g k - g (k + 1))
    (hg_nonneg : ∀ k, 0 <= g k) :
    Summable (fun k : Nat => c * (g k - g (k + 1))) := by
  refine summable_of_sum_range_le
    (f := fun k : Nat => c * (g k - g (k + 1))) (c := c * g 0) ?_ ?_
  · intro k
    exact mul_nonneg hc_nonneg (hdrop_nonneg k)
  · intro K
    calc
      Finset.sum (Finset.range K) (fun k : Nat => c * (g k - g (k + 1)))
          = c * Finset.sum (Finset.range K) (fun k : Nat => g k - g (k + 1)) := by
            rw [Finset.mul_sum]
      _ = c * (g 0 - g K) := by rw [sum_range_sub_telescope]
      _ <= c * g 0 := by
            exact mul_le_mul_of_nonneg_left (by linarith [hg_nonneg K]) hc_nonneg

theorem xp_summable_of_KL_orbit {m : Nat} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : Real)
    (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective)
    (hH_KL : KLOrbitPackage A nu mu) :
    Summable (fun n : Nat => ‖A.x n - A.p n‖) := by
  rcases hchosen with ⟨hnu, hmu, hstrict, hM2ltM1⟩
  let M1 : Real := A.M1 nu mu
  let M2 : Real := A.M2 nu mu
  let D : Real := M1 - M2
  have hDpos : 0 < D := by
    dsimp [D, M1, M2]
    nlinarith [hM2ltM1]
  have hboundedBelow :
      ∃ C : Real, ∀ x : EuclideanSpace m, (C : EReal) <= P.objective x :=
    objective_bddBelow_of_coercive_local hcoercive
  have h34 :=
    lemma_3_4_decrease A nu mu
      (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩) hboundedBelow
  rcases h34 with ⟨hxp_sq_sum, hxx_sq_sum, hobj_conv⟩
  have h37 :=
    lemma_3_7_pair_cluster_points A nu mu
      (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩) hcoercive
  rcases h37 with
    ⟨hΩne, hΩsub, hHcrit_eq_diag, hdistΩ, hΩcompact, hΩconn, hHconst⟩
  let Omega : Set (EuclideanSpace m × EuclideanSpace m) := omega (pairSequence A)
  have hOmega_ne : Omega.Nonempty := by
    simpa [Omega] using hΩne
  rcases hOmega_ne with ⟨zstar, hzstarOmega⟩
  have hOmega_compact : IsCompact Omega := by
    simpa [Omega] using hΩcompact
  have hOmega_const : ∃ c : EReal, ∀ z ∈ Omega, HFunction P M2 z = c := by
    simpa [Omega, M2] using hHconst
  have hKL_window := hH_KL Omega ⟨zstar, hzstarOmega⟩ hOmega_compact hOmega_const
    zstar hzstarOmega
  rcases hKL_window with ⟨epsilon, eta, phi, heps, heta, hphi, hKL⟩
  let Hreal : Nat -> Real := fun n => (HFunction P M2 (pairSequence A n)).toReal
  have hdescent_real :
      ∀ n, 1 <= n ->
        D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 <= Hreal n - Hreal (n + 1) := by
    intro n hn
    have h := lyapunov_descent_real A nu mu hnu hmu n hn
    simpa [Hreal, D, M1, M2] using h
  have hH_mono_tail :
      ∀ n, 1 <= n -> Hreal (n + 1) <= Hreal n := by
    intro n hn
    have hdrop := hdescent_real n hn
    have hnonneg : 0 <= D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 :=
      mul_nonneg (le_of_lt hDpos) (sq_nonneg _)
    nlinarith
  have hzstar : zstar ∈ omega (pairSequence A) := by
    simpa [Omega] using hzstarOmega
  have hzstar_Hcrit : zstar ∈ HCriticalSet P M2 := by
    exact hΩsub hzstar
  have hzstar_diag : zstar ∈ diagonalCriticalSet P := by
    rwa [hHcrit_eq_diag] at hzstar_Hcrit
  let pstar : EuclideanSpace m := zstar.1
  have hzstar_fst_eq_snd : zstar.1 = zstar.2 := hzstar_diag.1
  have hpstar_crit : pstar ∈ criticalPoints P.objective := by
    simpa [pstar] using hzstar_diag.2
  have hzstar_pair : zstar = (pstar, pstar) := by
    ext <;> simp [pstar, hzstar_fst_eq_snd]
  let HstarReal : Real := (HFunction P M2 zstar).toReal
  let Δ : Nat -> Real := fun n => Hreal n - HstarReal
  let denom : Nat -> Real := fun n =>
    Real.sqrt
      (‖subgradientEstimateVector A n + (2 * M2) • (A.p n - A.x n)‖ ^ 2 +
       (2 * M2) ^ 2 * ‖A.x n - A.p n‖ ^ 2)
  have hKL_ready :
      ∀ n, 2 <= n ->
        Metric.infDist (pairSequence A n) Omega < epsilon ->
        HFunction P M2 zstar < HFunction P M2 (pairSequence A n) ->
        HFunction P M2 (pairSequence A n) <
          erealAddReal (HFunction P M2 zstar) eta ->
        1 <= deriv phi (Δ n) * denom n := by
    intro n hn hdist hgt hlt
    have h := hKL n hn hdist hgt hlt
    simpa [Hreal, HstarReal, Δ, denom, M2] using h
  have hdescent_delta :
      ∀ n, 1 <= n ->
        D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 <= Δ n - Δ (n + 1) := by
    intro n hn
    have hdrop := hdescent_real n hn
    dsimp [Δ]
    linarith
  have hdelta_mono :
      ∀ n, 1 <= n -> Δ (n + 1) <= Δ n := by
    intro n hn
    have hmono := hH_mono_tail n hn
    dsimp [Δ]
    linarith
  have hM2_nonneg : 0 <= M2 := by
    dsimp [M2]
    exact m2_nonneg_thm A hnu hmu
  have hdenom_nonneg : ∀ n, 0 <= denom n := by
    intro n
    dsimp [denom]
    exact Real.sqrt_nonneg _
  have hlemma35_tail :
      ∀ n, 2 <= n ->
        subgradientEstimateVector A n ∈ limitingSubdifferential P.objective (A.p n) ∧
          ‖subgradientEstimateVector A n‖ <=
            (A.Lgrad_u / A.lambda n + P.Lgrad_h) * ‖A.x n - A.p n‖ +
              (A.alphaSeq n / A.lambda n) * (1 + A.lambda (n - 1) * P.Lgrad_h) *
                ‖A.x (n - 1) - A.p (n - 1)‖ := by
    intro n hn
    exact lemma_3_5_subgradient_estimate A n hn
  have hdist_to_Omega :
      Tendsto (fun n : Nat => Metric.infDist (pairSequence A n) Omega) atTop
        (nhds 0) := by
    simpa [Omega] using hdistΩ
  have hHreal_tendsto_HstarReal :
      Tendsto Hreal atTop (nhds HstarReal) := by
    have hHreal_tail_bddBelow :
        BddBelow (Set.range (fun k : Nat => Hreal (k + 1))) := by
      rcases hboundedBelow with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      rintro y ⟨k, rfl⟩
      have hp_eff : A.p (k + 1) ∈ ERealFunction.effectiveDom P.objective :=
        p_objective_effectiveDom_thm A (by omega)
      rcases (ERealFunction.mem_effectiveDom_iff_exists_real P.objective (A.p (k + 1))).mp
          hp_eff with ⟨r, hr⟩
      have hC_le_r : C <= r := by
        have hC_le_r_ereal : (C : EReal) <= (r : EReal) := by
          simpa [hr] using hC (A.p (k + 1))
        exact EReal.coe_le_coe_iff.mp hC_le_r_ereal
      have hM2_quad_nonneg : 0 <= M2 * ‖A.p (k + 1) - A.x (k + 1)‖ ^ 2 :=
        mul_nonneg hM2_nonneg (sq_nonneg _)
      dsimp [Hreal, HFunction, pairSequence]
      rw [objectiveWithQuadratic_toReal_eq_thm (P := P) (M := M2)
        (x := A.p (k + 1)) (y := A.x (k + 1)) hp_eff]
      rw [hr, EReal.toReal_coe]
      nlinarith
    have hHreal_tail_antitone : Antitone (fun k : Nat => Hreal (k + 1)) := by
      refine antitone_nat_of_succ_le ?_
      intro k
      simpa [Nat.add_assoc] using hH_mono_tail (k + 1) (by omega)
    have hHreal_tail_tendsto :
        Tendsto (fun k : Nat => Hreal (k + 1)) atTop
          (nhds (sInf (Set.range (fun k : Nat => Hreal (k + 1))))) :=
      antitone_real_tendsto_sInf hHreal_tail_antitone hHreal_tail_bddBelow
    have hHreal_tendsto_tail_limit :
        Tendsto Hreal atTop
          (nhds (sInf (Set.range (fun k : Nat => Hreal (k + 1))))) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mp hHreal_tail_tendsto
    rcases IsSequentialClusterPt.exists_subseq_tendsto (by simpa [Omega] using hzstarOmega) with
      ⟨ψ_raw, hψ_raw_mono, hψ_raw_pair_tendsto⟩
    let ψ : Nat -> Nat := fun k => ψ_raw (k + 2)
    have hψ_mono : StrictMono ψ := by
      intro a b hab
      exact hψ_raw_mono (by omega)
    have hψ_ge_two : ∀ k, 2 <= ψ k := by
      intro k
      have hle : k + 2 <= ψ_raw (k + 2) := hψ_raw_mono.le_apply
      dsimp [ψ]
      omega
    have hψ_pair_tendsto :
        Tendsto (pairSequence A ∘ ψ) atTop (nhds zstar) :=
      hψ_raw_pair_tendsto.comp (tendsto_add_atTop_nat 2)
    have hψ_p_tendsto : Tendsto (A.p ∘ ψ) atTop (nhds pstar) := by
      have hfst := (continuous_fst.tendsto zstar).comp hψ_pair_tendsto
      simpa [pairSequence, Function.comp, pstar] using hfst
    have hψ_x_tendsto : Tendsto (fun k : Nat => A.x (ψ k)) atTop (nhds pstar) := by
      have hsnd := (continuous_snd.tendsto zstar).comp hψ_pair_tendsto
      simpa [pairSequence, Function.comp, pstar, hzstar_fst_eq_snd] using hsnd
    have hsubseq_data :
        StrictMono ψ ∧ (∀ k, 2 <= ψ k) ∧
          Tendsto (A.p ∘ ψ) atTop (nhds pstar) ∧
          Tendsto (fun k : Nat => A.x (ψ k)) atTop (nhds pstar) := 
      ⟨hψ_mono, hψ_ge_two, hψ_p_tendsto, hψ_x_tendsto⟩
    rcases BotCsetnek2015.objective_constant_on_omega_core A nu mu
        (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩)
        hboundedBelow hxp_sq_sum hxx_sq_sum hobj_conv with
      ⟨c, hconst_obj⟩
    have hpstar_omega_p : pstar ∈ omega A.p := by
      refine ⟨ψ, hψ_mono, ?_⟩
      simpa [Function.comp] using hψ_p_tendsto
    have hpstar_obj : P.objective pstar = (c : EReal) :=
      hconst_obj pstar hpstar_omega_p
    have hobj_subseq :
        Tendsto (fun k : Nat => P.objective (A.p (ψ k))) atTop
          (nhds (P.objective pstar)) :=
      BotCsetnek2015.objective_tendsto_of_cluster_subsequence A nu mu
        (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩)
        hxp_sq_sum hxx_sq_sum hboundedBelow hobj_conv
        hψ_mono hψ_ge_two hψ_p_tendsto hψ_x_tendsto
    have hobj_subseq_c :
        Tendsto (fun k : Nat => P.objective (A.p (ψ k))) atTop
          (nhds ((c : EReal))) := by
      simpa [hpstar_obj] using hobj_subseq
    have hobj_toReal :
        Tendsto (fun k : Nat => (P.objective (A.p (ψ k))).toReal) atTop
          (nhds c) := by
      have hfinite : (c : EReal) ≠ ⊤ ∧ (c : EReal) ≠ ⊥ :=
        ⟨EReal.coe_ne_top c, EReal.coe_ne_bot c⟩
      simpa [EReal.toReal_coe] using
        (EReal.tendsto_toReal hfinite.1 hfinite.2).comp hobj_subseq_c
    have hnorm_zero :
        Tendsto (fun k : Nat => ‖A.p (ψ k) - A.x (ψ k)‖) atTop
          (nhds 0) := by
      have hnorm_xp :
          Tendsto (fun n : Nat => ‖A.x n - A.p n‖) atTop (nhds 0) := by
        have hs0 :
            Tendsto (fun n : Nat => ‖A.x n - A.p n‖ ^ 2) atTop
              (nhds 0) :=
          hxp_sq_sum.tendsto_atTop_zero
        have hsqrt :
            Tendsto (fun n : Nat => Real.sqrt (‖A.x n - A.p n‖ ^ 2)) atTop
              (nhds (Real.sqrt 0)) :=
          (Real.continuous_sqrt.tendsto 0).comp hs0
        simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt
      have hsubseq :=
        hnorm_xp.comp (StrictMono.tendsto_atTop hψ_mono)
      simpa [norm_sub_rev] using hsubseq
    have hquad_zero :
        Tendsto (fun k : Nat => M2 * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2) atTop
          (nhds 0) := by
      have hsq :=
        (hnorm_zero.pow 2).const_mul M2
      simpa using hsq
    have hHstar_eq_c : HstarReal = c := by
      have hp_eff : pstar ∈ ERealFunction.effectiveDom P.objective := by
        rw [ERealFunction.mem_effectiveDom_iff]
        rw [hpstar_obj]
        exact ⟨EReal.coe_ne_top c, EReal.coe_ne_bot c⟩
      dsimp [HstarReal, HFunction]
      rw [hzstar_pair]
      rw [objectiveWithQuadratic_toReal_eq_thm (P := P) (M := M2)
        (x := pstar) (y := pstar) hp_eff]
      rw [hpstar_obj, EReal.toReal_coe]
      simp
    have hHreal_subseq :
        Tendsto (fun k : Nat => Hreal (ψ k)) atTop (nhds HstarReal) := by
      have hHreal_eq : ∀ k : Nat,
          Hreal (ψ k) =
            (P.objective (A.p (ψ k))).toReal +
              M2 * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2 := by
        intro k
        have hp_eff : A.p (ψ k) ∈ ERealFunction.effectiveDom P.objective :=
          p_objective_effectiveDom_thm A (by
            have h2 := hψ_ge_two k
            omega)
        dsimp [Hreal, HFunction, pairSequence]
        rw [objectiveWithQuadratic_toReal_eq_thm (P := P) (M := M2)
          (x := A.p (ψ k)) (y := A.x (ψ k)) hp_eff]
      have hsum := hobj_toReal.add hquad_zero
      have hrew :
          (fun k : Nat =>
              (P.objective (A.p (ψ k))).toReal +
                M2 * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2) =
            fun k : Nat => Hreal (ψ k) := by
        funext k
        rw [hHreal_eq k]
      rw [← hrew]
      simpa [hHstar_eq_c] using hsum
    have hlimit_eq :
        sInf (Set.range (fun k : Nat => Hreal (k + 1))) = HstarReal := by
      exact tendsto_nhds_unique
        (hHreal_tendsto_tail_limit.comp (StrictMono.tendsto_atTop hψ_mono))
        hHreal_subseq
    simpa [hlimit_eq] using hHreal_tendsto_tail_limit
  have hdelta_tendsto_zero : Tendsto Δ atTop (nhds 0) := by
    dsimp [Δ]
    have hconst : Tendsto (fun _ : Nat => HstarReal) atTop (nhds HstarReal) :=
      tendsto_const_nhds
    simpa using hHreal_tendsto_HstarReal.sub hconst
  have hfinite_length_core :
      Summable (fun n : Nat => ‖A.x n - A.p n‖) := by
    have hdelta_eventually_eta : ∀ᶠ n in atTop, |Δ n| < eta := by
      have h := (Metric.tendsto_nhds.mp hdelta_tendsto_zero) eta heta
      simpa [Real.dist_eq, sub_eq_add_neg, abs_neg] using h
    have hdist_eventually_eps :
        ∀ᶠ n in atTop, |Metric.infDist (pairSequence A n) Omega| < epsilon := by
      have h := (Metric.tendsto_nhds.mp hdist_to_Omega) epsilon heps
      simpa [Real.dist_eq, sub_eq_add_neg, abs_neg] using h
    rcases (eventually_atTop.mp hdelta_eventually_eta) with ⟨NΔ, hNΔ⟩
    rcases (eventually_atTop.mp hdist_eventually_eps) with ⟨Nd, hNd⟩
    let N : Nat := max (max NΔ Nd) 2
    have hN_two : 2 <= N := by
      dsimp [N]
      omega
    have hdelta_abs_lt_eta : ∀ n, N <= n -> |Δ n| < eta := by
      intro n hn
      exact hNΔ n (by
        dsimp [N] at hn
        omega)
    have hdist_abs_lt_eps :
        ∀ n, N <= n -> |Metric.infDist (pairSequence A n) Omega| < epsilon := by
      intro n hn
      exact hNd n (by
        dsimp [N] at hn
        omega)
    have hdist_lt_eps :
        ∀ n, N <= n -> Metric.infDist (pairSequence A n) Omega < epsilon := by
      intro n hn
      have hnonneg : 0 <= Metric.infDist (pairSequence A n) Omega := Metric.infDist_nonneg
      have h := hdist_abs_lt_eps n hn
      rwa [abs_of_nonneg hnonneg] at h
    have hdelta_lt_eta_of_nonneg :
        ∀ n, N <= n -> 0 <= Δ n -> Δ n < eta := by
      intro n hn hnonneg
      have h := hdelta_abs_lt_eta n hn
      rwa [abs_of_nonneg hnonneg] at h
    have hdelta_tail_antitone : Antitone (fun k : Nat => Δ (k + 1)) := by
      refine antitone_nat_of_succ_le ?_
      intro k
      simpa [Nat.add_assoc] using hdelta_mono (k + 1) (by omega)
    have hdelta_tail_tendsto_zero :
        Tendsto (fun k : Nat => Δ (k + 1)) atTop (nhds 0) :=
      hdelta_tendsto_zero.comp (tendsto_add_atTop_nat 1)
    have hdelta_nonneg_tail : ∀ n, 1 <= n -> 0 <= Δ n := by
      intro n hn
      rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
      simpa [Nat.add_comm] using
        hdelta_tail_antitone.le_of_tendsto hdelta_tail_tendsto_zero k
    have hdelta_pos_lt_eta_of_pos :
        ∀ n, N <= n -> 0 < Δ n -> Δ n < eta := by
      intro n hn hpos
      exact hdelta_lt_eta_of_nonneg n hn (le_of_lt hpos)
    by_cases hzero_case : ∃ n, 1 <= n ∧ Δ n = 0
    · -- Case I in the paper: once the Lyapunov gap reaches zero, descent forces a
      -- zero tail for `‖x_n - p_n‖`, so summability follows from finite support.
      rcases hzero_case with ⟨n0, hn0, hΔn0⟩
      have hdelta_tail_zero_from_n0 : ∀ k, n0 <= k -> Δ k = 0 := by
        intro k hk
        have hk_nonneg : 0 <= Δ k := hdelta_nonneg_tail k (by omega)
        have hk_le : Δ k <= Δ n0 := by
          refine Nat.le_induction (le_refl _) (fun m hm hΔm => ?_) k hk
          have hm1 : 1 <= m := by omega
          exact le_trans (hdelta_mono m hm1) hΔm
        nlinarith
      have hxp_tail_zero : ∀ k, n0 <= k -> ‖A.x (k + 1) - A.p (k + 1)‖ = 0 := by
        intro k hk
        have hk1 : 1 <= k := by omega
        have hdrop := hdescent_delta k hk1
        have hΔk : Δ k = 0 := hdelta_tail_zero_from_n0 k hk
        have hΔk1 : Δ (k + 1) = 0 := hdelta_tail_zero_from_n0 (k + 1) (by omega)
        have hsq_zero : ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2 = 0 := by
          have hnonneg_sq : 0 <= ‖A.x (k + 1) - A.p (k + 1)‖ ^ 2 := sq_nonneg _
          have hD_nonneg : 0 <= D := le_of_lt hDpos
          nlinarith
        exact sq_eq_zero_iff.mp hsq_zero
      -- The remaining step is a finite-support summability conversion for the
      -- shifted zero tail.
      have hxp_tail_zero' : ∀ n, n0 + 1 <= n -> ‖A.x n - A.p n‖ = 0 := by
        intro n hn
        have hk : n0 <= n - 1 := by omega
        have hzero := hxp_tail_zero (n - 1) hk
        have hn_eq : n - 1 + 1 = n := by omega
        simpa [hn_eq] using hzero
      refine summable_of_ne_finset_zero (s := Finset.range (n0 + 1)) ?_
      intro n hn_not_mem
      have hn_ge : n0 + 1 <= n := by
        exact le_of_not_gt (fun hlt => hn_not_mem (Finset.mem_range.mpr hlt))
      exact hxp_tail_zero' n hn_ge
    · -- Case II in the paper: all tail gaps are strictly positive, so the KL
      -- window gives `0 < Δ n < eta` from index `N` onward.
      have hdelta_pos_tail : ∀ n, 1 <= n -> 0 < Δ n := by
        intro n hn
        have hnonneg := hdelta_nonneg_tail n hn
        have hne : Δ n ≠ 0 := by
          intro hzero
          exact hzero_case ⟨n, hn, hzero⟩
        exact lt_of_le_of_ne' hnonneg hne
      have hdelta_pos_lt_eta :
          ∀ n, N <= n -> 0 < Δ n ∧ Δ n < eta := by
        intro n hn
        have hpos := hdelta_pos_tail n (by omega)
        exact ⟨hpos, hdelta_pos_lt_eta_of_pos n hn hpos⟩
      have hphi_drop :
          ∀ n, N <= n ->
            phi (Δ n) - phi (Δ (n + 1)) >=
              deriv phi (Δ n) * (Δ n - Δ (n + 1)) := by
        intro n hn
        have hn1 : 1 <= n := by
          have hN2 : 2 <= N := hN_two
          omega
        have hnext1 : 1 <= n + 1 := by omega
        have ha : Δ n ∈ Set.Ioo 0 eta :=
          Set.mem_Ioo.mpr ⟨(hdelta_pos_lt_eta n hn).1, (hdelta_pos_lt_eta n hn).2⟩
        have hmono : Δ (n + 1) <= Δ n := hdelta_mono n hn1
        have hb : Δ (n + 1) ∈ Set.Icc 0 eta := by
          refine Set.mem_Icc.mpr ⟨hdelta_nonneg_tail (n + 1) hnext1, ?_⟩
          exact le_trans hmono (le_of_lt (hdelta_pos_lt_eta n hn).2)
        exact concave_phi_drop_ge_deriv_mul hphi ha hb hmono
      have hdescent_delta_tail :
          ∀ n, N <= n ->
            D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 <= Δ n - Δ (n + 1) := by
        intro n hn
        exact hdescent_delta n (by
          have hN2 : 2 <= N := hN_two
          omega)
      -- Remaining KL finite-length core of Theorem 3.1:
      -- combine the KL inequality, the concave desingularizer drop, and
      -- `hdescent_delta`; use `hlemma35_tail` to bound the denominator; then apply
      -- `lemma_2_3_two_step_summability`.
      have hHval_n :
          ∀ n, 1 <= n ->
            HFunction P M2 (pairSequence A n) = ((Hreal n : Real) : EReal) := by
        intro n hn
        have hF :
            HFunction P M2 (pairSequence A n) =
              (((P.objective (A.p n)).toReal + M2 * ‖A.p n - A.x n‖ ^ 2 : Real) : EReal) := by
          dsimp [HFunction, pairSequence]
          exact objectiveWithQuadratic_eq_coe_thm (P := P) (M := M2)
            (x := A.p n) (y := A.x n) (p_objective_effectiveDom_thm A hn)
        rw [hF]
        dsimp [Hreal]
        rw [hF]
        let q : Real := (P.objective (A.p n)).toReal + M2 * ‖A.p n - A.x n‖ ^ 2
        change (q : EReal) = ((((q : EReal)).toReal : Real) : EReal)
        simp [EReal.toReal_coe]
      have hHval_zstar :
          HFunction P M2 zstar = ((HstarReal : Real) : EReal) := by
        have hp_eff : pstar ∈ ERealFunction.effectiveDom P.objective := by
          simpa [criticalPoints, limitingSubdifferential] using hpstar_crit.1
        have hF :
            HFunction P M2 zstar =
              (((P.objective pstar).toReal + M2 * ‖pstar - pstar‖ ^ 2 : Real) : EReal) := by
          rw [hzstar_pair]
          dsimp [HFunction]
          exact objectiveWithQuadratic_eq_coe_thm (P := P) (M := M2)
            (x := pstar) (y := pstar) hp_eff
        rw [hF]
        dsimp [HstarReal]
        rw [hF]
        let q : Real := (P.objective pstar).toReal + M2 * ‖pstar - pstar‖ ^ 2
        change (q : EReal) = ((((q : EReal)).toReal : Real) : EReal)
        simp [EReal.toReal_coe]
      have hKL_tail :
          ∀ n, N <= n -> 1 <= deriv phi (Δ n) * denom n := by
        intro n hn
        refine hKL_ready n (by omega) (hdist_lt_eps n hn) ?_ ?_
        · rw [hHval_zstar, hHval_n n (by omega)]
          exact EReal.coe_lt_coe_iff.mpr (by
            have hpos := (hdelta_pos_lt_eta n hn).1
            dsimp [Δ] at hpos
            linarith)
        · rw [hHval_zstar, hHval_n n (by omega)]
          rw [erealAddReal_eq_add_for_bddBelow]
          rw [← EReal.coe_add]
          exact EReal.coe_lt_coe_iff.mpr (by
            have hlt := (hdelta_pos_lt_eta n hn).2
            dsimp [Δ] at hlt
            linarith)
      have hdenom_pos : ∀ n, N <= n -> 0 < denom n := by
        intro n hn
        by_contra hnot
        have hle : denom n <= 0 := le_of_not_gt hnot
        have hzero : denom n = 0 := by
          have hnonneg := hdenom_nonneg n
          linarith
        have hKL := hKL_tail n hn
        rw [hzero] at hKL
        nlinarith
      have hderiv_pos : ∀ n, N <= n -> 0 < deriv phi (Δ n) := by
        intro n hn
        have hmem : Δ n ∈ Set.Ioo 0 eta :=
          Set.mem_Ioo.mpr ⟨(hdelta_pos_lt_eta n hn).1, (hdelta_pos_lt_eta n hn).2⟩
        exact hphi.2.2.2.2.2 (Δ n) hmem
      have h32 :
          ∀ n, N <= n ->
            D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 / denom n <=
              phi (Δ n) - phi (Δ (n + 1)) := by
        intro n hn
        let r : Real := ‖A.x (n + 1) - A.p (n + 1)‖
        let d : Real := deriv phi (Δ n)
        let B : Real := denom n
        let drop : Real := phi (Δ n) - phi (Δ (n + 1))
        have hdrop : drop >= d * (Δ n - Δ (n + 1)) := by
          simpa [drop, d] using hphi_drop n hn
        have hdesc : D * r ^ 2 <= Δ n - Δ (n + 1) := by
          simpa [r] using hdescent_delta_tail n hn
        have hd_nonneg : 0 <= d := le_of_lt (hderiv_pos n hn)
        have hstep_a : d * D * r ^ 2 <= drop := by
          have hmul := mul_le_mul_of_nonneg_left hdesc hd_nonneg
          nlinarith
        have hKL : 1 <= d * B := by
          simpa [d, B] using hKL_tail n hn
        have hBpos : 0 < B := by
          simpa [B] using hdenom_pos n hn
        have hnum_nonneg : 0 <= D * r ^ 2 :=
          mul_nonneg (le_of_lt hDpos) (sq_nonneg _)
        have hdiv_nonneg : 0 <= D * r ^ 2 / B :=
          div_nonneg hnum_nonneg (le_of_lt hBpos)
        have hmul := mul_le_mul_of_nonneg_right hKL hdiv_nonneg
        have hstep_b : D * r ^ 2 / B <= d * D * r ^ 2 := by
          field_simp [ne_of_gt hBpos] at hmul ⊢
          nlinarith
        have hchain : D * r ^ 2 / B <= drop := le_trans hstep_b hstep_a
        simpa [r, B, drop] using hchain
      have h33 :
          ∀ n, N <= n ->
            ‖A.x (n + 1) - A.p (n + 1)‖ <=
              (1 / 2) * denom n +
                (phi (Δ n) - phi (Δ (n + 1))) / (2 * D) := by
        intro n hn
        have hmain := norm_le_delta_den_add_delta
          (D := D) (delta := 1) (B := denom n)
          (Delta := phi (Δ n) - phi (Δ (n + 1)))
          (r := ‖A.x (n + 1) - A.p (n + 1)‖)
          hDpos (by norm_num) (hdenom_pos n hn) (norm_nonneg _) (h32 n hn)
        simpa using hmain
      have hphi_diff_nonneg :
          ∀ n, N <= n -> 0 <= phi (Δ n) - phi (Δ (n + 1)) := by
        intro n hn
        have hdrop := hphi_drop n hn
        have hderiv_nonneg : 0 <= deriv phi (Δ n) := le_of_lt (hderiv_pos n hn)
        have hdelta_drop_nonneg : 0 <= Δ n - Δ (n + 1) := by
          have hn1 : 1 <= n := by
            have hN2 : 2 <= N := hN_two
            omega
          have hmono := hdelta_mono n hn1
          linarith
        nlinarith [mul_nonneg hderiv_nonneg hdelta_drop_nonneg]
      have h33_delta :
          ∀ delta : Real, 0 < delta ->
            ∀ n, N <= n ->
              ‖A.x (n + 1) - A.p (n + 1)‖ <=
                (delta / 2) * denom n +
                  (phi (Δ n) - phi (Δ (n + 1))) / (2 * delta * D) := by
        intro delta hdelta n hn
        exact norm_le_delta_den_add_delta
          (D := D) (delta := delta) (B := denom n)
          (Delta := phi (Δ n) - phi (Δ (n + 1)))
          (r := ‖A.x (n + 1) - A.p (n + 1)‖)
          hDpos hdelta (hdenom_pos n hn) (norm_nonneg _) (h32 n hn)
      let U : Real :=
        Real.sqrt 2 *
          Real.sqrt ((A.Lgrad_u / A.lambdaLower + P.Lgrad_h + 2 * M2) ^ 2 +
            (2 * M2) ^ 2)
      let V : Real :=
        Real.sqrt 2 * (A.alpha / A.lambdaLower) *
          (1 + A.lambdaUpper * P.Lgrad_h)
      have hU_nonneg : 0 <= U := by
        dsimp [U]
        positivity
      have hV_nonneg : 0 <= V := by
        have hratio : 0 <= A.alpha / A.lambdaLower :=
          div_nonneg A.alpha_nonneg (le_of_lt A.lambdaLower_pos)
        have hfactor : 0 <= 1 + A.lambdaUpper * P.Lgrad_h := by
          have hLh : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
          have hprod : 0 <= A.lambdaUpper * P.Lgrad_h :=
            mul_nonneg (le_of_lt A.lambdaUpper_pos) hLh
          linarith
        dsimp [V]
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hratio) hfactor
      have hdenom_bound :
          ∀ n, N <= n ->
            denom n <= U * ‖A.x n - A.p n‖ +
              V * ‖A.x (n - 1) - A.p (n - 1)‖ := by
        intro n hn
        let xn : Real := ‖A.x n - A.p n‖
        let yn : Real := ‖A.x (n - 1) - A.p (n - 1)‖
        let K1 : Real := A.Lgrad_u / A.lambdaLower + P.Lgrad_h
        let K2 : Real :=
          (A.alpha / A.lambdaLower) * (1 + A.lambdaUpper * P.Lgrad_h)
        let E : Real := 2 * M2
        have hn2 : 2 <= n := by
          have hN2 : 2 <= N := hN_two
          omega
        have hn1 : 1 <= n := by omega
        have hpred1 : 1 <= n - 1 := by omega
        have hx_nonneg : 0 <= xn := by
          dsimp [xn]
          exact norm_nonneg _
        have hy_nonneg : 0 <= yn := by
          dsimp [yn]
          exact norm_nonneg _
        have hK1_nonneg : 0 <= K1 := by
          have hLu : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
          have hLh : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
          dsimp [K1]
          exact add_nonneg (div_nonneg hLu (le_of_lt A.lambdaLower_pos)) hLh
        have hK2_nonneg : 0 <= K2 := by
          have hratio : 0 <= A.alpha / A.lambdaLower :=
            div_nonneg A.alpha_nonneg (le_of_lt A.lambdaLower_pos)
          have hfactor : 0 <= 1 + A.lambdaUpper * P.Lgrad_h := by
            have hLh : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
            exact add_nonneg zero_le_one (mul_nonneg (le_of_lt A.lambdaUpper_pos) hLh)
          dsimp [K2]
          exact mul_nonneg hratio hfactor
        have hE_nonneg : 0 <= E := by
          dsimp [E]
          nlinarith [hM2_nonneg]
        have hK1_bound :
            A.Lgrad_u / A.lambda n + P.Lgrad_h <= K1 := by
          have hlam_lower : A.lambdaLower <= A.lambda n := (A.lambda_bounds n hn1).1
          have hLu_nonneg : 0 <= A.Lgrad_u := le_of_lt A.u_Lgrad_pos
          have hdiv : A.Lgrad_u / A.lambda n <= A.Lgrad_u / A.lambdaLower :=
            div_le_div_of_nonneg_left hLu_nonneg A.lambdaLower_pos hlam_lower
          dsimp [K1]
          linarith
        have hK2_bound :
            (A.alphaSeq n / A.lambda n) * (1 + A.lambda (n - 1) * P.Lgrad_h) <=
              K2 := by
          have halpha_nonneg : 0 <= A.alphaSeq n := (A.alpha_bounds n hn1).1
          have halpha_le : A.alphaSeq n <= A.alpha := (A.alpha_bounds n hn1).2
          have hlam_lower : A.lambdaLower <= A.lambda n := (A.lambda_bounds n hn1).1
          have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam_lower
          have hlampred_upper : A.lambda (n - 1) <= A.lambdaUpper :=
            (A.lambda_bounds (n - 1) hpred1).2
          have hLh_nonneg : 0 <= P.Lgrad_h := P.h_lipschitz_gradient.1
          have hfactor_nonneg : 0 <= 1 + A.lambda (n - 1) * P.Lgrad_h := by
            have hlampred_nonneg : 0 <= A.lambda (n - 1) :=
              le_trans (le_of_lt A.lambdaLower_pos) (A.lambda_bounds (n - 1) hpred1).1
            exact add_nonneg zero_le_one (mul_nonneg hlampred_nonneg hLh_nonneg)
          have hfactor_le :
              1 + A.lambda (n - 1) * P.Lgrad_h <=
                1 + A.lambdaUpper * P.Lgrad_h := by
            simpa [add_comm] using
              add_le_add_left (mul_le_mul_of_nonneg_right hlampred_upper hLh_nonneg) 1
          have halpha_div_le : A.alphaSeq n / A.lambda n <= A.alpha / A.lambdaLower := by
            have hinv_le : (A.lambda n)⁻¹ <= (A.lambdaLower)⁻¹ :=
              inv_anti₀ A.lambdaLower_pos hlam_lower
            have h_alpha_inv_le :
                A.alphaSeq n * (A.lambda n)⁻¹ <=
                  A.alphaSeq n * (A.lambdaLower)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv_le halpha_nonneg
            have h_alpha_upper :
                A.alphaSeq n * (A.lambdaLower)⁻¹ <=
                  A.alpha * (A.lambdaLower)⁻¹ :=
              mul_le_mul_of_nonneg_right halpha_le
                (inv_nonneg.mpr (le_of_lt A.lambdaLower_pos))
            simpa [div_eq_mul_inv] using le_trans h_alpha_inv_le h_alpha_upper
          have halphadiv_nonneg : 0 <= A.alphaSeq n / A.lambda n :=
            div_nonneg halpha_nonneg (le_of_lt hlam_pos)
          have halphadiv_upper_nonneg : 0 <= A.alpha / A.lambdaLower :=
            div_nonneg A.alpha_nonneg (le_of_lt A.lambdaLower_pos)
          dsimp [K2]
          exact mul_le_mul halpha_div_le hfactor_le hfactor_nonneg halphadiv_upper_nonneg
        have hS_bound :
            ‖subgradientEstimateVector A n‖ <= K1 * xn + K2 * yn := by
          have hlem := (hlemma35_tail n hn2).2
          refine le_trans hlem ?_
          dsimp [xn, yn]
          exact add_le_add
            (mul_le_mul_of_nonneg_right hK1_bound (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hK2_bound (norm_nonneg _))
        have hv_le :
            ‖subgradientEstimateVector A n + E • (A.p n - A.x n)‖ <=
              ‖subgradientEstimateVector A n‖ + E * xn := by
          calc
            ‖subgradientEstimateVector A n + E • (A.p n - A.x n)‖
                <= ‖subgradientEstimateVector A n‖ + ‖E • (A.p n - A.x n)‖ :=
                  norm_add_le _ _
            _ = ‖subgradientEstimateVector A n‖ + E * xn := by
                  dsimp [xn]
                  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hE_nonneg,
                    norm_sub_rev]
        have hscalar := denom_algebra_bound
          (S := ‖subgradientEstimateVector A n‖) (x := xn) (y := yn)
          (C := K1) (D := K2) (E := E) (U := U) (V := V)
          (norm_nonneg _) hx_nonneg hy_nonneg hK1_nonneg hK2_nonneg hE_nonneg
          hS_bound (by
            dsimp [U, K1, E]) (by
            dsimp [V, K2]
            ring_nf)
        have hfirst_nonneg :
            0 <= ‖subgradientEstimateVector A n + E • (A.p n - A.x n)‖ :=
          norm_nonneg _
        have hfirst_bound :
            ‖subgradientEstimateVector A n + E • (A.p n - A.x n)‖ <=
              ‖subgradientEstimateVector A n‖ + E * xn := hv_le
        have hsqrt_reduce :
            denom n <=
              Real.sqrt ((‖subgradientEstimateVector A n‖ + E * xn) ^ 2 +
                (E * xn) ^ 2) := by
          dsimp [denom, E, xn]
          rw [show 2 * M2 = E by rfl]
          exact Real.sqrt_le_sqrt (by
            have hsq :
                ‖subgradientEstimateVector A n + E • (A.p n - A.x n)‖ ^ 2 <=
                  (‖subgradientEstimateVector A n‖ + E * xn) ^ 2 := by
              exact sq_le_sq'
                (by
                  have hright_nonneg :
                      0 <= ‖subgradientEstimateVector A n‖ + E * xn := by
                    exact add_nonneg (norm_nonneg _) (mul_nonneg hE_nonneg hx_nonneg)
                  linarith [hfirst_nonneg, hright_nonneg])
                hfirst_bound
            have hquad : (2 * M2) ^ 2 * ‖A.x n - A.p n‖ ^ 2 = (E * xn) ^ 2 := by
              dsimp [E, xn]
              ring
            rw [hquad]
            nlinarith)
        exact le_trans hsqrt_reduce hscalar
      obtain ⟨delta, hdelta_pos, hdelta_small⟩ :
          ∃ delta : Real, 0 < delta ∧ (delta / 2) * (U + V) < 1 := by
        refine ⟨1 / (U + V + 1), ?_, ?_⟩
        · have hden : 0 < U + V + 1 := by linarith
          positivity
        · have hden : 0 < U + V + 1 := by linarith
          have hsum_nonneg : 0 <= U + V := by linarith
          field_simp [ne_of_gt hden]
          nlinarith
      let a : Real := (delta / 2) * U
      let b : Real := (delta / 2) * V
      have hb_nonneg : 0 <= b := by
        dsimp [b]
        positivity
      have hab : a + b < 1 := by
        dsimp [a, b]
        nlinarith
      let xi : Nat -> Real := fun k => ‖A.x (N + k) - A.p (N + k)‖
      let eps : Nat -> Real := fun k =>
        (phi (Δ (N + k)) - phi (Δ (N + k + 1))) / (2 * delta * D)
      have hrec :
          ∀ k, 1 <= k -> xi (k + 1) <= a * xi k + b * xi (k - 1) + eps k := by
        intro k hk
        have hNk_ge : N <= N + k := by omega
        have hNkp1 : N + k + 1 = N + (k + 1) := by omega
        have hNkm1 : N + k - 1 = N + (k - 1) := by omega
        have h33k := h33_delta delta hdelta_pos (N + k) hNk_ge
        have hdenk := hdenom_bound (N + k) hNk_ge
        have hscale :
            (delta / 2) * denom (N + k) <=
              (delta / 2) *
                (U * ‖A.x (N + k) - A.p (N + k)‖ +
                  V * ‖A.x (N + k - 1) - A.p (N + k - 1)‖) := by
          exact mul_le_mul_of_nonneg_left hdenk (by positivity)
        calc
          xi (k + 1)
              = ‖A.x (N + k + 1) - A.p (N + k + 1)‖ := by
                  dsimp [xi]
                  rw [hNkp1]
          _ <= (delta / 2) * denom (N + k) + eps k := by
                  simpa [eps] using h33k
          _ <= (delta / 2) *
                  (U * ‖A.x (N + k) - A.p (N + k)‖ +
                    V * ‖A.x (N + k - 1) - A.p (N + k - 1)‖) + eps k := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right hscale (eps k)
          _ = a * xi k + b * xi (k - 1) + eps k := by
                  dsimp [a, b, xi]
                  rw [hNkm1]
                  ring_nf
      have heps_nonneg : ∀ k, 0 <= eps k := by
        intro k
        have hnum : 0 <= phi (Δ (N + k)) - phi (Δ (N + k + 1)) :=
          hphi_diff_nonneg (N + k) (by omega)
        have hden_pos : 0 < 2 * delta * D := by positivity
        dsimp [eps]
        exact div_nonneg hnum (le_of_lt hden_pos)
      have heps_sum : Summable eps := by
        let c : Real := 1 / (2 * delta * D)
        let g : Nat -> Real := fun k => phi (Δ (N + k))
        have hc_nonneg : 0 <= c := by
          dsimp [c]
          positivity
        have hdrop_nonneg : ∀ k, 0 <= g k - g (k + 1) := by
          intro k
          have h := hphi_diff_nonneg (N + k) (by omega)
          have hidx : N + (k + 1) = N + k + 1 := by omega
          dsimp [g]
          rwa [hidx]
        have hg_nonneg : ∀ k, 0 <= g k := by
          intro k
          dsimp [g]
          exact desingularizing_nonneg_of_lt hphi
            (hdelta_nonneg_tail (N + k) (by omega))
            (hdelta_lt_eta_of_nonneg (N + k) (by omega)
              (hdelta_nonneg_tail (N + k) (by omega)))
        have hsum := summable_scaled_telescope_drops
          (g := g) (c := c) hc_nonneg hdrop_nonneg hg_nonneg
        have heq :
            eps = fun k : Nat => c * (g k - g (k + 1)) := by
          funext k
          dsimp [eps, c, g]
          field_simp [ne_of_gt hdelta_pos, ne_of_gt hDpos]
          ring_nf
        simpa [heq] using hsum
      have hxi_sum : Summable xi := by
        exact lemma_2_3_two_step_summability xi eps a b
          (fun k => norm_nonneg _)
          heps_nonneg heps_sum hb_nonneg hab hrec
      have htail : Summable (fun k : Nat => ‖A.x (k + N) - A.p (k + N)‖) := by
        simpa [xi, Nat.add_comm] using hxi_sum
      exact (_root_.summable_nat_add_iff
        (f := fun n : Nat => ‖A.x n - A.p n‖) N).mp htail
  exact hfinite_length_core

/-- Theorem 3.1: finite length and convergence to a critical point under the KL hypothesis. -/
theorem theorem_3_1_convergence {m : Nat} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : Real) (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective)
    (hH_KL : ProductKLFunction (HFunction P (A.M2 nu mu))) :
    Summable (fun n : Nat => ‖A.x n - A.p n‖) ∧
      Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖) ∧
      ∃ x : EuclideanSpace m,
        x ∈ criticalPoints P.objective ∧
          Tendsto A.x atTop (nhds x) ∧ Tendsto A.p atTop (nhds x) := by
  rcases hchosen with ⟨hnu, hmu, hstrict, hM2ltM1⟩
  let M1 : Real := A.M1 nu mu
  let M2 : Real := A.M2 nu mu
  let D : Real := M1 - M2
  have hDpos : 0 < D := by
    dsimp [D, M1, M2]
    nlinarith [hM2ltM1]
  have hKLOrbit : KLOrbitPackage A nu mu := by
    exact hH_KL P A nu mu rfl
  have h37 :=
    lemma_3_7_pair_cluster_points A nu mu
      (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩) hcoercive
  rcases h37 with
    ⟨hΩne, hΩsub, hHcrit_eq_diag, hdistΩ, hΩcompact, hΩconn, hHconst⟩
  let Omega : Set (EuclideanSpace m × EuclideanSpace m) := omega (pairSequence A)
  have hOmega_ne : Omega.Nonempty := by
    simpa [Omega] using hΩne
  have hOmega_ne_for_KL : Omega.Nonempty := hOmega_ne
  rcases hOmega_ne with ⟨zstar, hzstarOmega⟩
  have hzstar : zstar ∈ omega (pairSequence A) := by
    simpa [Omega] using hzstarOmega
  have hzcrit : zstar.1 ∈ criticalPoints P.objective := by
    have hzH := hΩsub hzstar
    have hzdiag : zstar ∈ diagonalCriticalSet P := by
      rwa [← hHcrit_eq_diag]
    exact hzdiag.2
  have hOmega_compact : IsCompact Omega := by
    simpa [Omega] using hΩcompact
  have hOmega_const : ∃ c : EReal, ∀ z ∈ Omega, HFunction P (A.M2 nu mu) z = c := by
    simpa [Omega] using hHconst
  have hKL_window := hKLOrbit Omega hOmega_ne_for_KL hOmega_compact hOmega_const zstar hzstarOmega
  rcases hKL_window with ⟨epsilon, eta, phi, heps, heta, hphi, hKL⟩
  let Hreal : Nat -> Real := fun n => (HFunction P M2 (pairSequence A n)).toReal
  have hdescent_real :
      ∀ n, 1 <= n ->
        D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 <= Hreal n - Hreal (n + 1) := by
    intro n hn
    have h := lyapunov_descent_real A nu mu hnu hmu n hn
    simpa [Hreal, D, M1, M2] using h
  have hH_mono_tail :
      ∀ n, 1 <= n -> Hreal (n + 1) <= Hreal n := by
    intro n hn
    have hdrop := hdescent_real n hn
    have hnonneg : 0 <= D * ‖A.x (n + 1) - A.p (n + 1)‖ ^ 2 :=
      mul_nonneg (le_of_lt hDpos) (sq_nonneg _)
    nlinarith
  have hxp_sum : Summable (fun n : Nat => ‖A.x n - A.p n‖) :=
    xp_summable_of_KL_orbit A nu mu
      (by exact ⟨hnu, hmu, hstrict, hM2ltM1⟩) hcoercive hKLOrbit
  have hxinc_sum : Summable (fun n : Nat => ‖A.x (n + 1) - A.x n‖) :=
    x_increment_summable_of_xp_summable A hxp_sum
  rcases tendsto_of_summable_successive_norm A.x hxinc_sum with ⟨x, hxlim⟩
  have hplim : Tendsto A.p atTop (nhds x) :=
    p_tendsto_of_x_tendsto_xp_summable A hxlim hxp_sum
  have hxcrit : x ∈ criticalPoints P.objective := by
    have hpair : (x, x) ∈ omega (pairSequence A) :=
      pair_limit_mem_omega A hplim hxlim
    have hHcrit := hΩsub hpair
    have hdiag : (x, x) ∈ diagonalCriticalSet P := by
      rwa [hHcrit_eq_diag] at hHcrit
    exact hdiag.2
  exact ⟨hxp_sum, hxinc_sum, x, hxcrit, hxlim, hplim⟩

end BotCsetnek2015
