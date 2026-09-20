import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_4
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_5
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_5
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_thm_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_thm_3

open Filter
open scoped Topology

namespace BotCsetnek2015

open ERealFunction

theorem erealAddReal_eq_add (a : EReal) (r : ℝ) :
    erealAddReal a r = a + (r : EReal) := by
  cases a with
  | bot =>
      rw [EReal.bot_add]
      change (⊥ : EReal) = ⊥
      rfl
  | coe s =>
      rw [← EReal.coe_add]
      change ((s + r : ℝ) : EReal) = ((s + r : ℝ) : EReal)
      rfl
  | top =>
      rw [EReal.top_add_coe]
      change (⊤ : EReal) = ⊤
      rfl

theorem lowerSemicontinuous_add_ereal_local {X : Type*} [TopologicalSpace X]
    {g h : X → EReal} (hg : LowerSemicontinuous g) (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using
        (EReal.le_liminf_add :
          Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
            Filter.liminf (g + h) (nhds x))

theorem objective_isProper {m : ℕ} (P : ProblemData m) :
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

theorem objective_lowerSemicontinuous {m : ℕ} (P : ProblemData m) :
    LowerSemicontinuous P.objective := by
  have hh_cont : Continuous (fun x : EuclideanSpace m ↦ (P.h x : EReal)) :=
    continuous_coe_real_ereal.comp P.h_frechet_differentiable.continuous
  have hh_lsc : LowerSemicontinuous (fun x : EuclideanSpace m ↦ (P.h x : EReal)) :=
    hh_cont.lowerSemicontinuous
  have hsum :
      LowerSemicontinuous
        (fun x : EuclideanSpace m ↦ P.f x + (P.h x : EReal)) :=
    lowerSemicontinuous_add_ereal_local P.f_lsc hh_lsc
  change LowerSemicontinuous (objectiveSum P.f P.h)
  convert hsum using 1
  funext x
  simp [objectiveSum, erealAddReal_eq_add]

theorem tendsto_norm_of_summable_norm_sq {m : ℕ}
    {z : ℕ → EuclideanSpace m}
    (hs : Summable (fun n : ℕ ↦ ‖z n‖ ^ 2)) :
    Tendsto (fun n : ℕ ↦ ‖z n‖) atTop (nhds 0) := by
  have hs0 : Tendsto (fun n : ℕ ↦ ‖z n‖ ^ 2) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  have hsqrt :
      Tendsto (fun n : ℕ ↦ Real.sqrt (‖z n‖ ^ 2)) atTop
        (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hs0
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

theorem p_increments_tendsto_zero {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P)
    (hxp : Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖ ^ 2))
    (hxx : Summable (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖ ^ 2)) :
    Tendsto (fun n : ℕ ↦ A.p (n + 1) - A.p n) atTop
      (nhds (0 : EuclideanSpace m)) := by
  have hxp_norm :
      Tendsto (fun n : ℕ ↦ ‖A.x n - A.p n‖) atTop (nhds 0) :=
    tendsto_norm_of_summable_norm_sq (z := fun n ↦ A.x n - A.p n) hxp
  have hxx_norm :
      Tendsto (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖) atTop (nhds 0) :=
    tendsto_norm_of_summable_norm_sq (z := fun n ↦ A.x (n + 1) - A.x n) hxx
  have hxp_vec :
      Tendsto (fun n : ℕ ↦ A.x n - A.p n) atTop
        (nhds (0 : EuclideanSpace m)) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hxp_norm
  have hxx_vec :
      Tendsto (fun n : ℕ ↦ A.x (n + 1) - A.x n) atTop
        (nhds (0 : EuclideanSpace m)) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hxx_norm
  have hxp_shift_neg :
      Tendsto (fun n : ℕ ↦ A.p (n + 1) - A.x (n + 1)) atTop
        (nhds (0 : EuclideanSpace m)) := by
    have hshift :
        Tendsto (fun n : ℕ ↦ A.x (n + 1) - A.p (n + 1)) atTop
          (nhds (0 : EuclideanSpace m)) :=
      hxp_vec.comp (tendsto_add_atTop_nat 1)
    simpa [sub_eq_add_neg] using hshift.neg
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          (A.p (n + 1) - A.x (n + 1)) +
            (A.x (n + 1) - A.x n) + (A.x n - A.p n))
        atTop (nhds (0 : EuclideanSpace m)) := by
    simpa using (hxp_shift_neg.add hxx_vec).add hxp_vec
  have hid :
      (fun n : ℕ ↦ A.p (n + 1) - A.p n) =
        fun n : ℕ ↦
          (A.p (n + 1) - A.x (n + 1)) +
            (A.x (n + 1) - A.x n) + (A.x n - A.p n) := by
    funext n
    abel
  simpa [hid]
    using hsum

theorem erealAddReal_le_of_le_local {a : EReal} {r s : ℝ}
    (hrs : r ≤ s) : erealAddReal a r ≤ erealAddReal a s := by
  cases a using EReal.rec with
  | bot =>
      change (⊥ : EReal) ≤ (⊥ : EReal)
      rfl
  | coe a =>
      change ((a + r : ℝ) : EReal) ≤ ((a + s : ℝ) : EReal)
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  | top =>
      change (⊤ : EReal) ≤ (⊤ : EReal)
      rfl

theorem objectiveWithQuadratic_mono_coeff_local {m : ℕ} (P : ProblemData m)
    {M M' : ℝ} (hMM : M ≤ M') (x y : EuclideanSpace m) :
    objectiveWithQuadratic P M x y ≤ objectiveWithQuadratic P M' x y := by
  unfold objectiveWithQuadratic
  apply erealAddReal_le_of_le_local
  exact mul_le_mul_of_nonneg_right hMM (sq_nonneg _)

theorem m2_nonneg_local {m : ℕ} {P : ProblemData m} (A : AlgorithmData P)
    {nu mu : ℝ} (hnu : 0 < nu) (hmu : 0 < mu) :
    0 ≤ A.M2 nu mu := by
  have hLh : 0 ≤ P.Lgrad_h := P.h_lipschitz_gradient.1
  have hLu : 0 ≤ A.Lgrad_u := le_of_lt A.u_Lgrad_pos
  have hlower : 0 ≤ A.lambdaLower := le_of_lt A.lambdaLower_pos
  have halpha : 0 ≤ A.alpha := A.alpha_nonneg
  unfold AlgorithmData.M2 M2Value
  have hnu_nonneg : 0 ≤ nu := le_of_lt hnu
  have hmu_nonneg : 0 ≤ mu := le_of_lt hmu
  have htwo_nu : 0 ≤ 2 * nu := mul_nonneg (by norm_num) hnu_nonneg
  have htwo_mu : 0 ≤ 2 * mu := mul_nonneg (by norm_num) hmu_nonneg
  have htwo_lower : 0 ≤ 2 * A.lambdaLower := mul_nonneg (by norm_num) hlower
  have hbr1 :
      0 ≤
        P.Lgrad_h ^ 2 / (2 * nu) + nu + P.Lgrad_h +
          A.Lgrad_u / (2 * A.lambdaLower) := by
    have h1 : 0 ≤ P.Lgrad_h ^ 2 / (2 * nu) :=
      div_nonneg (sq_nonneg _) htwo_nu
    have h4 : 0 ≤ A.Lgrad_u / (2 * A.lambdaLower) :=
      div_nonneg hLu htwo_lower
    nlinarith
  have hbr2 :
      0 ≤
        mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 +
          (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu) := by
    have hleft : 0 ≤ mu * A.lambdaUpper ^ 2 * P.Lgrad_h ^ 2 :=
      mul_nonneg (mul_nonneg hmu_nonneg (sq_nonneg _)) (sq_nonneg _)
    have hright : 0 ≤ (1 + A.lambdaUpper * P.Lgrad_h) ^ 2 / (2 * mu) :=
      div_nonneg (sq_nonneg _) htwo_mu
    nlinarith
  exact add_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbr1)
    (mul_nonneg (div_nonneg halpha hlower) hbr2)

private noncomputable def algorithmStepSmoothPart_local {m : ℕ} (P : ProblemData m)
    (u : EuclideanSpace m → ℝ) (lambda alphaSeq : ℕ → ℝ)
    (x : ℕ → EuclideanSpace m) (n : ℕ) : EuclideanSpace m → ℝ :=
  fun y ↦
    (1 / lambda n) * bregmanDistance u y (x n) +
      inner ℝ y (gradient P.h (x n)) +
      (alphaSeq n / lambda n) * inner ℝ y (x (n - 1) - x n)

theorem algorithmStepObjective_eq_objectiveSum_smoothPart_local {m : ℕ}
    (P : ProblemData m) (u : EuclideanSpace m → ℝ)
    (lambda alphaSeq : ℕ → ℝ) (x : ℕ → EuclideanSpace m) (n : ℕ) :
    algorithmStepObjective P u lambda alphaSeq x n =
      objectiveSum P.f (algorithmStepSmoothPart_local P u lambda alphaSeq x n) := by
  rfl

theorem objectiveSum_effectiveDom_iff_local {m : ℕ}
    (f : EuclideanSpace m → EReal) (phi : EuclideanSpace m → ℝ)
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

theorem erealAddReal_ne_bot_local (a : EReal) (r : ℝ) (ha : a ≠ ⊥) :
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

theorem algorithmStep_argmin_effectiveDom_local {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) (_hn : 1 ≤ n)
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
  have hGpn_le_Gz : G (A.p n) ≤ G z := by
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

theorem p_objective_effectiveDom_local {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {n : ℕ} (hn : 1 ≤ n) :
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

theorem objectiveWithQuadratic_eq_coe_local {m : ℕ} {P : ProblemData m}
    {M : ℝ} {x y : EuclideanSpace m}
    (hx : x ∈ ERealFunction.effectiveDom P.objective) :
    objectiveWithQuadratic P M x y =
      (((P.objective x).toReal + M * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
  rcases (ERealFunction.mem_effectiveDom_iff_exists_real P.objective x).mp hx with ⟨r, hr⟩
  unfold objectiveWithQuadratic erealAddReal
  rw [hr]
  change ((r : EReal) + ((M * ‖x - y‖ ^ 2 : ℝ) : EReal) =
    ((r + M * ‖x - y‖ ^ 2 : ℝ) : EReal))
  rw [← EReal.coe_add]

theorem objective_le_objectiveWithQuadratic_of_nonneg_local {m : ℕ}
    {P : ProblemData m} {M : ℝ} {x y : EuclideanSpace m}
    (hM : 0 ≤ M) (hx : x ∈ ERealFunction.effectiveDom P.objective) :
    P.objective x ≤ objectiveWithQuadratic P M x y := by
  have hobj_coe :
      P.objective x = (((P.objective x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal
      ((ERealFunction.mem_effectiveDom_iff P.objective x).mp hx).1
      ((ERealFunction.mem_effectiveDom_iff P.objective x).mp hx).2).symm
  have hquad := objectiveWithQuadratic_eq_coe_local (P := P) (M := M) (x := x) (y := y) hx
  rw [hobj_coe, hquad]
  exact EReal.coe_le_coe_iff.mpr (by
    have hnonneg : 0 ≤ M * ‖x - y‖ ^ 2 := mul_nonneg hM (sq_nonneg _)
    nlinarith)

theorem p_objective_uniform_upper_tail {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → P.objective (A.p n) ≤ (C : EReal) := by
  rcases hchosen with ⟨hnu, hmu, _hstrict, hM2ltM1⟩
  let M1 : ℝ := A.M1 nu mu
  let M2 : ℝ := A.M2 nu mu
  let H : ℕ → EReal := fun n ↦ objectiveWithQuadratic P M2 (A.p n) (A.x n)
  have hM2_nonneg : 0 ≤ M2 := by
    dsimp [M2]
    exact m2_nonneg_local A hnu hmu
  have hstep : ∀ n : ℕ, 2 ≤ n → H n ≤ H (n - 1) := by
    intro n hn
    dsimp [H, M1, M2]
    exact le_trans
      (objectiveWithQuadratic_mono_coeff_local P (le_of_lt hM2ltM1) (A.p n) (A.x n))
      (lemma_3_2_descent A nu mu hnu hmu n hn)
  have hH_le_one : ∀ n : ℕ, 1 ≤ n → H n ≤ H 1 := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro hn
        by_cases h1 : n + 1 = 1
        · simpa [h1]
        · have htwo : 2 ≤ n + 1 := by omega
          have hn_pos : 1 ≤ n := by omega
          have hpred : n + 1 - 1 = n := by omega
          calc
            H (n + 1) ≤ H (n + 1 - 1) := hstep (n + 1) htwo
            _ = H n := by rw [hpred]
            _ ≤ H 1 := ih hn_pos
  let C : ℝ := (H 1).toReal
  have hH1_coe : H 1 = (C : EReal) := by
    have hp_eff : A.p 1 ∈ ERealFunction.effectiveDom P.objective :=
      p_objective_effectiveDom_local A (by omega)
    dsimp [C, H]
    rw [objectiveWithQuadratic_eq_coe_local (P := P) (M := M2)
      (x := A.p 1) (y := A.x 1) hp_eff]
    rw [EReal.toReal_coe]
  refine ⟨C, ?_⟩
  intro n hn
  have hp_eff : A.p n ∈ ERealFunction.effectiveDom P.objective :=
    p_objective_effectiveDom_local A hn
  calc
    P.objective (A.p n)
        ≤ H n := by
          dsimp [H, M2]
          exact objective_le_objectiveWithQuadratic_of_nonneg_local hM2_nonneg hp_eff
    _ ≤ H 1 := hH_le_one n hn
    _ = (C : EReal) := hH1_coe

theorem p_range_bounded_of_coercive {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective) :
    Bornology.IsBounded (Set.range A.p) := by
  rcases p_objective_uniform_upper_tail A nu mu hchosen with ⟨C, hC⟩
  let tailSet : Set (EuclideanSpace m) := {p | ∃ n : ℕ, 1 ≤ n ∧ p = A.p n}
  have htail_subset : tailSet ⊆ ERealFunction.lowerLevelSet P.objective C := by
    intro p hp
    rcases hp with ⟨n, hn, rfl⟩
    simpa [ERealFunction.lowerLevelSet] using hC n hn
  have htail_bounded : Bornology.IsBounded tailSet :=
    (hcoercive C).subset htail_subset
  have hsingleton : Bornology.IsBounded ({A.p 0} : Set (EuclideanSpace m)) :=
    Bornology.isBounded_singleton
  have hunion_bounded : Bornology.IsBounded ({A.p 0} ∪ tailSet : Set (EuclideanSpace m)) :=
    hsingleton.union htail_bounded
  have hrange_subset : Set.range A.p ⊆ ({A.p 0} ∪ tailSet : Set (EuclideanSpace m)) := by
    rintro y ⟨n, rfl⟩
    by_cases hn0 : n = 0
    · left
      simp [hn0]
    · right
      refine ⟨n, ?_, rfl⟩
      omega
  exact hunion_bounded.subset hrange_subset

theorem cluster_subseq_ge_two {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {pstar : EuclideanSpace m}
    (hpstar : pstar ∈ omega A.p) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (∀ k, 2 ≤ ψ k) ∧
      Tendsto (A.p ∘ ψ) atTop (nhds pstar) := by
  rcases IsSequentialClusterPt.exists_subseq_tendsto (by simpa [omega] using hpstar) with
    ⟨φ, hφ_mono, hφ_tendsto⟩
  refine ⟨fun k ↦ φ (k + 2), ?_, ?_, ?_⟩
  · intro i j hij
    exact hφ_mono (by omega)
  · intro k
    have hge : k + 2 ≤ φ (k + 2) := StrictMono.id_le hφ_mono (k + 2)
    exact le_trans (by omega : 2 ≤ k + 2) hge
  · have hshift : Tendsto (fun k : ℕ ↦ k + 2) atTop atTop :=
      tendsto_add_atTop_nat 2
    simpa [Function.comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hφ_tendsto.comp hshift

theorem tendsto_x_of_p_subseq {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {pstar : EuclideanSpace m} {ψ : ℕ → ℕ}
    (hxp_sum : Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖ ^ 2))
    (hψ_tendsto : Tendsto (A.p ∘ ψ) atTop (nhds pstar))
    (hψ_mono : StrictMono ψ) :
    Tendsto (fun k : ℕ ↦ A.x (ψ k)) atTop (nhds pstar) := by
  have hxp_norm :
      Tendsto (fun n : ℕ ↦ ‖A.x n - A.p n‖) atTop (nhds 0) :=
    tendsto_norm_of_summable_norm_sq (z := fun n ↦ A.x n - A.p n) hxp_sum
  have hxp_vec :
      Tendsto (fun n : ℕ ↦ A.x n - A.p n) atTop
        (nhds (0 : EuclideanSpace m)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hxp_norm
  have hxp_sub :
      Tendsto (fun k : ℕ ↦ A.x (ψ k) - A.p (ψ k)) atTop
        (nhds (0 : EuclideanSpace m)) :=
    hxp_vec.comp (StrictMono.tendsto_atTop hψ_mono)
  have hsum :
      Tendsto (fun k : ℕ ↦ (A.x (ψ k) - A.p (ψ k)) + A.p (ψ k))
        atTop (nhds ((0 : EuclideanSpace m) + pstar)) :=
    hxp_sub.add hψ_tendsto
  simpa [Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using hsum

theorem ereal_bounded_limit_finite {z : ℕ → EReal} {l : EReal}
    {C_low C_high : ℝ}
    (hz_low : ∀ n, (C_low : EReal) ≤ z n)
    (hz_high : ∀ n, 1 ≤ n → z n ≤ (C_high : EReal))
    (hz_tendsto : Tendsto z atTop (nhds l)) :
    l ≠ ⊤ ∧ l ≠ ⊥ := by
  constructor
  · intro hl_top
    have hnhds : Set.Ioi (C_high : EReal) ∈ nhds l := by
      rw [hl_top]
      exact (isOpen_Ioi.mem_nhds (EReal.coe_lt_top C_high))
    rcases Filter.eventually_atTop.mp (hz_tendsto hnhds) with ⟨N1, hN1⟩
    let N := max 1 N1
    have hgt : (C_high : EReal) < z N := hN1 N (le_max_right _ _)
    have hle : z N ≤ (C_high : EReal) := hz_high N (le_max_left _ _)
    exact (not_lt_of_ge hle) hgt
  · intro hl_bot
    have hnhds : Set.Iio (C_low : EReal) ∈ nhds l := by
      rw [hl_bot]
      exact (isOpen_Iio.mem_nhds (EReal.bot_lt_coe C_low))
    rcases Filter.eventually_atTop.mp (hz_tendsto hnhds) with ⟨N, hN⟩
    have hlt : z N < (C_low : EReal) := hN N le_rfl
    have hle : (C_low : EReal) ≤ z N := hz_low N
    exact (not_lt_of_ge hle) hlt

theorem subgradientEstimate_tendsto_zero {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P)
    (hxp_sum : Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖ ^ 2)) :
    Tendsto (fun n : ℕ ↦ subgradientEstimateVector A n) atTop
      (nhds (0 : EuclideanSpace m)) := by
  have hxp_norm :
      Tendsto (fun n : ℕ ↦ ‖A.x n - A.p n‖) atTop (nhds 0) :=
    tendsto_norm_of_summable_norm_sq (z := fun n ↦ A.x n - A.p n) hxp_sum
  have hxp_vec :
      Tendsto (fun n : ℕ ↦ A.x n - A.p n) atTop
        (nhds (0 : EuclideanSpace m)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hxp_norm
  let K1 : ℝ := A.Lgrad_u / A.lambdaLower + P.Lgrad_h
  let K2 : ℝ := (A.alpha / A.lambdaLower) * (1 + A.lambdaUpper * P.Lgrad_h)
  have hshift_atTop : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    exact ⟨N + 1, by intro n hn; omega⟩
  have hxp_norm_shift :
      Tendsto (fun n : ℕ ↦ ‖A.x (n - 1) - A.p (n - 1)‖) atTop (nhds 0) :=
    hxp_norm.comp hshift_atTop
  have hK1_bound (n : ℕ) (hn : 2 ≤ n) :
      A.Lgrad_u / A.lambda n + P.Lgrad_h ≤ K1 := by
    have hn1 : 1 ≤ n := by omega
    have hlam_lower : A.lambdaLower ≤ A.lambda n := (A.lambda_bounds n hn1).1
    have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam_lower
    have hLu_nonneg : 0 ≤ A.Lgrad_u := le_of_lt A.u_Lgrad_pos
    have hdiv : A.Lgrad_u / A.lambda n ≤ A.Lgrad_u / A.lambdaLower := by
      exact div_le_div_of_nonneg_left hLu_nonneg A.lambdaLower_pos hlam_lower
    dsimp [K1]
    linarith
  have hK2_bound (n : ℕ) (hn : 2 ≤ n) :
      (A.alphaSeq n / A.lambda n) * (1 + A.lambda (n - 1) * P.Lgrad_h) ≤ K2 := by
    have hn1 : 1 ≤ n := by omega
    have hpred1 : 1 ≤ n - 1 := by omega
    have halpha_nonneg : 0 ≤ A.alphaSeq n := (A.alpha_bounds n hn1).1
    have halpha_le : A.alphaSeq n ≤ A.alpha := (A.alpha_bounds n hn1).2
    have hlam_lower : A.lambdaLower ≤ A.lambda n := (A.lambda_bounds n hn1).1
    have hlam_pos : 0 < A.lambda n := lt_of_lt_of_le A.lambdaLower_pos hlam_lower
    have hlampred_upper : A.lambda (n - 1) ≤ A.lambdaUpper :=
      (A.lambda_bounds (n - 1) hpred1).2
    have hLh_nonneg : 0 ≤ P.Lgrad_h := P.h_lipschitz_gradient.1
    have hfactor_nonneg : 0 ≤ 1 + A.lambda (n - 1) * P.Lgrad_h := by
      have hlampred_nonneg : 0 ≤ A.lambda (n - 1) :=
        le_trans (le_of_lt A.lambdaLower_pos) (A.lambda_bounds (n - 1) hpred1).1
      nlinarith [mul_nonneg hlampred_nonneg hLh_nonneg]
    have hfactor_le : 1 + A.lambda (n - 1) * P.Lgrad_h ≤
        1 + A.lambdaUpper * P.Lgrad_h := by
      nlinarith [mul_le_mul_of_nonneg_right hlampred_upper hLh_nonneg]
    have halpha_div_le : A.alphaSeq n / A.lambda n ≤ A.alpha / A.lambdaLower := by
      have hinv_le : (A.lambda n)⁻¹ ≤ (A.lambdaLower)⁻¹ :=
        inv_anti₀ A.lambdaLower_pos hlam_lower
      have h_alpha_inv_le : A.alphaSeq n * (A.lambda n)⁻¹ ≤
          A.alphaSeq n * (A.lambdaLower)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv_le halpha_nonneg
      have h_alpha_upper : A.alphaSeq n * (A.lambdaLower)⁻¹ ≤
          A.alpha * (A.lambdaLower)⁻¹ :=
        mul_le_mul_of_nonneg_right halpha_le (inv_nonneg.mpr (le_of_lt A.lambdaLower_pos))
      simpa [div_eq_mul_inv] using le_trans h_alpha_inv_le h_alpha_upper
    have halphadiv_nonneg : 0 ≤ A.alphaSeq n / A.lambda n :=
      div_nonneg halpha_nonneg (le_of_lt hlam_pos)
    have halphadiv_upper_nonneg : 0 ≤ A.alpha / A.lambdaLower := by
      exact div_nonneg A.alpha_nonneg (le_of_lt A.lambdaLower_pos)
    dsimp [K2]
    exact mul_le_mul halpha_div_le hfactor_le hfactor_nonneg halphadiv_upper_nonneg
  have hnorm_bound (n : ℕ) (hn : 2 ≤ n) :
      ‖subgradientEstimateVector A n‖ ≤
        K1 * ‖A.x n - A.p n‖ + K2 * ‖A.x (n - 1) - A.p (n - 1)‖ := by
    have hlem := (lemma_3_5_subgradient_estimate A n hn).2
    refine le_trans hlem ?_
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (hK1_bound n hn) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_right (hK2_bound n hn) (norm_nonneg _)
  have hg_tendsto :
      Tendsto
        (fun n : ℕ ↦
          K1 * ‖A.x n - A.p n‖ + K2 * ‖A.x (n - 1) - A.p (n - 1)‖)
        atTop (nhds 0) := by
    have h1 :
        Tendsto (fun n : ℕ ↦ K1 * ‖A.x n - A.p n‖) atTop (nhds (K1 * 0)) :=
      Tendsto.const_mul K1 hxp_norm
    have h2 :
        Tendsto (fun n : ℕ ↦ K2 * ‖A.x (n - 1) - A.p (n - 1)‖) atTop
          (nhds (K2 * 0)) :=
      Tendsto.const_mul K2 hxp_norm_shift
    simpa using h1.add h2
  have hnorm_tendsto :
      Tendsto (fun n : ℕ ↦ ‖subgradientEstimateVector A n‖) atTop (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall (fun n ↦ norm_nonneg _)) ?_ hg_tendsto
    exact eventually_atTop.2 ⟨2, fun n hn ↦ hnorm_bound n hn⟩
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto

theorem pstar_effectiveDom_of_cluster {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu)
    (hboundedBelow :
      ∃ C : ℝ, ∀ x : EuclideanSpace m, (C : EReal) ≤ P.objective x)
    (hobj_conv : ∃ l_obj : EReal,
      Tendsto (fun n : ℕ ↦ P.objective (A.p n)) atTop (nhds l_obj))
    {pstar : EuclideanSpace m} {ψ : ℕ → ℕ} (hψ_mono : StrictMono ψ)
    (hψ_tendsto : Tendsto (A.p ∘ ψ) atTop (nhds pstar)) :
    pstar ∈ ERealFunction.effectiveDom P.objective := by
  rcases hobj_conv with ⟨l_obj, hl_obj_tendsto⟩
  rcases hboundedBelow with ⟨C_low, hC_low⟩
  rcases p_objective_uniform_upper_tail A nu mu hchosen with ⟨C_high, hC_high⟩
  have hl_obj_finite : l_obj ≠ ⊤ ∧ l_obj ≠ ⊥ := by
    exact ereal_bounded_limit_finite
      (z := fun n : ℕ ↦ P.objective (A.p n)) (l := l_obj)
      (C_low := C_low) (C_high := C_high)
      (fun n ↦ hC_low (A.p n)) hC_high hl_obj_tendsto
  have hsubseq_tendsto :
      Tendsto (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop (nhds l_obj) :=
    hl_obj_tendsto.comp (StrictMono.tendsto_atTop hψ_mono)
  have hobj_le_lobj : P.objective pstar ≤ l_obj := by
    have h_lsc_at : LowerSemicontinuousAt P.objective pstar :=
      (objective_lowerSemicontinuous P) pstar
    calc
      P.objective pstar ≤ Filter.liminf P.objective (nhds pstar) :=
        h_lsc_at.le_liminf
      _ ≤ Filter.liminf (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop :=
        hψ_tendsto.liminf_le_liminf_comp
      _ = l_obj := hsubseq_tendsto.liminf_eq
  have hp_ne_top : P.objective pstar ≠ ⊤ := by
    intro htop
    rw [htop] at hobj_le_lobj
    exact hl_obj_finite.1 (top_le_iff.mp hobj_le_lobj)
  have hp_ne_bot : P.objective pstar ≠ ⊥ := by
    intro hbot
    have hlow : (C_low : EReal) ≤ P.objective pstar := hC_low pstar
    rw [hbot] at hlow
    exact EReal.coe_ne_bot C_low (le_bot_iff.mp hlow)
  rw [ERealFunction.mem_effectiveDom_iff]
  exact ⟨hp_ne_top, hp_ne_bot⟩

theorem objective_tendsto_of_cluster_subsequence {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {pstar : EuclideanSpace m}
    (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu)
    (hxp_sum : Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖ ^ 2))
    (hxx_sum : Summable (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖ ^ 2))
    (hboundedBelow :
      ∃ C : ℝ, ∀ x : EuclideanSpace m, (C : EReal) ≤ P.objective x)
    (hobj_conv : ∃ l_obj : EReal,
      Tendsto (fun n : ℕ ↦ P.objective (A.p n)) atTop (nhds l_obj))
    {ψ : ℕ → ℕ} (hψ_mono : StrictMono ψ) (hψ_ge_two : ∀ k, 2 ≤ ψ k)
    (hψ_tendsto : Tendsto (A.p ∘ ψ) atTop (nhds pstar))
    (hx_tendsto : Tendsto (fun k : ℕ ↦ A.x (ψ k)) atTop (nhds pstar)) :
    Tendsto (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop
      (nhds (P.objective pstar)) := by
  have hpstar_eff : pstar ∈ ERealFunction.effectiveDom P.objective :=
    pstar_effectiveDom_of_cluster A nu mu hchosen hboundedBelow hobj_conv
      hψ_mono hψ_tendsto
  rcases hobj_conv with ⟨l_obj, hl_obj_tendsto⟩
  have hsubseq_to_lobj :
      Tendsto (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop (nhds l_obj) :=
    hl_obj_tendsto.comp (StrictMono.tendsto_atTop hψ_mono)
  have hobj_le_lobj : P.objective pstar ≤ l_obj := by
    have h_lsc_at : LowerSemicontinuousAt P.objective pstar :=
      (objective_lowerSemicontinuous P) pstar
    calc
      P.objective pstar ≤ Filter.liminf P.objective (nhds pstar) :=
        h_lsc_at.le_liminf
      _ ≤ Filter.liminf (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop :=
        hψ_tendsto.liminf_le_liminf_comp
      _ = l_obj := hsubseq_to_lobj.liminf_eq
  have hlobj_le_obj : l_obj ≤ P.objective pstar := by
    have hpstar_eff_f : pstar ∈ ERealFunction.effectiveDom P.f :=
      (objectiveSum_effectiveDom_iff_local P.f P.h pstar).mp hpstar_eff
    have hpk_eff_obj (k : ℕ) :
        A.p (ψ k) ∈ ERealFunction.effectiveDom P.objective := by
      exact p_objective_effectiveDom_local A (by
        have h2 : 2 ≤ ψ k := hψ_ge_two k
        omega)
    have hpk_eff_f (k : ℕ) :
        A.p (ψ k) ∈ ERealFunction.effectiveDom P.f :=
      (objectiveSum_effectiveDom_iff_local P.f P.h (A.p (ψ k))).mp (hpk_eff_obj k)
    let φ : ℕ → EuclideanSpace m → ℝ := fun n y ↦
      (1 / A.lambda n) * bregmanDistance A.u y (A.x n) +
        inner ℝ y (gradient P.h (A.x n)) +
        (A.alphaSeq n / A.lambda n) * inner ℝ y (A.x (n - 1) - A.x n)
    have h_argmin (k : ℕ) :
        algorithmStepObjective P A.u A.lambda A.alphaSeq A.x (ψ k) (A.p (ψ k))
          ≤ algorithmStepObjective P A.u A.lambda A.alphaSeq A.x (ψ k) pstar := by
      have hn1 : 1 ≤ ψ k := by
        have h2 : 2 ≤ ψ k := hψ_ge_two k
        omega
      have hmem := A.p_argmin (ψ k) hn1
      have hmin := (mem_argminSet_iff
        (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x (ψ k))
        (A.p (ψ k))).mp hmem
      rw [hmin]
      exact sInf_le (s := Set.range
        (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x (ψ k)))
        (Set.mem_range_self pstar)
    have h_argmin_ereal (k : ℕ) :
        erealAddReal (P.f (A.p (ψ k))) (φ (ψ k) (A.p (ψ k)))
          ≤ erealAddReal (P.f pstar) (φ (ψ k) pstar) := by
      simpa [algorithmStepObjective, φ] using h_argmin k
    have h_finite_k (k : ℕ) :
        P.f (A.p (ψ k)) ≠ ⊤ ∧ P.f (A.p (ψ k)) ≠ ⊥ :=
      (ERealFunction.mem_effectiveDom_iff P.f (A.p (ψ k))).mp (hpk_eff_f k)
    have h_finite_pstar : P.f pstar ≠ ⊤ ∧ P.f pstar ≠ ⊥ :=
      (ERealFunction.mem_effectiveDom_iff P.f pstar).mp hpstar_eff_f
    have h_ereal_to_real (k : ℕ) :
        (P.f (A.p (ψ k))).toReal + φ (ψ k) (A.p (ψ k))
          ≤ (P.f pstar).toReal + φ (ψ k) pstar := by
      have hineq := h_argmin_ereal k
      rw [erealAddReal_eq_add, erealAddReal_eq_add] at hineq
      have hcoef1 :
          P.f (A.p (ψ k)) =
            (((P.f (A.p (ψ k))).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (h_finite_k k).1 (h_finite_k k).2).symm
      have hcoef2 :
          P.f pstar = (((P.f pstar).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal h_finite_pstar.1 h_finite_pstar.2).symm
      rw [hcoef1, hcoef2] at hineq
      exact EReal.coe_le_coe_iff.mp hineq
    have h_obj_toReal_eq (y : EuclideanSpace m)
        (hy : y ∈ ERealFunction.effectiveDom P.f) :
        (P.objective y).toReal = (P.f y).toReal + P.h y := by
      rcases (ERealFunction.mem_effectiveDom_iff_exists_real P.f y).mp hy with ⟨r, hr⟩
      unfold ProblemData.objective objectiveSum
      rw [hr]
      rw [erealAddReal_eq_add]
      have hsum : ((r : EReal) + ((P.h y : ℝ) : EReal)) =
          (((r + P.h y : ℝ) : ℝ) : EReal) := by
        rw [← EReal.coe_add]
      rw [hsum]
      simpa using (EReal.toReal_coe (r + P.h y))
    have h_f_toReal_sub (y : EuclideanSpace m)
        (hy : y ∈ ERealFunction.effectiveDom P.f) :
        (P.f y).toReal = (P.objective y).toReal - P.h y := by
      have h := h_obj_toReal_eq y hy
      linarith
    have h_objective_ineq (k : ℕ) :
        (P.objective (A.p (ψ k))).toReal
          ≤ (P.objective pstar).toReal
            + (P.h (A.p (ψ k)) - P.h pstar
              + φ (ψ k) pstar - φ (ψ k) (A.p (ψ k))) := by
      have h := h_ereal_to_real k
      rw [h_f_toReal_sub (A.p (ψ k)) (hpk_eff_f k),
        h_f_toReal_sub pstar hpstar_eff_f] at h
      linarith
    have hl_obj_finite : l_obj ≠ ⊤ ∧ l_obj ≠ ⊥ := by
      rcases hboundedBelow with ⟨C_low, hC_low⟩
      rcases p_objective_uniform_upper_tail A nu mu hchosen with ⟨C_high, hC_high⟩
      exact ereal_bounded_limit_finite
        (z := fun n : ℕ ↦ P.objective (A.p n)) (l := l_obj)
        (C_low := C_low) (C_high := C_high)
        (fun n ↦ hC_low (A.p n)) hC_high hl_obj_tendsto
    have hpstar_obj_fin : P.objective pstar ≠ ⊤ ∧ P.objective pstar ≠ ⊥ :=
      (ERealFunction.mem_effectiveDom_iff P.objective pstar).mp hpstar_eff
    have h_subseq_real :
        Tendsto (fun k : ℕ ↦ (P.objective (A.p (ψ k))).toReal) atTop
          (nhds l_obj.toReal) :=
      (EReal.tendsto_toReal hl_obj_finite.1 hl_obj_finite.2).comp hsubseq_to_lobj
    have h_error :
        Tendsto
          (fun k : ℕ ↦
            P.h (A.p (ψ k)) - P.h pstar + φ (ψ k) pstar -
              φ (ψ k) (A.p (ψ k))) atTop (nhds 0) := by
      have h_term_h :
          Tendsto (fun k : ℕ ↦ P.h (A.p (ψ k)) - P.h pstar) atTop (nhds 0) := by
        have hh :
            Tendsto (fun k : ℕ ↦ P.h (A.p (ψ k))) atTop (nhds (P.h pstar)) :=
          (P.h_frechet_differentiable.continuous.tendsto pstar).comp hψ_tendsto
        simpa [sub_self] using
          hh.sub
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ ↦ P.h pstar) atTop (nhds (P.h pstar)))
      -- Remaining analytic estimate from the paper: after expanding `φ`, the
      -- two Bregman terms are bounded by squared norms via
      -- `algorithm_bregman_bounds`; the gradient inner product vanishes by
      -- continuity/boundedness of `gradient P.h`; the inertial inner product
      -- vanishes using `hxp_sum`, `hxx_sum`, and `ψ k - 1 → ∞`.
      have hxp_norm :
          Tendsto (fun n : ℕ ↦ ‖A.x n - A.p n‖) atTop (nhds 0) :=
        tendsto_norm_of_summable_norm_sq (z := fun n ↦ A.x n - A.p n) hxp_sum
      have hxx_norm :
          Tendsto (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖) atTop (nhds 0) :=
        tendsto_norm_of_summable_norm_sq
          (z := fun n ↦ A.x (n + 1) - A.x n) hxx_sum
      have hxp_norm_subseq :
          Tendsto (fun k : ℕ ↦ ‖A.x (ψ k) - A.p (ψ k)‖) atTop (nhds 0) :=
        hxp_norm.comp (StrictMono.tendsto_atTop hψ_mono)
      have hp_norm_subseq :
          Tendsto (fun k : ℕ ↦ ‖pstar - A.p (ψ k)‖) atTop (nhds 0) := by
        have hp_vec :
            Tendsto (fun k : ℕ ↦ pstar - (A.p ∘ ψ) k) atTop
              (nhds (pstar - pstar)) :=
          tendsto_const_nhds.sub hψ_tendsto
        simpa [Function.comp] using hp_vec.norm
      have hx_norm_subseq :
          Tendsto (fun k : ℕ ↦ ‖pstar - A.x (ψ k)‖) atTop (nhds 0) := by
        have hx_vec :
            Tendsto (fun k : ℕ ↦ pstar - A.x (ψ k)) atTop
              (nhds (pstar - pstar)) :=
          tendsto_const_nhds.sub hx_tendsto
        simpa using hx_vec.norm
      have hxx_shift_subseq :
          Tendsto (fun k : ℕ ↦ ‖A.x (ψ k - 1) - A.x (ψ k)‖) atTop (nhds 0) := by
        have hshift_atTop : Tendsto (fun k : ℕ ↦ ψ k - 1) atTop atTop := by
          rw [tendsto_atTop_atTop]
          intro N
          have hψ_atTop := StrictMono.tendsto_atTop hψ_mono
          rw [tendsto_atTop_atTop] at hψ_atTop
          rcases hψ_atTop (N + 1) with ⟨K, hK⟩
          exact ⟨K, by
            intro k hk
            have hψN : N + 1 ≤ ψ k := hK k hk
            omega⟩
        have hxx' :
            Tendsto (fun n : ℕ ↦ ‖A.x n - A.x (n + 1)‖) atTop (nhds 0) := by
          simpa [norm_sub_rev] using hxx_norm
        have hcomp := hxx'.comp hshift_atTop
        have hidx : ∀ᶠ k in atTop,
            ‖A.x (ψ k - 1) - A.x ((ψ k - 1) + 1)‖ =
              ‖A.x (ψ k - 1) - A.x (ψ k)‖ := by
          exact Eventually.of_forall (fun k ↦ by
            have h2 : 2 ≤ ψ k := hψ_ge_two k
            congr
            omega)
        exact hcomp.congr' hidx
      have hlambda_inv_bound (k : ℕ) :
          0 ≤ 1 / A.lambda (ψ k) ∧ 1 / A.lambda (ψ k) ≤ 1 / A.lambdaLower := by
        have hn1 : 1 ≤ ψ k := by have h2 := hψ_ge_two k; omega
        have hlam_lower := (A.lambda_bounds (ψ k) hn1).1
        have hlam_pos : 0 < A.lambda (ψ k) := lt_of_lt_of_le A.lambdaLower_pos hlam_lower
        constructor
        · exact div_nonneg zero_le_one (le_of_lt hlam_pos)
        · exact one_div_le_one_div_of_le A.lambdaLower_pos hlam_lower
      have h_bregman :
          Tendsto
            (fun k : ℕ ↦
              (1 / A.lambda (ψ k)) *
                (bregmanDistance A.u pstar (A.x (ψ k)) -
                  bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k)))) atTop
            (nhds 0) := by
        let C : ℝ := (A.Lgrad_u / 2) * (1 / A.lambdaLower)
        have hC_nonneg : 0 ≤ C := by
          dsimp [C]
          exact mul_nonneg
            (div_nonneg (le_of_lt A.u_Lgrad_pos) (by norm_num))
            (div_nonneg zero_le_one (le_of_lt A.lambdaLower_pos))
        have hbound (k : ℕ) :
            |(1 / A.lambda (ψ k)) *
                (bregmanDistance A.u pstar (A.x (ψ k)) -
                  bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k)))| ≤
              C * ‖pstar - A.x (ψ k)‖ ^ 2 +
                C * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2 := by
          have hD1_nonneg : 0 ≤ bregmanDistance A.u pstar (A.x (ψ k)) := by
            have hlower := (algorithm_bregman_bounds A pstar (A.x (ψ k))).1
            have hsigma_nonneg : 0 ≤ A.sigma := le_of_lt A.u_strongly_convex.1
            exact le_trans (mul_nonneg (div_nonneg hsigma_nonneg (by norm_num)) (sq_nonneg _)) hlower
          have hD2_nonneg : 0 ≤ bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k)) := by
            have hlower := (algorithm_bregman_bounds A (A.p (ψ k)) (A.x (ψ k))).1
            have hsigma_nonneg : 0 ≤ A.sigma := le_of_lt A.u_strongly_convex.1
            exact le_trans (mul_nonneg (div_nonneg hsigma_nonneg (by norm_num)) (sq_nonneg _)) hlower
          have hD1_upper := (algorithm_bregman_bounds A pstar (A.x (ψ k))).2
          have hD2_upper := (algorithm_bregman_bounds A (A.p (ψ k)) (A.x (ψ k))).2
          have hinv_nonneg := (hlambda_inv_bound k).1
          have hinv_upper := (hlambda_inv_bound k).2
          calc
            |(1 / A.lambda (ψ k)) *
                (bregmanDistance A.u pstar (A.x (ψ k)) -
                  bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k)))|
                ≤ (1 / A.lambda (ψ k)) *
                    (bregmanDistance A.u pstar (A.x (ψ k)) +
                      bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k))) := by
                  rw [abs_mul]
                  rw [abs_of_nonneg hinv_nonneg]
                  exact mul_le_mul_of_nonneg_left
                    (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩) hinv_nonneg
            _ ≤ (1 / A.lambdaLower) *
                    ((A.Lgrad_u / 2) * ‖pstar - A.x (ψ k)‖ ^ 2 +
                      (A.Lgrad_u / 2) * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2) := by
                  have hsum_nonneg : 0 ≤
                      bregmanDistance A.u pstar (A.x (ψ k)) +
                        bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k)) :=
                    add_nonneg hD1_nonneg hD2_nonneg
                  have hsum_upper :
                      bregmanDistance A.u pstar (A.x (ψ k)) +
                        bregmanDistance A.u (A.p (ψ k)) (A.x (ψ k)) ≤
                        (A.Lgrad_u / 2) * ‖pstar - A.x (ψ k)‖ ^ 2 +
                          (A.Lgrad_u / 2) * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2 :=
                    add_le_add hD1_upper hD2_upper
                  have hright_nonneg : 0 ≤
                      (A.Lgrad_u / 2) * ‖pstar - A.x (ψ k)‖ ^ 2 +
                        (A.Lgrad_u / 2) * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2 := by
                    have hLu : 0 ≤ A.Lgrad_u := le_of_lt A.u_Lgrad_pos
                    positivity
                  exact le_trans
                    (mul_le_mul_of_nonneg_left hsum_upper hinv_nonneg)
                    (mul_le_mul_of_nonneg_right hinv_upper hright_nonneg)
            _ = C * ‖pstar - A.x (ψ k)‖ ^ 2 +
                    C * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2 := by
                  ring
        have hlim :
            Tendsto
              (fun k : ℕ ↦
                C * ‖pstar - A.x (ψ k)‖ ^ 2 +
                  C * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2) atTop (nhds 0) := by
          have h1 := (hx_norm_subseq.pow 2).const_mul C
          have h2 : Tendsto (fun k : ℕ ↦ C * ‖A.p (ψ k) - A.x (ψ k)‖ ^ 2)
              atTop (nhds (C * 0)) := by
            simpa [norm_sub_rev] using (hxp_norm_subseq.pow 2).const_mul C
          simpa using h1.add h2
        refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
        simpa [Real.norm_eq_abs] using
          squeeze_zero' (Eventually.of_forall (fun k ↦ abs_nonneg _))
            (Eventually.of_forall hbound) hlim
      have h_grad_diff :
          Tendsto (fun k : ℕ ↦ gradient P.h (A.x (ψ k)) - gradient P.h pstar)
            atTop (nhds (0 : EuclideanSpace m)) := by
        refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
        have hbound (k : ℕ) :
            ‖gradient P.h (A.x (ψ k)) - gradient P.h pstar‖ ≤
              P.Lgrad_h * ‖A.x (ψ k) - pstar‖ :=
          P.h_lipschitz_gradient.2.2 (A.x (ψ k)) pstar
        have hlim : Tendsto (fun k : ℕ ↦ P.Lgrad_h * ‖A.x (ψ k) - pstar‖)
            atTop (nhds 0) := by
          have hx' : Tendsto (fun k : ℕ ↦ ‖A.x (ψ k) - pstar‖) atTop (nhds 0) := by
            simpa [norm_sub_rev] using hx_norm_subseq
          simpa using hx'.const_mul P.Lgrad_h
        refine squeeze_zero' (Eventually.of_forall (fun k ↦ norm_nonneg _))
          (Eventually.of_forall hbound) hlim
      have h_grad :
          Tendsto (fun k : ℕ ↦ gradient P.h (A.x (ψ k))) atTop
            (nhds (gradient P.h pstar)) := by
        have hconst :
            Tendsto (fun _ : ℕ ↦ gradient P.h pstar) atTop
              (nhds (gradient P.h pstar)) :=
          tendsto_const_nhds
        have hsum := h_grad_diff.add hconst
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
      have h_grad_ip :
          Tendsto (fun k : ℕ ↦
            inner ℝ (pstar - A.p (ψ k)) (gradient P.h (A.x (ψ k)))) atTop
            (nhds 0) := by
        have hp_vec :
            Tendsto (fun k : ℕ ↦ pstar - A.p (ψ k)) atTop
              (nhds (0 : EuclideanSpace m)) := by
          have hp :
              Tendsto (fun k : ℕ ↦ pstar - (A.p ∘ ψ) k) atTop
                (nhds (pstar - pstar)) :=
            tendsto_const_nhds.sub hψ_tendsto
          simpa [Function.comp] using hp
        simpa using hp_vec.inner h_grad
      have hcoeff_bound (k : ℕ) :
          |A.alphaSeq (ψ k) / A.lambda (ψ k)| ≤ A.alpha / A.lambdaLower := by
        have hn1 : 1 ≤ ψ k := by have h2 := hψ_ge_two k; omega
        have halpha_nonneg := (A.alpha_bounds (ψ k) hn1).1
        have halpha_le := (A.alpha_bounds (ψ k) hn1).2
        have hlam_lower := (A.lambda_bounds (ψ k) hn1).1
        have hlam_pos : 0 < A.lambda (ψ k) := lt_of_lt_of_le A.lambdaLower_pos hlam_lower
        have hdiv_nonneg : 0 ≤ A.alphaSeq (ψ k) / A.lambda (ψ k) :=
          div_nonneg halpha_nonneg (le_of_lt hlam_pos)
        rw [abs_of_nonneg hdiv_nonneg]
        have hinv_le : (A.lambda (ψ k))⁻¹ ≤ (A.lambdaLower)⁻¹ :=
          inv_anti₀ A.lambdaLower_pos hlam_lower
        have h1 :
            A.alphaSeq (ψ k) * (A.lambda (ψ k))⁻¹ ≤
              A.alphaSeq (ψ k) * (A.lambdaLower)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv_le halpha_nonneg
        have h2 :
            A.alphaSeq (ψ k) * (A.lambdaLower)⁻¹ ≤
              A.alpha * (A.lambdaLower)⁻¹ :=
          mul_le_mul_of_nonneg_right halpha_le
            (inv_nonneg.mpr (le_of_lt A.lambdaLower_pos))
        simpa [div_eq_mul_inv] using le_trans h1 h2
      have h_inertial_ip :
          Tendsto (fun k : ℕ ↦
            (A.alphaSeq (ψ k) / A.lambda (ψ k)) *
              inner ℝ (pstar - A.p (ψ k)) (A.x (ψ k - 1) - A.x (ψ k)))
            atTop (nhds 0) := by
        have hxstep_vec :
            Tendsto (fun k : ℕ ↦ A.x (ψ k - 1) - A.x (ψ k)) atTop
              (nhds (0 : EuclideanSpace m)) :=
          tendsto_zero_iff_norm_tendsto_zero.mpr hxx_shift_subseq
        have hp_vec :
            Tendsto (fun k : ℕ ↦ pstar - A.p (ψ k)) atTop
              (nhds (0 : EuclideanSpace m)) := by
          exact tendsto_zero_iff_norm_tendsto_zero.mpr hp_norm_subseq
        have hip :
            Tendsto
              (fun k : ℕ ↦
                inner ℝ (pstar - A.p (ψ k)) (A.x (ψ k - 1) - A.x (ψ k)))
              atTop (nhds 0) := by
          have h := Filter.Tendsto.inner (𝕜 := ℝ) hp_vec hxstep_vec
          simpa using h
        let C : ℝ := A.alpha / A.lambdaLower
        have hC_nonneg : 0 ≤ C := by
          dsimp [C]
          exact div_nonneg A.alpha_nonneg (le_of_lt A.lambdaLower_pos)
        have hbound (k : ℕ) :
            ‖(A.alphaSeq (ψ k) / A.lambda (ψ k)) *
                inner ℝ (pstar - A.p (ψ k)) (A.x (ψ k - 1) - A.x (ψ k))‖ ≤
              C *
                ‖inner ℝ (pstar - A.p (ψ k)) (A.x (ψ k - 1) - A.x (ψ k))‖ := by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hcoeff_bound k) (abs_nonneg _)
        have hlim :
            Tendsto
              (fun k : ℕ ↦
                C *
                  ‖inner ℝ (pstar - A.p (ψ k)) (A.x (ψ k - 1) - A.x (ψ k))‖)
              atTop (nhds 0) := by
          simpa [Real.norm_eq_abs] using hip.norm.const_mul C
        exact tendsto_zero_iff_norm_tendsto_zero.mpr
          (squeeze_zero' (Eventually.of_forall (fun k ↦ norm_nonneg _))
            (Eventually.of_forall hbound) hlim)
      have h_phi :
          Tendsto (fun k : ℕ ↦ φ (ψ k) pstar - φ (ψ k) (A.p (ψ k)))
            atTop (nhds 0) := by
        have hsum := h_bregman.add (h_grad_ip.add h_inertial_ip)
        simpa [φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add,
          inner_add_left, inner_sub_left] using hsum
      simpa [sub_eq_add_neg, add_assoc] using h_term_h.add h_phi
    have h_rhs :
        Tendsto
          (fun k : ℕ ↦
            (P.objective pstar).toReal +
              (P.h (A.p (ψ k)) - P.h pstar + φ (ψ k) pstar -
                φ (ψ k) (A.p (ψ k)))) atTop
          (nhds ((P.objective pstar).toReal + 0)) := by
      exact tendsto_const_nhds.add h_error
    have h_lobj_toReal_le : l_obj.toReal ≤ (P.objective pstar).toReal := by
      have hle_eventually :
          ∀ᶠ k in atTop,
            (P.objective (A.p (ψ k))).toReal ≤
              (P.objective pstar).toReal +
                (P.h (A.p (ψ k)) - P.h pstar + φ (ψ k) pstar -
                  φ (ψ k) (A.p (ψ k))) :=
        Eventually.of_forall h_objective_ineq
      have hle :=
        le_of_tendsto_of_tendsto h_subseq_real h_rhs hle_eventually
      simpa using hle
    have hl_obj_coe : l_obj = (l_obj.toReal : EReal) :=
      (EReal.coe_toReal hl_obj_finite.1 hl_obj_finite.2).symm
    have hpstar_obj_coe :
        P.objective pstar = (((P.objective pstar).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hpstar_obj_fin.1 hpstar_obj_fin.2).symm
    rw [hl_obj_coe, hpstar_obj_coe]
    exact EReal.coe_le_coe_iff.mpr h_lobj_toReal_le
  have hobj_eq : P.objective pstar = l_obj := le_antisymm hobj_le_lobj hlobj_le_obj
  simpa [hobj_eq] using hsubseq_to_lobj

theorem cluster_point_critical_core {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {pstar : EuclideanSpace m}
    (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu)
    (hboundedBelow :
      ∃ C : ℝ, ∀ x : EuclideanSpace m, (C : EReal) ≤ P.objective x)
    (hxp_sum : Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖ ^ 2))
    (hxx_sum : Summable (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖ ^ 2))
    (hobj_conv : ∃ l_obj : EReal,
      Tendsto (fun n : ℕ ↦ P.objective (A.p n)) atTop (nhds l_obj))
    (hpstar : pstar ∈ omega A.p) :
    pstar ∈ limitingCriticalPoints P.objective := by
  rcases cluster_subseq_ge_two A hpstar with ⟨ψ, hψ_mono, hψ_ge_two, hψ_tendsto⟩
  have hx_tendsto : Tendsto (fun k : ℕ ↦ A.x (ψ k)) atTop (nhds pstar) :=
    tendsto_x_of_p_subseq A hxp_sum hψ_tendsto hψ_mono
  have hsub_mem :
      ∀ k, subgradientEstimateVector A (ψ k) ∈
        limitingSubdifferential P.objective (A.p (ψ k)) := by
    intro k
    exact (lemma_3_5_subgradient_estimate A (ψ k) (hψ_ge_two k)).1
  -- Remaining core analytic passage from the paper:
  -- use the argmin inequality to identify objective values on this cluster
  -- subsequence, prove the selected subgradients tend to `0`, then apply
  -- `limitingSubdifferential_closed_graph`.
  have hzero :
      (0 : EuclideanSpace m) ∈ limitingSubdifferential P.objective pstar := by
    have hsub_tendsto_zero :
        Tendsto (fun n : ℕ ↦ subgradientEstimateVector A n) atTop
          (nhds (0 : EuclideanSpace m)) :=
      subgradientEstimate_tendsto_zero A hxp_sum
    have hsub_tendsto_subseq :
        Tendsto (fun k : ℕ ↦ subgradientEstimateVector A (ψ k)) atTop
          (nhds (0 : EuclideanSpace m)) :=
      hsub_tendsto_zero.comp (StrictMono.tendsto_atTop hψ_mono)
    have hobj_tendsto :
        Tendsto (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop
          (nhds (P.objective pstar)) :=
      objective_tendsto_of_cluster_subsequence A nu mu hchosen hxp_sum hxx_sum
        hboundedBelow hobj_conv hψ_mono hψ_ge_two hψ_tendsto hx_tendsto
    have hpstar_eff : pstar ∈ ERealFunction.effectiveDom P.objective :=
      pstar_effectiveDom_of_cluster A nu mu hchosen hboundedBelow hobj_conv
        hψ_mono hψ_tendsto
    exact limitingSubdifferential_closed_graph
      (fun k : ℕ ↦ A.p (ψ k))
      (fun k : ℕ ↦ subgradientEstimateVector A (ψ k))
      hpstar_eff hsub_mem
      (Filter.Tendsto.prodMk_nhds hψ_tendsto hsub_tendsto_subseq)
      hobj_tendsto
  simpa [limitingCriticalPoints] using hzero

theorem objective_constant_on_omega_core {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu)
    (hboundedBelow :
      ∃ C : ℝ, ∀ x : EuclideanSpace m, (C : EReal) ≤ P.objective x)
    (_hxp_sum : Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖ ^ 2))
    (_hxx_sum : Summable (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖ ^ 2))
    (hobj_conv : ∃ l_obj : EReal,
      Tendsto (fun n : ℕ ↦ P.objective (A.p n)) atTop (nhds l_obj)) :
    ∃ c : ℝ, ∀ p ∈ omega A.p, P.objective p = (c : EReal) := by
  have hboundedBelow_all := hboundedBelow
  have hobj_conv_all := hobj_conv
  rcases hobj_conv with ⟨l_obj, hl_obj_tendsto⟩
  rcases hboundedBelow with ⟨C_low, hC_low⟩
  rcases p_objective_uniform_upper_tail A nu mu hchosen with ⟨C_high, hC_high⟩
  -- The remaining formal gap is the EReal order/limit step: the bounds
  -- `C_low ≤ objective (p n) ≤ C_high` make `l_obj` finite, and every cluster
  -- subsequence has objective limit `objective pstar`; uniqueness gives the
  -- common real value.
  have hl_obj_finite : l_obj ≠ ⊤ ∧ l_obj ≠ ⊥ := by
    exact ereal_bounded_limit_finite
      (z := fun n : ℕ ↦ P.objective (A.p n)) (l := l_obj)
      (C_low := C_low) (C_high := C_high)
      (fun n ↦ hC_low (A.p n)) hC_high hl_obj_tendsto
  let c : ℝ := l_obj.toReal
  have hl_obj_eq : l_obj = (c : EReal) :=
    (EReal.coe_toReal hl_obj_finite.1 hl_obj_finite.2).symm
  refine ⟨c, ?_⟩
  intro pstar hpstar
  rcases cluster_subseq_ge_two A hpstar with ⟨ψ, hψ_mono, _hψ_ge_two, _hψ_tendsto⟩
  have hsubseq_to_global :
      Tendsto (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop (nhds l_obj) :=
    hl_obj_tendsto.comp (StrictMono.tendsto_atTop hψ_mono)
  have hsubseq_to_cluster :
    Tendsto (fun k : ℕ ↦ P.objective (A.p (ψ k))) atTop
        (nhds (P.objective pstar)) := by
    have hx_tendsto : Tendsto (fun k : ℕ ↦ A.x (ψ k)) atTop (nhds pstar) :=
      tendsto_x_of_p_subseq A _hxp_sum _hψ_tendsto hψ_mono
    exact objective_tendsto_of_cluster_subsequence A nu mu hchosen _hxp_sum _hxx_sum
      hboundedBelow_all hobj_conv_all hψ_mono _hψ_ge_two _hψ_tendsto hx_tendsto
  have h_eq : P.objective pstar = l_obj :=
    tendsto_nhds_unique hsubseq_to_cluster hsubseq_to_global
  rw [h_eq, hl_obj_eq]

/-- Lemma 3.6: cluster points of `(p_n)` are nonempty, critical, compact/connected, and level-constant. -/
theorem lemma_3_6_cluster_points {m : ℕ} {P : ProblemData m} (A : AlgorithmData P)
    (nu mu : ℝ) (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective) :
    (omega A.p).Nonempty ∧
      omega A.p ⊆ limitingCriticalPoints P.objective ∧
      Tendsto (fun n : ℕ ↦ Metric.infDist (A.p n) (omega A.p)) atTop (nhds 0) ∧
      IsCompact (omega A.p) ∧
      IsConnected (omega A.p) ∧
      (∃ c : ℝ, ∀ p ∈ omega A.p, P.objective p = (c : EReal)) := by
  have hboundedBelow :
      ∃ C : ℝ, ∀ x : EuclideanSpace m, (C : EReal) ≤ P.objective x := by
    have hmin :=
      exists_minimizer_of_proper_lsc_coercive P.objective (objective_isProper P)
        (objective_lowerSemicontinuous P) hcoercive
    rcases hmin.1 with ⟨C, hCinf⟩
    rcases hmin.2 with ⟨xmin, hxmin_min, hxmin_eq_inf⟩
    have hmin_all : ∀ x : EuclideanSpace m, P.objective xmin ≤ P.objective x := by
      simpa [IsMinOn, IsMinFilter] using hxmin_min
    refine ⟨C, ?_⟩
    intro x
    rw [← hCinf, ← hxmin_eq_inf]
    exact hmin_all x
  rcases lemma_3_4_decrease A nu mu hchosen hboundedBelow with
    ⟨hxp_sum, hxx_sum, hobj_conv⟩
  have hp_inc : Tendsto (fun n : ℕ ↦ A.p (n + 1) - A.p n) atTop
      (nhds (0 : EuclideanSpace m)) :=
    p_increments_tendsto_zero A hxp_sum hxx_sum
  have hp_bounded : Bornology.IsBounded (Set.range A.p) := by
    exact p_range_bounded_of_coercive A nu mu hchosen hcoercive
  have hcluster := cluster_set_properties_of_vanishing_increments A.p hp_bounded hp_inc
  rcases hcluster with ⟨homega_nonempty, homega_compact, homega_connected, hdist⟩
  have hcrit_subset : omega A.p ⊆ limitingCriticalPoints P.objective := by
    intro pstar hpstar
    exact cluster_point_critical_core A nu mu hchosen hboundedBelow hxp_sum hxx_sum
      hobj_conv hpstar
  have hconstant :
      ∃ c : ℝ, ∀ p ∈ omega A.p, P.objective p = (c : EReal) := by
    exact objective_constant_on_omega_core A nu mu hchosen hboundedBelow hxp_sum hxx_sum
      hobj_conv
  exact ⟨homega_nonempty, hcrit_subset, hdist, homega_compact, homega_connected,
    hconstant⟩

end BotCsetnek2015
