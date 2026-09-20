import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.algo_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_1

namespace BotCsetnek2015

open ERealFunction

/-- The vector `s_n` from Lemma 3.5. -/
noncomputable def subgradientEstimateVector {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) : EuclideanSpace m :=
  (1 / A.lambda n) • (gradient A.u (A.x n) - gradient A.u (A.p n)) +
    (gradient P.h (A.p n) - gradient P.h (A.x n)) +
    (A.alphaSeq n / A.lambda n) • (A.p (n - 1) - A.x (n - 1)) +
    ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) •
      (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1)))

private noncomputable def algorithmStepSmoothPart {m : ℕ} (P : ProblemData m)
    (u : EuclideanSpace m → ℝ) (lambda alphaSeq : ℕ → ℝ)
    (x : ℕ → EuclideanSpace m) (n : ℕ) : EuclideanSpace m → ℝ :=
  fun y ↦
    (1 / lambda n) * bregmanDistance u y (x n) +
      inner ℝ y (gradient P.h (x n)) +
      (alphaSeq n / lambda n) * inner ℝ y (x (n - 1) - x n)

theorem algorithmStepObjective_eq_objectiveSum_smoothPart {m : ℕ}
    (P : ProblemData m) (u : EuclideanSpace m → ℝ)
    (lambda alphaSeq : ℕ → ℝ) (x : ℕ → EuclideanSpace m) (n : ℕ) :
    algorithmStepObjective P u lambda alphaSeq x n =
      objectiveSum P.f (algorithmStepSmoothPart P u lambda alphaSeq x n) := by
  rfl

private theorem objectiveSum_effectiveDom_iff_local {m : ℕ}
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

theorem erealAddReal_ne_bot (a : EReal) (r : ℝ) (ha : a ≠ ⊥) :
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

theorem algorithmStep_argmin_effectiveDom {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) (_hn : 1 ≤ n)
    (hargmin : A.p n ∈ argminSet
      (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n)) :
    A.p n ∈ ERealFunction.effectiveDom
      (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n) := by
  classical
  let phi := algorithmStepSmoothPart P A.u A.lambda A.alphaSeq A.x n
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
    exact algorithmStepObjective_eq_objectiveSum_smoothPart P A.u A.lambda A.alphaSeq A.x n
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
    exact erealAddReal_ne_bot (P.f (A.p n)) (phi (A.p n)) (P.f_proper.1 (A.p n))
  rw [ERealFunction.mem_effectiveDom_iff]
  exact ⟨hne_top, hne_bot⟩

theorem lipschitzGradient_contDiff_one {m : ℕ}
    {g : EuclideanSpace m → ℝ} {L : ℝ}
    (hg : HasLipschitzContinuousGradient g L) :
    ContDiff ℝ 1 g := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨hg.2.1, ?_⟩
  have hgrad_lip : LipschitzWith (Real.toNNReal L) (gradient g) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have h := hg.2.2 x y
    simpa [dist_eq_norm, Real.coe_toNNReal _ hg.1] using h
  have hgrad_cont : Continuous (gradient g) := hgrad_lip.continuous
  have hrepr : fderiv ℝ g =
      fun x ↦ (InnerProductSpace.toDual ℝ (EuclideanSpace m)) (gradient g x) := by
    funext x
    ext v
    have hdiffAt : DifferentiableAt ℝ g x := hg.2.1 x
    simpa [InnerProductSpace.toDual_apply_apply]
      using (inner_gradient_left (𝕜 := ℝ) (f := g) (x := x) (y := v) hdiffAt).symm
  rw [hrepr]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace m)).continuous.comp hgrad_cont

theorem algorithmStepSmoothPart_contDiff {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) :
    ContDiff ℝ 1
      (algorithmStepSmoothPart P A.u A.lambda A.alphaSeq A.x n) := by
  have hu_cd : ContDiff ℝ 1 A.u := lipschitzGradient_contDiff_one A.u_lipschitz_gradient
  have hbreg : ContDiff ℝ 1
      (fun y : EuclideanSpace m ↦ bregmanDistance A.u y (A.x n)) := by
    dsimp [bregmanDistance]
    have hinner : ContDiff ℝ 1
        (fun y : EuclideanSpace m ↦ inner ℝ (gradient A.u (A.x n)) (y - A.x n)) := by
      have hconst : ContDiff ℝ 1
          (fun _ : EuclideanSpace m ↦ gradient A.u (A.x n)) := contDiff_const
      have hid : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y) := by
        simpa [id] using (contDiff_id : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y))
      have hsub : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y - A.x n) := by
        simpa using hid.sub
          (contDiff_const : ContDiff ℝ 1 (fun _ : EuclideanSpace m ↦ A.x n))
      exact hconst.inner ℝ hsub
    exact (hu_cd.sub contDiff_const).sub hinner
  have hterm1 : ContDiff ℝ 1
      (fun y : EuclideanSpace m ↦ (1 / A.lambda n) * bregmanDistance A.u y (A.x n)) := by
    simpa using (contDiff_const.mul hbreg : ContDiff ℝ 1
      (fun y : EuclideanSpace m ↦ (1 / A.lambda n) * bregmanDistance A.u y (A.x n)))
  have hterm2 : ContDiff ℝ 1
      (fun y : EuclideanSpace m ↦ inner ℝ y (gradient P.h (A.x n))) := by
    have hid : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y) := by
      simpa [id] using (contDiff_id : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y))
    exact hid.inner ℝ contDiff_const
  have hterm3 : ContDiff ℝ 1
      (fun y : EuclideanSpace m ↦
        (A.alphaSeq n / A.lambda n) * inner ℝ y (A.x (n - 1) - A.x n)) := by
    have hid : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y) := by
      simpa [id] using (contDiff_id : ContDiff ℝ 1 (fun y : EuclideanSpace m ↦ y))
    have hinner : ContDiff ℝ 1
        (fun y : EuclideanSpace m ↦ inner ℝ y (A.x (n - 1) - A.x n)) :=
      hid.inner ℝ contDiff_const
    simpa using (contDiff_const.mul hinner : ContDiff ℝ 1
      (fun y : EuclideanSpace m ↦
        (A.alphaSeq n / A.lambda n) * inner ℝ y (A.x (n - 1) - A.x n)))
  change ContDiff ℝ 1 (fun y : EuclideanSpace m ↦
    (1 / A.lambda n) * bregmanDistance A.u y (A.x n) +
      inner ℝ y (gradient P.h (A.x n)) +
      (A.alphaSeq n / A.lambda n) * inner ℝ y (A.x (n - 1) - A.x n))
  simpa [one_div] using (hterm1.add hterm2).add hterm3

theorem hasFDerivAt_inner_const_sub {m : ℕ}
    (c q p : EuclideanSpace m) :
    HasFDerivAt (fun y : EuclideanSpace m ↦ inner ℝ c (y - q))
      (InnerProductSpace.toDual ℝ (EuclideanSpace m) c) p := by
  let L : EuclideanSpace m →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (EuclideanSpace m) c
  have hL : HasFDerivAt (fun y : EuclideanSpace m ↦ L y) L p := L.hasFDerivAt
  have h := hL.sub_const (L q)
  convert h using 1
  ext y
  simp [L, InnerProductSpace.toDual_apply_apply, inner_sub_right]

theorem hasFDerivAt_inner_right_const {m : ℕ}
    (c p : EuclideanSpace m) :
    HasFDerivAt (fun y : EuclideanSpace m ↦ inner ℝ y c)
      (InnerProductSpace.toDual ℝ (EuclideanSpace m) c) p := by
  have h := ((ContinuousLinearMap.id ℝ (EuclideanSpace m)).hasFDerivAt.inner ℝ
    (hasFDerivAt_const (𝕜 := ℝ) c p))
  convert h using 1
  ext v
  simp [fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.toDual_apply_apply]
  rw [real_inner_comm v c]

theorem hasFDerivAt_bregmanDistance_left {m : ℕ}
    {u : EuclideanSpace m → ℝ} (hu : Differentiable ℝ u)
    (p q : EuclideanSpace m) :
    HasFDerivAt (fun y : EuclideanSpace m ↦ bregmanDistance u y q)
      (InnerProductSpace.toDual ℝ (EuclideanSpace m) (gradient u p - gradient u q)) p := by
  have hu_at : HasFDerivAt u
      (InnerProductSpace.toDual ℝ (EuclideanSpace m) (gradient u p)) p := by
    have hdiffAt : DifferentiableAt ℝ u p := hu p
    have hbase : HasFDerivAt u (fderiv ℝ u p) p := hdiffAt.hasFDerivAt
    convert hbase using 1
    ext v
    simpa [InnerProductSpace.toDual_apply_apply]
      using (inner_gradient_left (𝕜 := ℝ) (f := u) (x := p) (y := v) hdiffAt)
  have hconst : HasFDerivAt (fun _ : EuclideanSpace m ↦ u q) 0 p :=
    hasFDerivAt_const (𝕜 := ℝ) (u q) p
  have hinner := hasFDerivAt_inner_const_sub (gradient u q) q p
  have h := (hu_at.sub hconst).sub hinner
  dsimp [bregmanDistance]
  convert h using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

theorem hasFDerivAt_algorithmStepSmoothPart {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) :
    HasFDerivAt (algorithmStepSmoothPart P A.u A.lambda A.alphaSeq A.x n)
      (InnerProductSpace.toDual ℝ (EuclideanSpace m)
        ((1 / A.lambda n) • (gradient A.u (A.p n) - gradient A.u (A.x n)) +
          gradient P.h (A.x n) +
          (A.alphaSeq n / A.lambda n) • (A.x (n - 1) - A.x n))) (A.p n) := by
  let p := A.p n
  let q := A.x n
  let c := A.x (n - 1) - A.x n
  have hbreg := hasFDerivAt_bregmanDistance_left A.u_lipschitz_gradient.2.1 p q
  have hterm1 : HasFDerivAt
      (fun y : EuclideanSpace m ↦ (1 / A.lambda n) * bregmanDistance A.u y q)
      ((1 / A.lambda n) •
        InnerProductSpace.toDual ℝ (EuclideanSpace m) (gradient A.u p - gradient A.u q)) p := by
    simpa using hbreg.const_mul (1 / A.lambda n)
  have hterm2 := hasFDerivAt_inner_right_const (gradient P.h q) p
  have hinner3 := hasFDerivAt_inner_right_const c p
  have hterm3 : HasFDerivAt
      (fun y : EuclideanSpace m ↦ (A.alphaSeq n / A.lambda n) * inner ℝ y c)
      ((A.alphaSeq n / A.lambda n) • InnerProductSpace.toDual ℝ (EuclideanSpace m) c) p := by
    simpa using hinner3.const_mul (A.alphaSeq n / A.lambda n)
  have hsum := (hterm1.add hterm2).add hterm3
  change HasFDerivAt (fun y : EuclideanSpace m ↦
      (1 / A.lambda n) * bregmanDistance A.u y (A.x n) +
        inner ℝ y (gradient P.h (A.x n)) +
        (A.alphaSeq n / A.lambda n) * inner ℝ y (A.x (n - 1) - A.x n))
      (InnerProductSpace.toDual ℝ (EuclideanSpace m)
        ((1 / A.lambda n) • (gradient A.u (A.p n) - gradient A.u (A.x n)) +
          gradient P.h (A.x n) +
          (A.alphaSeq n / A.lambda n) • (A.x (n - 1) - A.x n))) (A.p n)
  convert hsum using 1
  ext y
  simp [p, q, c]

theorem gradient_algorithmStepSmoothPart {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) :
    gradient (algorithmStepSmoothPart P A.u A.lambda A.alphaSeq A.x n) (A.p n) =
      (1 / A.lambda n) • (gradient A.u (A.p n) - gradient A.u (A.x n)) +
        gradient P.h (A.x n) +
        (A.alphaSeq n / A.lambda n) • (A.x (n - 1) - A.x n) := by
  let rhs : EuclideanSpace m :=
    (1 / A.lambda n) • (gradient A.u (A.p n) - gradient A.u (A.x n)) +
      gradient P.h (A.x n) +
      (A.alphaSeq n / A.lambda n) • (A.x (n - 1) - A.x n)
  have hderiv := hasFDerivAt_algorithmStepSmoothPart A n
  change (InnerProductSpace.toDual ℝ (EuclideanSpace m)).symm
      (fderiv ℝ (algorithmStepSmoothPart P A.u A.lambda A.alphaSeq A.x n) (A.p n)) = rhs
  rw [hderiv.fderiv]
  simp [rhs]

theorem algorithm_optimality_subgradient_base {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (n : ℕ) (hn : 1 ≤ n) :
    ((1 / A.lambda n) • (gradient A.u (A.x n) - gradient A.u (A.p n)) +
      (gradient P.h (A.p n) - gradient P.h (A.x n)) +
      (A.alphaSeq n / A.lambda n) • (A.x n - A.x (n - 1))) ∈
      limitingSubdifferential P.objective (A.p n) := by
  have hargmin :
      A.p n ∈ argminSet (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n) :=
    A.p_argmin n hn
  have hmin_step :
      IsMinOn (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n)
        Set.univ (A.p n) := by
    intro y _hy
    rw [mem_argminSet_iff] at hargmin
    rw [hargmin]
    exact sInf_le
      (s := Set.range (algorithmStepObjective P A.u A.lambda A.alphaSeq A.x n))
      (Set.mem_range_self y)
  let phi := algorithmStepSmoothPart P A.u A.lambda A.alphaSeq A.x n
  have hxeff :
      A.p n ∈ ERealFunction.effectiveDom (objectiveSum P.f phi) := by
    have hx_alg := algorithmStep_argmin_effectiveDom A n hn hargmin
    simpa [phi, algorithmStepObjective_eq_objectiveSum_smoothPart]
      using hx_alg
  have hmin_phi : IsMinOn (objectiveSum P.f phi) Set.univ (A.p n) := by
    simpa [phi, algorithmStepObjective_eq_objectiveSum_smoothPart] using hmin_step
  have hfermat :
      (0 : EuclideanSpace m) ∈
        limitingSubdifferential (objectiveSum P.f phi) (A.p n) :=
    fermat_rule_limitingSubdifferential hxeff hmin_phi
  have hphi_cd : ContDiff ℝ 1 phi := by
    simpa [phi] using algorithmStepSmoothPart_contDiff A n
  have hsum_phi :=
    limitingSubdifferential_smooth_sum_rule P.f phi (A.p n)
      P.f_proper P.f_lsc hphi_cd
  rw [hsum_phi] at hfermat
  rcases hfermat with ⟨w, hw, hzero⟩
  have hw_eq : w = - gradient phi (A.p n) := by
    have hsum_zero : w + gradient phi (A.p n) = 0 := by
      simpa using hzero.symm
    calc
      w = w + gradient phi (A.p n) - gradient phi (A.p n) := by abel
      _ = 0 - gradient phi (A.p n) := by rw [hsum_zero]
      _ = - gradient phi (A.p n) := by abel
  have hh_cd : ContDiff ℝ 1 P.h :=
    lipschitzGradient_contDiff_one P.h_lipschitz_gradient
  have hsum_h :=
    limitingSubdifferential_smooth_sum_rule P.f P.h (A.p n)
      P.f_proper P.f_lsc hh_cd
  change
    ((1 / A.lambda n) • (gradient A.u (A.x n) - gradient A.u (A.p n)) +
      (gradient P.h (A.p n) - gradient P.h (A.x n)) +
      (A.alphaSeq n / A.lambda n) • (A.x n - A.x (n - 1))) ∈
      limitingSubdifferential (objectiveSum P.f P.h) (A.p n)
  rw [hsum_h]
  refine ⟨w, hw, ?_⟩
  rw [hw_eq]
  have hgrad := gradient_algorithmStepSmoothPart A n
  rw [hgrad]
  simp [sub_eq_add_neg, smul_add, smul_neg, add_comm, add_left_comm, add_assoc]

theorem x_update_sub_prev {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {n : ℕ} (hn : 2 ≤ n) :
    A.x n - A.x (n - 1) =
      (A.p (n - 1) - A.x (n - 1)) +
        A.lambda (n - 1) •
          (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))) := by
  have hpred : 1 ≤ n - 1 := by omega
  have hsucc : (n - 1) + 1 = n := by omega
  have hxupd := A.x_update (n - 1) hpred
  rw [hsucc] at hxupd
  calc
    A.x n - A.x (n - 1)
        = (A.p (n - 1) +
            A.lambda (n - 1) •
              (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1)))) -
            A.x (n - 1) := by rw [hxupd]
    _ = (A.p (n - 1) - A.x (n - 1)) +
        A.lambda (n - 1) •
          (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))) := by
      abel

theorem subgradientEstimateVector_eq_base {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {n : ℕ} (hn : 2 ≤ n) :
    subgradientEstimateVector A n =
      (1 / A.lambda n) • (gradient A.u (A.x n) - gradient A.u (A.p n)) +
        (gradient P.h (A.p n) - gradient P.h (A.x n)) +
        (A.alphaSeq n / A.lambda n) • (A.x n - A.x (n - 1)) := by
  have hn1 : 1 ≤ n := by omega
  have hlambda_n_lower := (A.lambda_bounds n hn1).1
  have hlambda_n_pos : 0 < A.lambda n := by
    linarith [A.lambdaLower_pos, hlambda_n_lower]
  have hlambda_n_ne : A.lambda n ≠ 0 := ne_of_gt hlambda_n_pos
  have hxsplit := x_update_sub_prev A hn
  unfold subgradientEstimateVector
  rw [hxsplit]
  simp only [smul_add, smul_smul]
  have hcoef :
      (A.alphaSeq n / A.lambda n) * A.lambda (n - 1) =
        (A.alphaSeq n * A.lambda (n - 1)) / A.lambda n := by
    field_simp [hlambda_n_ne]
  rw [hcoef]
  abel

theorem subgradientEstimateVector_norm_bound {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) {n : ℕ} (hn : 2 ≤ n) :
    ‖subgradientEstimateVector A n‖ ≤
      (A.Lgrad_u / A.lambda n + P.Lgrad_h) * ‖A.x n - A.p n‖ +
        (A.alphaSeq n / A.lambda n) *
          (1 + A.lambda (n - 1) * P.Lgrad_h) *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
  have hn1 : 1 ≤ n := by omega
  have hpred : 1 ≤ n - 1 := by omega
  have hlambda_n_lower := (A.lambda_bounds n hn1).1
  have hlambda_n_pos : 0 < A.lambda n := by
    linarith [A.lambdaLower_pos, hlambda_n_lower]
  have hlambda_n_nonneg : 0 ≤ A.lambda n := le_of_lt hlambda_n_pos
  have hlambda_n_ne : A.lambda n ≠ 0 := ne_of_gt hlambda_n_pos
  have hlambda_pred_lower := (A.lambda_bounds (n - 1) hpred).1
  have hlambda_pred_pos : 0 < A.lambda (n - 1) := by
    linarith [A.lambdaLower_pos, hlambda_pred_lower]
  have hlambda_pred_nonneg : 0 ≤ A.lambda (n - 1) := le_of_lt hlambda_pred_pos
  have hα_nonneg : 0 ≤ A.alphaSeq n := (A.alpha_bounds n hn1).1
  have hα_div_nonneg : 0 ≤ A.alphaSeq n / A.lambda n :=
    div_nonneg hα_nonneg hlambda_n_nonneg
  have hcoef_nonneg :
      0 ≤ (A.alphaSeq n * A.lambda (n - 1)) / A.lambda n :=
    div_nonneg (mul_nonneg hα_nonneg hlambda_pred_nonneg) hlambda_n_nonneg
  have hinv_nonneg : 0 ≤ 1 / A.lambda n := by positivity
  let a : EuclideanSpace m :=
    (1 / A.lambda n) • (gradient A.u (A.x n) - gradient A.u (A.p n))
  let b : EuclideanSpace m := gradient P.h (A.p n) - gradient P.h (A.x n)
  let c : EuclideanSpace m :=
    (A.alphaSeq n / A.lambda n) • (A.p (n - 1) - A.x (n - 1))
  let d : EuclideanSpace m :=
    ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) •
      (gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1)))
  have hs_def : subgradientEstimateVector A n = a + b + c + d := by
    rfl
  have htri : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    have h1 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ :=
      norm_add_le (a + b + c) d
    have h2 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ :=
      norm_add_le (a + b) c
    have h3 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ :=
      norm_add_le a b
    nlinarith
  have ha :
      ‖a‖ ≤ (A.Lgrad_u / A.lambda n) * ‖A.x n - A.p n‖ := by
    have hu_lip := A.u_lipschitz_gradient.2.2 (A.x n) (A.p n)
    calc
      ‖a‖ =
          ‖(1 / A.lambda n : ℝ)‖ *
            ‖gradient A.u (A.x n) - gradient A.u (A.p n)‖ := by
        simp [a, norm_smul]
      _ =
          (1 / A.lambda n) *
            ‖gradient A.u (A.x n) - gradient A.u (A.p n)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
      _ ≤ (1 / A.lambda n) *
          (A.Lgrad_u * ‖A.x n - A.p n‖) := by
        exact mul_le_mul_of_nonneg_left hu_lip hinv_nonneg
      _ = (A.Lgrad_u / A.lambda n) * ‖A.x n - A.p n‖ := by
        field_simp [hlambda_n_ne]
  have hb :
      ‖b‖ ≤ P.Lgrad_h * ‖A.x n - A.p n‖ := by
    have hh_lip := P.h_lipschitz_gradient.2.2 (A.x n) (A.p n)
    simpa [b, norm_sub_rev] using hh_lip
  have hc :
      ‖c‖ ≤
        (A.alphaSeq n / A.lambda n) * ‖A.x (n - 1) - A.p (n - 1)‖ := by
    calc
      ‖c‖ =
          ‖(A.alphaSeq n / A.lambda n : ℝ)‖ *
            ‖A.p (n - 1) - A.x (n - 1)‖ := by
        simp [c, norm_smul]
      _ =
          (A.alphaSeq n / A.lambda n) *
            ‖A.p (n - 1) - A.x (n - 1)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hα_div_nonneg]
      _ ≤
          (A.alphaSeq n / A.lambda n) *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
        rw [norm_sub_rev]
  have hd :
      ‖d‖ ≤
        ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) * P.Lgrad_h *
          ‖A.x (n - 1) - A.p (n - 1)‖ := by
    have hh_lip := P.h_lipschitz_gradient.2.2 (A.x (n - 1)) (A.p (n - 1))
    calc
      ‖d‖ =
          ‖((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n : ℝ)‖ *
            ‖gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))‖ := by
        simp [d, norm_smul]
      _ =
          ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) *
            ‖gradient P.h (A.x (n - 1)) - gradient P.h (A.p (n - 1))‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hcoef_nonneg]
      _ ≤
          ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) *
            (P.Lgrad_h * ‖A.x (n - 1) - A.p (n - 1)‖) := by
        exact mul_le_mul_of_nonneg_left hh_lip hcoef_nonneg
      _ =
          ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
        ring
  rw [hs_def]
  calc
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := htri
    _ ≤
        (A.Lgrad_u / A.lambda n) * ‖A.x n - A.p n‖ +
          P.Lgrad_h * ‖A.x n - A.p n‖ +
          (A.alphaSeq n / A.lambda n) *
            ‖A.x (n - 1) - A.p (n - 1)‖ +
          ((A.alphaSeq n * A.lambda (n - 1)) / A.lambda n) * P.Lgrad_h *
            ‖A.x (n - 1) - A.p (n - 1)‖ := by
      nlinarith [ha, hb, hc, hd]
    _ =
        (A.Lgrad_u / A.lambda n + P.Lgrad_h) * ‖A.x n - A.p n‖ +
          (A.alphaSeq n / A.lambda n) *
            (1 + A.lambda (n - 1) * P.Lgrad_h) *
              ‖A.x (n - 1) - A.p (n - 1)‖ := by
      field_simp [hlambda_n_ne]
      ring

/-- Lemma 3.5: subgradient membership and norm estimate. -/
theorem lemma_3_5_subgradient_estimate {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) :
    ∀ n, 2 ≤ n →
      subgradientEstimateVector A n ∈ limitingSubdifferential P.objective (A.p n) ∧
        ‖subgradientEstimateVector A n‖ ≤
          (A.Lgrad_u / A.lambda n + P.Lgrad_h) * ‖A.x n - A.p n‖ +
            (A.alphaSeq n / A.lambda n) * (1 + A.lambda (n - 1) * P.Lgrad_h) *
              ‖A.x (n - 1) - A.p (n - 1)‖ := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hbase := algorithm_optimality_subgradient_base A n hn1
  have hvec := subgradientEstimateVector_eq_base A hn
  have hmembership :
      subgradientEstimateVector A n ∈ limitingSubdifferential P.objective (A.p n) := by
    rw [hvec]
    exact hbase
  exact ⟨hmembership, subgradientEstimateVector_norm_bound A hn⟩

end BotCsetnek2015
