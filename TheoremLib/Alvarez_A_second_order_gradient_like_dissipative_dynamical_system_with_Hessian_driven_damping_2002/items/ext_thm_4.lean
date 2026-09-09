import Mathlib
open Filter
open scoped Topology
namespace AlvarezAttouchBolteRedont
/-- The recorded vector field is the Hilbert-space gradient of the scalar potential. -/
def IsGradientOf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (gradPhi : H → H) : Prop :=
  ∀ x v : H,
    HasDerivAt (fun t : ℝ => phi (x + t • v))
      (inner ℝ (gradPhi x) v) 0

/-- The Frechet derivative of `phi` is represented by the Hilbert-space gradient field. -/
def IsFrechetGradientOf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (gradPhi : H → H) : Prop :=
  ∀ x : H,
    HasFDerivAt phi (InnerProductSpace.toDualMap ℝ H (gradPhi x)) x

/-- Lipschitz continuity on each bounded subset of the Hilbert space. -/
def LipschitzOnBoundedSets {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → H) : Prop :=
  ∀ s : Set H, Bornology.IsBounded s → ∃ K : NNReal, LipschitzOnWith K F s

/-- Forward-time version of system (1.2), matching the paper's half-line domain. -/
structure NonnegativeDissipativeSystem (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (gradPhi : H → H) (beta a b : ℝ) (x0 y0 : H) where
  x : ℝ → H
  y : ℝ → H
  xdot : ℝ → H
  ydot : ℝ → H
  beta_pos : 0 < beta
  b_pos : 0 < b
  a_add_b_pos : 0 < a + b
  initial_x : x 0 = x0
  initial_y : y 0 = y0
  equation_x : ∀ t : ℝ, 0 <= t →
    xdot t + beta • gradPhi (x t) + a • x t + b • y t = 0
  equation_y : ∀ t : ℝ, 0 <= t →
    ydot t + a • x t + b • y t = 0

/-- The Lyapunov energy `F_lambda(x, y) = lambda * phi x + 1 / 2 * |a x + b y|^2`. -/
noncomputable def LyapunovEnergy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (lam a b : ℝ) (p : Prod H H) : ℝ :=
  lam * phi p.1 + (1 / 2) * norm (a • p.1 + b • p.2) ^ 2

/-- A trajectory whose recorded velocity fields are the actual derivatives on `(0, +infty)`. -/
def IsGenuineTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {gradPhi : H → H} {beta a b : ℝ} {x0 y0 : H}
    (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0) : Prop :=
  (∀ t : ℝ, 0 < t → HasDerivAt sys.x (sys.xdot t) t) ∧
    (∀ t : ℝ, 0 < t → HasDerivAt sys.y (sys.ydot t) t)

/-- The interior regularity asserted for solutions in Theorem 1.1. -/
def IsRegularTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {gradPhi : H → H} {beta a b : ℝ} {x0 y0 : H}
    (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0) : Prop :=
  ContDiffOn ℝ 1 sys.x (Set.Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 2 sys.y (Set.Ici (0 : ℝ))

/--
The trajectory is continuous on the closed time interval `[0, +infty)`.
Together with the stored equalities `x 0 = x0` and `y 0 = y0`, this rules out
positive-time solutions that jump at the initial time.
-/
def IsContinuousOnNonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {gradPhi : H → H} {beta a b : ℝ} {x0 y0 : H}
    (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0) : Prop :=
  ContinuousOn sys.x (Set.Ici (0 : ℝ)) ∧
    ContinuousOn sys.y (Set.Ici (0 : ℝ))

/-- The solution predicate used in Theorem 1.1 on the paper's interval `[0, +infty)`. -/
def IsSolutionOnNonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {gradPhi : H → H} {beta a b : ℝ} {x0 y0 : H}
    (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0) : Prop :=
  IsGenuineTrajectory sys ∧ IsRegularTrajectory sys ∧ IsContinuousOnNonnegative sys

/--
Equality of two stored first-order systems on the paper's time domain `[0, +infty)`.
The structure stores total functions `ℝ → H`, but the ODE requirements and
uniqueness assertion are only for nonnegative time.
-/
def SameTrajectoryOnNonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {gradPhi : H → H} {beta a b : ℝ} {x0 y0 : H}
    (sys1 sys2 : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0) : Prop :=
  ∀ t : ℝ, 0 <= t →
    sys1.x t = sys2.x t ∧
      sys1.y t = sys2.y t ∧
      sys1.xdot t = sys2.xdot t ∧
      sys1.ydot t = sys2.ydot t

/-- Existence and uniqueness of a solution on the interval `[0, +infty)`. -/
def existsUniqueSolutionOnNonnegative {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gradPhi : H → H) (beta a b : ℝ) (x0 y0 : H) : Prop :=
  ∃ sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0,
    IsSolutionOnNonnegative sys ∧
      ∀ sys' : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0,
        IsSolutionOnNonnegative sys' →
          SameTrajectoryOnNonnegative sys' sys

/-- Square integrability on the nonnegative half-line. -/
def MemL2OnNonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℝ → H) : Prop :=
  MeasureTheory.MemLp f 2
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- Boundedness of the range on the nonnegative half-line. -/
def BoundedOnNonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℝ → H) : Prop :=
  Bornology.IsBounded (f '' Set.Ici (0 : ℝ))

private theorem bounded_image_of_lipschitzOn_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : H → H} {s : Set H} {K : NNReal}
    (hs : Bornology.IsBounded s) (hK : LipschitzOnWith K F s) :
    Bornology.IsBounded (F '' s) := by
  have hLip : LipschitzWith K (s.restrict F) := hK.to_restrict
  haveI : BoundedSpace s := hs.boundedSpace_val
  have hs_univ : Bornology.IsBounded (Set.univ : Set s) := Bornology.IsBounded.all _
  have himg := hLip.isBounded_image hs_univ
  rw [Set.image_univ] at himg
  convert himg using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩

private theorem aabr_energy_bddBelow
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b lam : ℝ)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hbeta : 0 < beta)
    (hlam_low : beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam) :
    ∃ m : ℝ, ∀ t : ℝ, 0 <= t →
      m <= LyapunovEnergy phi lam a b (sys.x t, sys.y t) := by
  have hlam_nonneg : 0 <= lam := by
    have hsq : 0 <= (Real.sqrt (a + b) - Real.sqrt b) ^ 2 := sq_nonneg _
    have hbase : 0 <= beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 :=
      mul_nonneg (le_of_lt hbeta) hsq
    exact le_trans hbase hlam_low
  rcases hphi_bddBelow with ⟨mphi, hmphi⟩
  refine ⟨lam * mphi, ?_⟩
  intro t ht
  unfold LyapunovEnergy
  have hphi_le : lam * mphi <= lam * phi (sys.x t) :=
    mul_le_mul_of_nonneg_left (hmphi (sys.x t)) hlam_nonneg
  have hnorm : 0 <= (1 / 2 : ℝ) * norm (a • sys.x t + b • sys.y t) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

private theorem aabr_grad_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {gradPhi : H → H} {beta a b : ℝ} {x0 y0 : H}
    (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    (hxbdd : BoundedOnNonnegative sys.x) :
    BoundedOnNonnegative (fun t : ℝ => gradPhi (sys.x t)) := by
  rcases hgrad_lip (sys.x '' Set.Ici (0 : ℝ)) hxbdd with ⟨K, hK⟩
  have himg : Bornology.IsBounded (gradPhi '' (sys.x '' Set.Ici (0 : ℝ))) :=
    bounded_image_of_lipschitzOn_bounded hxbdd hK
  unfold BoundedOnNonnegative
  convert himg using 1
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨sys.x t, ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, rfl⟩

private theorem BoundedOnNonnegative.congr
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : ℝ → H}
    (hf : BoundedOnNonnegative f) (hfg : ∀ t : ℝ, 0 <= t → g t = f t) :
    BoundedOnNonnegative g := by
  unfold BoundedOnNonnegative at *
  refine hf.subset ?_
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact ⟨t, ht, (hfg t ht).symm⟩

private theorem BoundedOnNonnegative.const_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : ℝ) {f : ℝ → H} (hf : BoundedOnNonnegative f) :
    BoundedOnNonnegative (fun t : ℝ => c • f t) := by
  unfold BoundedOnNonnegative at *
  let L : H →L[ℝ] H := c • ContinuousLinearMap.id ℝ H
  have hsmul : Bornology.IsBounded (L '' (f '' Set.Ici (0 : ℝ))) :=
    Bornology.IsBounded.image L hf
  refine hsmul.subset ?_
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact ⟨f t, ⟨t, ht, rfl⟩, rfl⟩

private theorem BoundedOnNonnegative.add
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : ℝ → H}
    (hf : BoundedOnNonnegative f) (hg : BoundedOnNonnegative g) :
    BoundedOnNonnegative (fun t : ℝ => f t + g t) := by
  unfold BoundedOnNonnegative at *
  let L : H × H →L[ℝ] H :=
    ContinuousLinearMap.fst ℝ H H + ContinuousLinearMap.snd ℝ H H
  have hprod :
      Bornology.IsBounded ((f '' Set.Ici (0 : ℝ)) ×ˢ (g '' Set.Ici (0 : ℝ))) :=
    hf.prod hg
  have hadd :
      Bornology.IsBounded (L '' ((f '' Set.Ici (0 : ℝ)) ×ˢ (g '' Set.Ici (0 : ℝ)))) :=
    Bornology.IsBounded.image L hprod
  refine hadd.subset ?_
  intro z hz
  rcases hz with ⟨t, ht, rfl⟩
  exact ⟨(f t, g t), ⟨⟨t, ht, rfl⟩, ⟨t, ht, rfl⟩⟩, rfl⟩

private theorem BoundedOnNonnegative.sub
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {f g : ℝ → H}
    (hf : BoundedOnNonnegative f) (hg : BoundedOnNonnegative g) :
    BoundedOnNonnegative (fun t : ℝ => f t - g t) := by
  simpa [sub_eq_add_neg] using
    BoundedOnNonnegative.add hf (BoundedOnNonnegative.const_smul (-1 : ℝ) hg)

private theorem antitoneOn_Ici_bddBelow_tendsto_atTop
    {f : ℝ → ℝ}
    (hanti : AntitoneOn f (Set.Ici (0 : ℝ)))
    (hlower : ∃ m : ℝ, ∀ t : ℝ, 0 <= t → m <= f t) :
    ∃ l : ℝ, Tendsto f atTop (nhds l) := by
  let g : ℝ → ℝ := fun t => f (max t 0)
  have hganti : Antitone g := by
    intro x y hxy
    dsimp [g]
    exact hanti (le_max_right x 0) (le_max_right y 0) (max_le_max_right 0 hxy)
  rcases hlower with ⟨m, hm⟩
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨m, ?_⟩
    rintro z ⟨t, rfl⟩
    exact hm (max t 0) (le_max_right t 0)
  refine ⟨⨅ t, g t, ?_⟩
  have hlim : Tendsto g atTop (nhds (⨅ t, g t)) :=
    tendsto_atTop_ciInf hganti hbdd
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  dsimp [g]
  rw [max_eq_left ht]

/-- The quadratic form occurring in the derivative of an admissible Lyapunov energy
is nonpositive on a ℝ Hilbert space. -/
lemma aabr_admissible_energy_deriv_nonpos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (beta a b lam : ℝ) (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    (hlow : beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam)
    (hhigh : lam <= beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2) (u q : H) :
    -lam * beta * ‖u‖ ^ 2 - (lam + a * beta) * inner ℝ u q -
        (a + b) * ‖q‖ ^ 2 <= 0 := by
  have hs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (le_of_lt hab)
  have ht_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
  have hs_nonneg : 0 <= Real.sqrt (a + b) := Real.sqrt_nonneg _
  have ht_nonneg : 0 <= Real.sqrt b := Real.sqrt_nonneg _
  have hs_four : Real.sqrt (a + b) ^ 4 = (a + b) ^ 2 := by
    rw [show Real.sqrt (a + b) ^ 4 = (Real.sqrt (a + b) ^ 2) ^ 2 by ring, hs_sq]
  have ht_four : Real.sqrt b ^ 4 = b ^ 2 := by
    rw [show Real.sqrt b ^ 4 = (Real.sqrt b ^ 2) ^ 2 by ring, ht_sq]
  have hst : Real.sqrt (a + b) ^ 2 * Real.sqrt b ^ 2 = (a + b) * b := by
    rw [hs_sq, ht_sq]
  have hdisc : (lam + a * beta) ^ 2 <= 4 * (lam * beta) * (a + b) := by
    have hprod : 0 <=
        (lam - beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2) *
          (beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 - lam) :=
      mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hhigh)
    ring_nf at hprod
    rw [hs_sq, ht_sq] at hprod
    ring_nf at hprod ⊢
    nlinarith
  have hlam_nonneg : 0 <= lam := by
    have : 0 <= beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 :=
      mul_nonneg (le_of_lt hbeta) (sq_nonneg _)
    exact this.trans hlow
  have hA_nonneg : 0 <= lam * beta := mul_nonneg hlam_nonneg (le_of_lt hbeta)
  have hB_pos : 0 < a + b := hab
  have hr : 0 <= ‖u‖ := norm_nonneg _
  have hq : 0 <= ‖q‖ := norm_nonneg _
  have hCabs_sq : |lam + a * beta| ^ 2 = (lam + a * beta) ^ 2 := sq_abs _
  have hquad :
      0 <= lam * beta * ‖u‖ ^ 2 - |lam + a * beta| * ‖u‖ * ‖q‖ +
        (a + b) * ‖q‖ ^ 2 := by
    by_cases hA : lam * beta = 0
    · have hC : lam + a * beta = 0 := by nlinarith
      simp [hA, hC, mul_nonneg (le_of_lt hab) (sq_nonneg ‖q‖)]
    · have hApos : 0 < lam * beta := lt_of_le_of_ne hA_nonneg (Ne.symm hA)
      have hrest : 0 <= 4 * (lam * beta) * (a + b) - |lam + a * beta| ^ 2 := by
        rw [hCabs_sq]
        linarith
      have hsquare : 0 <=
          (2 * (lam * beta) * ‖u‖ - |lam + a * beta| * ‖q‖) ^ 2 := sq_nonneg _
      nlinarith
  have hinner : |inner ℝ u q| <= ‖u‖ * ‖q‖ := abs_real_inner_le_norm u q
  have hcross : -(lam + a * beta) * inner ℝ u q <=
      |lam + a * beta| * ‖u‖ * ‖q‖ := by
    calc
      -(lam + a * beta) * inner ℝ u q <=
          |lam + a * beta| * |inner ℝ u q| := by
            calc
              -(lam + a * beta) * inner ℝ u q <=
                  |-(lam + a * beta) * inner ℝ u q| := le_abs_self _
              _ = |lam + a * beta| * |inner ℝ u q| := by
                rw [abs_mul, abs_neg]
      _ <= |lam + a * beta| * (‖u‖ * ‖q‖) :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
      _ = |lam + a * beta| * ‖u‖ * ‖q‖ := by ring
  nlinarith

/-- The autonomous phase-space vector field for the dissipative system. -/
def aabr_phaseField {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gradPhi : H → H) (beta a b : ℝ) : H × H → H × H :=
  fun z => (-beta • gradPhi z.1 - a • z.1 - b • z.2, -a • z.1 - b • z.2)

/-- The phase field is locally Lipschitz when the gradient is Lipschitz on bounded sets. -/
private theorem aabr_phaseField_locallyLipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (gradPhi : H → H) (beta a b : ℝ)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi) :
    LocallyLipschitz (aabr_phaseField gradPhi beta a b) := by
  have hgrad_local : LocallyLipschitz gradPhi := by
    intro x
    rcases hgrad_lip (Metric.closedBall x 1) Metric.isBounded_closedBall with ⟨K, hK⟩
    exact ⟨K, Metric.closedBall x 1, Metric.closedBall_mem_nhds x zero_lt_one, hK⟩
  have hfst : LocallyLipschitz (Prod.fst : H × H → H) :=
    LipschitzWith.prod_fst.locallyLipschitz
  have hsnd : LocallyLipschitz (Prod.snd : H × H → H) :=
    LipschitzWith.prod_snd.locallyLipschitz
  let Lbeta : H →L[ℝ] H := beta • ContinuousLinearMap.id ℝ H
  let La : H →L[ℝ] H := a • ContinuousLinearMap.id ℝ H
  let Lb : H →L[ℝ] H := b • ContinuousLinearMap.id ℝ H
  have hbeta_grad : LocallyLipschitz (fun z : H × H => beta • gradPhi z.1) := by
    simpa [Lbeta, Function.comp_def] using
      Lbeta.lipschitz.locallyLipschitz.comp (hgrad_local.comp hfst)
  have hax : LocallyLipschitz (fun z : H × H => a • z.1) := by
    simpa [La, Function.comp_def] using La.lipschitz.locallyLipschitz.comp hfst
  have hby : LocallyLipschitz (fun z : H × H => b • z.2) := by
    simpa [Lb, Function.comp_def] using Lb.lipschitz.locallyLipschitz.comp hsnd
  have hfirst : LocallyLipschitz (fun z : H × H => -beta • gradPhi z.1 - a • z.1 - b • z.2) := by
    intro z
    rcases hbeta_grad z with ⟨K1, s1, hs1, h1⟩
    rcases hax z with ⟨K2, s2, hs2, h2⟩
    rcases hby z with ⟨K3, s3, hs3, h3⟩
    have hs12 : s1 ∩ s2 ∈ 𝓝 z := Filter.inter_mem hs1 hs2
    have hs123 : s1 ∩ s2 ∩ s3 ∈ 𝓝 z := Filter.inter_mem hs12 hs3
    refine ⟨K1 + K2 + K3, s1 ∩ s2 ∩ s3, hs123, ?_⟩
    simpa only [neg_smul] using
      ((h1.mono (Set.inter_subset_left.trans Set.inter_subset_left)).neg.sub
        (h2.mono (Set.inter_subset_left.trans Set.inter_subset_right))).sub
        (h3.mono Set.inter_subset_right)
  have hsecond : LocallyLipschitz (fun z : H × H => -a • z.1 - b • z.2) := by
    intro z
    rcases hax z with ⟨K1, s1, hs1, h1⟩
    rcases hby z with ⟨K2, s2, hs2, h2⟩
    refine ⟨K1 + K2, s1 ∩ s2, Filter.inter_mem hs1 hs2, ?_⟩
    simpa only [neg_smul] using
      (h1.mono Set.inter_subset_left).neg.sub (h2.mono Set.inter_subset_right)
  convert hfirst.prodMk hsecond using 1

/-- The strict dissipation identity at the midpoint admissible Lyapunov parameter. -/
lemma aabr_midpoint_dissipation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (beta a b : ℝ) (u q : H) :
    -(- (beta * (a + 2 * b)) * beta * ‖u‖ ^ 2 -
        ((beta * (a + 2 * b)) + a * beta) * inner ℝ u q -
        (a + b) * ‖q‖ ^ 2) =
      beta ^ 2 * b * ‖u‖ ^ 2 + (a + b) * ‖beta • u + q‖ ^ 2 := by
  rw [show ‖u‖ ^ 2 = inner ℝ u u by rw [real_inner_self_eq_norm_sq],
    show ‖q‖ ^ 2 = inner ℝ q q by rw [real_inner_self_eq_norm_sq],
    show ‖beta • u + q‖ ^ 2 = inner ℝ (beta • u + q) (beta • u + q) by
      rw [real_inner_self_eq_norm_sq]]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm q u]
  ring

/-- Derivative of the Lyapunov energy along a genuine `(g-DIN)` trajectory. -/
lemma aabr_energy_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b lam : ℝ)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hsol : IsSolutionOnNonnegative sys) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => LyapunovEnergy phi lam a b (sys.x s, sys.y s))
      (-lam * beta * ‖gradPhi (sys.x t)‖ ^ 2 -
        (lam + a * beta) * inner ℝ (gradPhi (sys.x t))
          (a • sys.x t + b • sys.y t) -
        (a + b) * ‖a • sys.x t + b • sys.y t‖ ^ 2) t := by
  have hx : HasDerivAt sys.x (sys.xdot t) t := hsol.1.1 t ht
  have hy : HasDerivAt sys.y (sys.ydot t) t := hsol.1.2 t ht
  have hphi : HasDerivAt (fun s : ℝ => phi (sys.x s))
      (inner ℝ (gradPhi (sys.x t)) (sys.xdot t)) t := by
    convert (hgrad_phi (sys.x t)).comp_hasDerivAt t hx using 1
  have hq : HasDerivAt (fun s : ℝ => a • sys.x s + b • sys.y s)
      (a • sys.xdot t + b • sys.ydot t) t := by
    exact (hx.const_smul a).add (hy.const_smul b)
  have hnorm := hq.norm_sq.const_smul (1 / 2 : ℝ)
  have hE := (hphi.const_smul lam).add hnorm
  convert hE using 1
  have hxeq := sys.equation_x t (le_of_lt ht)
  have hyeq := sys.equation_y t (le_of_lt ht)
  have hxval : sys.xdot t = -beta • gradPhi (sys.x t) - a • sys.x t - b • sys.y t := by
    rw [show -beta • gradPhi (sys.x t) - a • sys.x t - b • sys.y t =
      -(beta • gradPhi (sys.x t) + a • sys.x t + b • sys.y t) by module]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc] using hxeq
  have hyval : sys.ydot t = -a • sys.x t - b • sys.y t := by
    rw [show -a • sys.x t - b • sys.y t = -(a • sys.x t + b • sys.y t) by module]
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_assoc] using hyeq
  rw [hxval, hyval]
  rw [show ‖gradPhi (sys.x t)‖ ^ 2 =
      inner ℝ (gradPhi (sys.x t)) (gradPhi (sys.x t)) by
    rw [real_inner_self_eq_norm_sq],
    show ‖a • sys.x t + b • sys.y t‖ ^ 2 =
      inner ℝ (a • sys.x t + b • sys.y t) (a • sys.x t + b • sys.y t) by
    rw [real_inner_self_eq_norm_sq]]
  simp only [one_div, invOf_eq_inv, smul_add, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (sys.x t) (gradPhi (sys.x t)),
    real_inner_comm (sys.y t) (gradPhi (sys.x t)),
    real_inner_comm (sys.y t) (sys.x t)]
  ring

private theorem aabr_global_solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    (x0 y0 : H) :
    existsUniqueSolutionOnNonnegative gradPhi beta a b x0 y0 := by
  -- EXTERNAL-REPAIR NOTE: needs a formal maximal-solution continuation theorem for the local ODE API.
  sorry

private theorem aabr_energy_antitone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b lam : ℝ)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hsol : IsSolutionOnNonnegative sys)
    (hlam_low : beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam)
    (hlam_high : lam <= beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2) :
    AntitoneOn
      (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
      (Set.Ici (0 : ℝ)) := by
  have hcont : IsContinuousOnNonnegative sys := hsol.2.2
  have hphi_cont : Continuous phi := continuous_iff_continuousAt.2 fun x =>
    (hgrad_phi x).continuousAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
  · have hphix : ContinuousOn (fun t : ℝ => phi (sys.x t)) (Set.Ici 0) :=
      hphi_cont.comp_continuousOn hcont.1
    have hq : ContinuousOn (fun t : ℝ => a • sys.x t + b • sys.y t) (Set.Ici 0) :=
      (hcont.1.const_smul a).add (hcont.2.const_smul b)
    have hnorm : ContinuousOn
        (fun t : ℝ => ‖a • sys.x t + b • sys.y t‖ ^ 2) (Set.Ici 0) :=
      hq.norm.pow 2
    exact (hphix.const_mul lam).add (hnorm.const_mul (1 / 2 : ℝ))
  · intro t ht
    have ht_pos : 0 < t := by simpa only [interior_Ici] using ht
    exact (aabr_energy_hasDerivAt phi gradPhi beta a b lam sys hgrad_phi hsol ht_pos).hasDerivWithinAt
  · intro t ht
    exact aabr_admissible_energy_deriv_nonpos beta a b lam hbeta hb hab
      hlam_low hlam_high (gradPhi (sys.x t)) (a • sys.x t + b • sys.y t)

private theorem aabr_l2_estimates
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hsol : IsSolutionOnNonnegative sys) :
      MemL2OnNonnegative sys.xdot ∧
      MemL2OnNonnegative sys.ydot := by
  let lamMid : ℝ := beta * (a + 2 * b)
  have _hlowerMid :
      ∃ m : ℝ, ∀ t : ℝ, 0 <= t →
        m <= LyapunovEnergy phi lamMid a b (sys.x t, sys.y t) := by
    -- The interior midpoint is admissible by the strict endpoint calculation in
    -- the plan; after that the existing lower-bound lemma applies.
    have hmid_low :
        beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lamMid := by
      have hs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt (le_of_lt hab)
      have ht_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
      have hprod_nonneg : 0 <= Real.sqrt (a + b) * Real.sqrt b :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hbase : (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= a + 2 * b := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hbase (le_of_lt hbeta)
    exact aabr_energy_bddBelow phi gradPhi beta a b lamMid sys hphi_bddBelow hbeta hmid_low
  sorry

private theorem aabr_phi_convergence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hEconv : ∀ lam : ℝ,
      beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam →
      lam <= beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 →
      ∃ l : ℝ,
        Tendsto (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
          atTop (nhds l)) :
    ∃ l : ℝ, Tendsto (fun t : ℝ => phi (sys.x t)) atTop (nhds l) := by
  let lamLow : ℝ := beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2
  let lamHigh : ℝ := beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2
  have hendpoint_le : lamLow <= lamHigh := by
    dsimp [lamLow, lamHigh]
    have hs : 0 <= Real.sqrt (a + b) := Real.sqrt_nonneg _
    have ht : 0 <= Real.sqrt b := Real.sqrt_nonneg _
    have hbase :
        (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <=
          (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
      nlinarith [mul_nonneg hs ht]
    exact mul_le_mul_of_nonneg_left hbase (le_of_lt hbeta)
  rcases hEconv lamLow le_rfl hendpoint_le with ⟨Llow, hLlow⟩
  rcases hEconv lamHigh hendpoint_le le_rfl with ⟨Lhigh, hLhigh⟩
  have hgap_pos : 0 < lamHigh - lamLow := by
    have hs_pos : 0 < Real.sqrt (a + b) := Real.sqrt_pos.2 hab
    have ht_pos : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    have hbase :
        (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <
          (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
      nlinarith [mul_pos hs_pos ht_pos]
    have hlt : lamLow < lamHigh := by
      dsimp [lamLow, lamHigh]
      exact mul_lt_mul_of_pos_left hbase hbeta
    exact sub_pos.2 hlt
  have hgap_ne : lamHigh - lamLow ≠ 0 := ne_of_gt hgap_pos
  have _hEdiff := hLhigh.sub hLlow
  refine ⟨(1 / (lamHigh - lamLow)) * (Lhigh - Llow), ?_⟩
  have hscaled := (hLhigh.sub hLlow).const_mul (1 / (lamHigh - lamLow))
  refine hscaled.congr' ?_
  filter_upwards with t
  have hs_ne : Real.sqrt (a + b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab)
  have ht_ne : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  dsimp [LyapunovEnergy, lamLow, lamHigh]
  field_simp [hgap_ne, hs_ne, ht_ne]
  ring_nf
  rw [show
    beta * Real.sqrt (a + b) * Real.sqrt b * phi (sys.x t) *
        (Real.sqrt (a + b))⁻¹ * (Real.sqrt b)⁻¹ * 2 =
      beta * phi (sys.x t) *
        (Real.sqrt (a + b) * (Real.sqrt (a + b))⁻¹) *
        (Real.sqrt b * (Real.sqrt b)⁻¹) * 2 by
      ring]
  simp [hs_ne, ht_ne]

private theorem aabr_bounded_xdot_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hsol : IsSolutionOnNonnegative sys)
    (hxbdd : BoundedOnNonnegative sys.x)
    (hgrad_bdd : BoundedOnNonnegative (fun t : ℝ => gradPhi (sys.x t)))
    (hy_bdd : BoundedOnNonnegative sys.y)
    (hxdot_bdd : BoundedOnNonnegative sys.xdot)
    (hxdot_l2 : MemL2OnNonnegative sys.xdot) :
    Tendsto sys.xdot atTop (nhds 0) := by
  rcases hgrad_lip (sys.x '' Set.Ici (0 : ℝ)) hxbdd with ⟨K, hK⟩
  have _hgrad_lip_on_range := hK
  have _hx_deriv : ∀ t : ℝ, 0 < t → HasDerivAt sys.x (sys.xdot t) t :=
    fun t ht => hsol.1.1 t ht
  sorry

private theorem aabr_lyapunov_and_limits
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hsol : IsSolutionOnNonnegative sys) (lam : ℝ)
    (hlam_low : beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam)
    (hlam_high : lam <= beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2) :
      AntitoneOn
        (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
        (Set.Ici (0 : ℝ)) ∧
      (∃ m : ℝ, ∀ t : ℝ, 0 <= t →
        m <= LyapunovEnergy phi lam a b (sys.x t, sys.y t)) ∧
      (∃ l : ℝ,
        Tendsto
          (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
          atTop (nhds l)) ∧
      MemL2OnNonnegative sys.xdot ∧
      (∃ l : ℝ, Tendsto (fun t : ℝ => phi (sys.x t)) atTop (nhds l)) ∧
      MemL2OnNonnegative sys.ydot ∧
      Tendsto sys.ydot atTop (nhds 0) := by
  have hantitone :
      AntitoneOn
        (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
        (Set.Ici (0 : ℝ)) := by
    exact aabr_energy_antitone phi gradPhi beta a b lam hgrad_phi hbeta hb hab sys hsol
      hlam_low hlam_high
  have hlower :
      ∃ m : ℝ, ∀ t : ℝ, 0 <= t →
        m <= LyapunovEnergy phi lam a b (sys.x t, sys.y t) :=
    aabr_energy_bddBelow phi gradPhi beta a b lam sys hphi_bddBelow hbeta hlam_low
  have henergy_conv :
      ∃ l : ℝ,
        Tendsto
          (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
          atTop (nhds l) := by
    exact antitoneOn_Ici_bddBelow_tendsto_atTop hantitone hlower
  have hl2_estimates :
      MemL2OnNonnegative sys.xdot ∧
      MemL2OnNonnegative sys.ydot :=
    aabr_l2_estimates phi gradPhi beta a b hgrad_phi hphi_bddBelow hbeta hb hab sys hsol
  have hxdot_l2 : MemL2OnNonnegative sys.xdot := hl2_estimates.1
  have hphi_conv :
      ∃ l : ℝ, Tendsto (fun t : ℝ => phi (sys.x t)) atTop (nhds l) := by
    refine aabr_phi_convergence phi gradPhi beta a b hbeta hb hab sys ?_
    intro mu hmu_low hmu_high
    have hanti_mu :
        AntitoneOn
          (fun t : ℝ => LyapunovEnergy phi mu a b (sys.x t, sys.y t))
          (Set.Ici (0 : ℝ)) :=
      aabr_energy_antitone phi gradPhi beta a b mu hgrad_phi hbeta hb hab sys hsol
        hmu_low hmu_high
    have hlower_mu :
        ∃ m : ℝ, ∀ t : ℝ, 0 <= t →
          m <= LyapunovEnergy phi mu a b (sys.x t, sys.y t) :=
      aabr_energy_bddBelow phi gradPhi beta a b mu sys hphi_bddBelow hbeta hmu_low
    exact antitoneOn_Ici_bddBelow_tendsto_atTop hanti_mu hlower_mu
  have hydot_l2 : MemL2OnNonnegative sys.ydot := hl2_estimates.2
  have hydot_lim : Tendsto sys.ydot atTop (nhds 0) := by
    sorry
  exact ⟨hantitone, hlower, henergy_conv, hxdot_l2, hphi_conv,
    hydot_l2, hydot_lim⟩

private theorem aabr_bounded_case
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b)
    {x0 y0 : H} (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0)
    (hsol : IsSolutionOnNonnegative sys)
    (hxbdd : BoundedOnNonnegative sys.x) :
      BoundedOnNonnegative (fun t : ℝ => gradPhi (sys.x t)) ∧
      BoundedOnNonnegative sys.xdot ∧
      Tendsto sys.xdot atTop (nhds 0) ∧
      Tendsto (fun t : ℝ => gradPhi (sys.x t)) atTop (nhds 0) := by
  have hgrad_bdd : BoundedOnNonnegative (fun t : ℝ => gradPhi (sys.x t)) :=
    aabr_grad_bounded sys hgrad_lip hxbdd
  have hendpoint_le :
      beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <=
        beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
    have hs : 0 <= Real.sqrt (a + b) := Real.sqrt_nonneg _
    have ht : 0 <= Real.sqrt b := Real.sqrt_nonneg _
    have hbase :
        (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <=
          (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := by
      nlinarith [mul_nonneg hs ht]
    exact mul_le_mul_of_nonneg_left hbase (le_of_lt hbeta)
  let lamTop : ℝ := beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2
  have hlyap :=
    aabr_lyapunov_and_limits phi gradPhi beta a b hphi_c1 hgrad_phi hphi_bddBelow
      hgrad_lip hbeta hb hab sys hsol lamTop hendpoint_le le_rfl
  have hy_bdd : BoundedOnNonnegative sys.y := by
    have hlam_nonneg : 0 <= lamTop := by
      have hsq : 0 <= (Real.sqrt (a + b) + Real.sqrt b) ^ 2 := sq_nonneg _
      exact mul_nonneg (le_of_lt hbeta) hsq
    rcases hphi_bddBelow with ⟨mphi, hmphi⟩
    let E : ℝ → ℝ := fun t =>
      LyapunovEnergy phi lamTop a b (sys.x t, sys.y t)
    have hE_le_E0 : ∀ t : ℝ, 0 <= t → E t <= E 0 := by
      intro t ht
      exact hlyap.1 (by simp) ht ht
    have hv_bdd :
        BoundedOnNonnegative (fun t : ℝ => a • sys.x t + b • sys.y t) := by
      refine (isBounded_iff_forall_norm_le).2 ?_
      let C0 : ℝ := 2 * (E 0 - lamTop * mphi)
      refine ⟨max C0 1, ?_⟩
      rintro z ⟨t, ht, rfl⟩
      have hphi_le : lamTop * mphi <= lamTop * phi (sys.x t) :=
        mul_le_mul_of_nonneg_left (hmphi (sys.x t)) hlam_nonneg
      have hsq_le : norm (a • sys.x t + b • sys.y t) ^ 2 <= C0 := by
        have hEt : E t <= E 0 := hE_le_E0 t ht
        dsimp [E, LyapunovEnergy] at hEt
        dsimp [C0, E, LyapunovEnergy]
        nlinarith
      have hC_ge_C0 : C0 <= max C0 1 := le_max_left _ _
      have hC_ge_one : (1 : ℝ) <= max C0 1 := le_max_right _ _
      have hC_nonneg : 0 <= max C0 1 := by linarith
      have hsq_le_Csq :
          norm (a • sys.x t + b • sys.y t) ^ 2 <= (max C0 1) ^ 2 := by
        have hC_le_Csq : max C0 1 <= (max C0 1) ^ 2 := by nlinarith
        exact hsq_le.trans (hC_ge_C0.trans hC_le_Csq)
      have habs := (sq_le_sq.mp hsq_le_Csq)
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hC_nonneg] using habs
    have hax : BoundedOnNonnegative (fun t : ℝ => a • sys.x t) :=
      BoundedOnNonnegative.const_smul a hxbdd
    have hby : BoundedOnNonnegative (fun t : ℝ => b • sys.y t) :=
      (BoundedOnNonnegative.sub hv_bdd hax).congr (by
        intro t ht
        module)
    have hb_ne : b ≠ 0 := ne_of_gt hb
    have hy_scaled :
        BoundedOnNonnegative (fun t : ℝ => (1 / b) • (b • sys.y t)) :=
      BoundedOnNonnegative.const_smul (1 / b) hby
    exact hy_scaled.congr (by
      intro t ht
      simp [smul_smul, hb_ne])
  have hxdot_bdd : BoundedOnNonnegative sys.xdot := by
    have hbeta_grad :
        BoundedOnNonnegative (fun t : ℝ => beta • gradPhi (sys.x t)) :=
      BoundedOnNonnegative.const_smul beta hgrad_bdd
    have hax : BoundedOnNonnegative (fun t : ℝ => a • sys.x t) :=
      BoundedOnNonnegative.const_smul a hxbdd
    have hby : BoundedOnNonnegative (fun t : ℝ => b • sys.y t) :=
      BoundedOnNonnegative.const_smul b hy_bdd
    have hsum :
        BoundedOnNonnegative
          (fun t : ℝ => (beta • gradPhi (sys.x t) + a • sys.x t) + b • sys.y t) :=
      (BoundedOnNonnegative.add hbeta_grad hax).add hby
    have hneg :
        BoundedOnNonnegative
          (fun t : ℝ =>
            (-1 : ℝ) • ((beta • gradPhi (sys.x t) + a • sys.x t) + b • sys.y t)) :=
      BoundedOnNonnegative.const_smul (-1 : ℝ) hsum
    exact hneg.congr (by
      intro t ht
      have hx := sys.equation_x t ht
      have hxdot :
          sys.xdot t = -((beta • gradPhi (sys.x t) + a • sys.x t) + b • sys.y t) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_assoc] using hx
      rw [hxdot]
      module)
  have hxdot_lim : Tendsto sys.xdot atTop (nhds 0) := by
    exact aabr_bounded_xdot_tendsto_zero phi gradPhi beta a b hgrad_lip sys hsol
      hxbdd hgrad_bdd hy_bdd hxdot_bdd hlyap.2.2.2.1
  have hgrad_lim : Tendsto (fun t : ℝ => gradPhi (sys.x t)) atTop (nhds 0) := by
    have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta
    have hbeta_grad :
        Tendsto (fun t : ℝ => beta • gradPhi (sys.x t)) atTop (nhds 0) := by
      have hsum : Tendsto (fun t : ℝ => sys.xdot t - sys.ydot t) atTop (nhds 0) := by
        simpa using hxdot_lim.sub hlyap.2.2.2.2.2.2
      have hneg : Tendsto (fun t : ℝ => -(sys.xdot t - sys.ydot t)) atTop (nhds 0) := by
        simpa using hsum.neg
      refine hneg.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      have hx := sys.equation_x t ht
      have hy := sys.equation_y t ht
      have hdiff : sys.xdot t - sys.ydot t + beta • gradPhi (sys.x t) = 0 := by
        calc
          sys.xdot t - sys.ydot t + beta • gradPhi (sys.x t) =
              (sys.xdot t + beta • gradPhi (sys.x t) + a • sys.x t + b • sys.y t) -
                (sys.ydot t + a • sys.x t + b • sys.y t) := by module
          _ = 0 := by rw [hx, hy]; module
      have : -(sys.xdot t - sys.ydot t) = beta • gradPhi (sys.x t) := by
        exact neg_eq_iff_add_eq_zero.mpr hdiff
      exact this
    have hscaled := hbeta_grad.const_smul (1 / beta)
    simpa [smul_smul, hbeta_ne, one_div] using hscaled
  exact ⟨hgrad_bdd, hxdot_bdd, hxdot_lim, hgrad_lim⟩

private theorem alvarez_attouch_bolte_redont_theorem_1_1_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b) :
    (∀ x0 y0 : H,
      existsUniqueSolutionOnNonnegative gradPhi beta a b x0 y0) ∧
    (∀ (x0 y0 : H)
        (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0),
      IsSolutionOnNonnegative sys →
      ∀ lam : ℝ,
        beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam →
        lam <= beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 →
          AntitoneOn
            (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
            (Set.Ici (0 : ℝ)) ∧
          (∃ m : ℝ, ∀ t : ℝ, 0 <= t →
            m <= LyapunovEnergy phi lam a b (sys.x t, sys.y t)) ∧
          (∃ l : ℝ,
            Tendsto
              (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
              atTop (nhds l)) ∧
          MemL2OnNonnegative sys.xdot ∧
          (∃ l : ℝ, Tendsto (fun t : ℝ => phi (sys.x t)) atTop (nhds l)) ∧
           MemL2OnNonnegative sys.ydot ∧
           Tendsto sys.ydot atTop (nhds 0)) ∧
    (∀ (x0 y0 : H)
        (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0),
      IsSolutionOnNonnegative sys →
      BoundedOnNonnegative sys.x →
        BoundedOnNonnegative (fun t : ℝ => gradPhi (sys.x t)) ∧
        BoundedOnNonnegative sys.xdot ∧
        Tendsto sys.xdot atTop (nhds 0) ∧
        Tendsto (fun t : ℝ => gradPhi (sys.x t)) atTop (nhds 0)) := by
  refine ⟨?existence, ?lyapunov, ?bounded_case⟩
  · intro x0 y0
    exact aabr_global_solution phi gradPhi beta a b hphi_c1 hgrad_phi hphi_bddBelow
      hgrad_lip hbeta hb hab x0 y0
  · intro x0 y0 sys hsol lam hlam_low hlam_high
    exact aabr_lyapunov_and_limits phi gradPhi beta a b hphi_c1 hgrad_phi hphi_bddBelow
      hgrad_lip hbeta hb hab sys hsol lam hlam_low hlam_high
  · intro x0 y0 sys hsol hxbdd
    exact aabr_bounded_case phi gradPhi beta a b hphi_c1 hgrad_phi hphi_bddBelow
      hgrad_lip hbeta hb hab sys hsol hxbdd

/--
Theorem 1.1 of Alvarez, Attouch, Bolte, and Redont for the first-order dissipative
system (1.2).

The solution predicate includes continuity on `[0, +infty)`, so the initial
conditions are satisfied in the same topology used for the ODE interval, not merely
as isolated values at `t = 0`.
-/
theorem alvarez_attouch_bolte_redont_theorem_1_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi : H → ℝ) (gradPhi : H → H) (beta a b : ℝ)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hgrad_phi : IsFrechetGradientOf phi gradPhi)
    (hphi_bddBelow : ∃ m : ℝ, ∀ x : H, m <= phi x)
    (hgrad_lip : LipschitzOnBoundedSets gradPhi)
    (hbeta : 0 < beta) (hb : 0 < b) (hab : 0 < a + b) :
    (∀ x0 y0 : H,
      existsUniqueSolutionOnNonnegative gradPhi beta a b x0 y0) ∧
    (∀ (x0 y0 : H)
        (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0),
      IsSolutionOnNonnegative sys →
      ∀ lam : ℝ,
        beta * (Real.sqrt (a + b) - Real.sqrt b) ^ 2 <= lam →
        lam <= beta * (Real.sqrt (a + b) + Real.sqrt b) ^ 2 →
          AntitoneOn
            (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
            (Set.Ici (0 : ℝ)) ∧
          (∃ m : ℝ, ∀ t : ℝ, 0 <= t →
            m <= LyapunovEnergy phi lam a b (sys.x t, sys.y t)) ∧
          (∃ l : ℝ,
            Tendsto
              (fun t : ℝ => LyapunovEnergy phi lam a b (sys.x t, sys.y t))
              atTop (nhds l)) ∧
          MemL2OnNonnegative sys.xdot ∧
          (∃ l : ℝ, Tendsto (fun t : ℝ => phi (sys.x t)) atTop (nhds l)) ∧
           MemL2OnNonnegative sys.ydot ∧
           Tendsto sys.ydot atTop (nhds 0)) ∧
    (∀ (x0 y0 : H)
        (sys : NonnegativeDissipativeSystem H gradPhi beta a b x0 y0),
      IsSolutionOnNonnegative sys →
      BoundedOnNonnegative sys.x →
        BoundedOnNonnegative (fun t : ℝ => gradPhi (sys.x t)) ∧
        BoundedOnNonnegative sys.xdot ∧
        Tendsto sys.xdot atTop (nhds 0) ∧
        Tendsto (fun t : ℝ => gradPhi (sys.x t)) atTop (nhds 0)) := by
  exact alvarez_attouch_bolte_redont_theorem_1_1_core phi gradPhi beta a b hphi_c1
    hgrad_phi hphi_bddBelow hgrad_lip hbeta hb hab

end AlvarezAttouchBolteRedont
