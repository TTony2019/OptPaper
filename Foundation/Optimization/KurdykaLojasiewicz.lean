import Mathlib
import Mathlib.Tactic
import Foundation.Analysis.LimitingSubdifferential
import Foundation.Analysis.Semicontinuity

/-!
# Kurdyka--Łojasiewicz functions

The nonsmooth KL property for extended-real-valued functions, together with the
uniformization theorem on compact sets where the function is constant.
-/

open Filter
open scoped Topology BigOperators

namespace ERealFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Add a real number to an extended real, resolving the indeterminate `⊤ + ⊥` case in favor of
`⊤`.  For finite real perturbations this agrees with ordinary addition. -/
def addReal (a : EReal) (r : ℝ) : EReal :=
  EReal.sumWithTopBotAsTop a (r : EReal)

/-- A finite-parameter desingularizing function. -/
def DesingularizingFunction (eta : ℝ) (phi : ℝ → ℝ) : Prop :=
  0 < eta ∧
    ConcaveOn ℝ (Set.Ico 0 eta) phi ∧
    phi 0 = 0 ∧
    ContDiffOn ℝ 1 phi (Set.Ioo 0 eta) ∧
    ContinuousAt phi 0 ∧
    ∀ s ∈ Set.Ioo 0 eta, 0 < deriv phi s

/-- The KL property at a point of the limiting-subdifferential domain. -/
def HasKLPropertyAt (f : E → EReal) (xbar : E) : Prop :=
  xbar ∈ limitingSubdifferentialDomain f ∧
    ∃ eta : ℝ, ∃ U : Set E, ∃ phi : ℝ → ℝ,
      0 < eta ∧ U ∈ nhds xbar ∧ DesingularizingFunction eta phi ∧
        ∀ x ∈ U,
          f xbar < f x →
          f x < addReal (f xbar) eta →
          (1 : ENNReal) ≤ ENNReal.ofReal
              (deriv phi ((f x).toReal - (f xbar).toReal)) *
            Metric.infEDist (0 : E) (limitingSubdifferential f x)

/-- A proper lower-semicontinuous extended-real-valued function is a KL function when it has the
KL property at every point of its limiting-subdifferential domain. -/
def IsKLFunction (f : E → EReal) : Prop :=
  IsProper f ∧ LowerSemicontinuous f ∧
    ∀ x ∈ limitingSubdifferentialDomain f, HasKLPropertyAt f x

theorem desingularizingFunction_id :
    DesingularizingFunction 1 (fun s : ℝ ↦ s) := by
  refine ⟨by norm_num, ?_, rfl, ?_, continuousAt_id, ?_⟩
  · simpa using
      (concaveOn_id (𝕜 := ℝ) (s := Set.Ico (0 : ℝ) 1)
        (convex_Ico (0 : ℝ) 1))
  · simpa using (contDiffOn_id : ContDiffOn ℝ 1 (fun s : ℝ ↦ s) (Set.Ioo 0 1))
  · intro s hs
    simp

private theorem finset_inf'_pos {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (g : ι → ℝ) (hg : ∀ a ∈ s, 0 < g a) :
    0 < s.inf' hs g := by
  rw [Finset.lt_inf'_iff]
  exact hg

omit [InnerProductSpace ℝ E] in
private theorem tube_cover_of_infDist_lt_finset_inf
    {Omega : Set E} {ι : Type*}
    {t : Finset ι} (_ht : t.Nonempty) (center : ι → E) (r : ι → ℝ)
    (_hr_pos : ∀ i ∈ t, 0 < r i)
    (hcover : ∀ y ∈ Omega, ∃ i ∈ t, dist y (center i) < r i)
    (epsilon : ℝ) (heps_le : ∀ i ∈ t, epsilon ≤ r i)
    (hOmega_nonempty : Omega.Nonempty) :
    ∀ x, Metric.infDist x Omega < epsilon →
      ∃ i ∈ t, dist x (center i) < 2 * r i := by
  intro x hdist
  rcases (Metric.infDist_lt_iff hOmega_nonempty).mp hdist with ⟨y, hyOmega, hxy⟩
  rcases hcover y hyOmega with ⟨i, hi, hyi⟩
  refine ⟨i, hi, ?_⟩
  calc
    dist x (center i) ≤ dist x y + dist y (center i) := dist_triangle x y (center i)
    _ < epsilon + r i := add_lt_add hxy hyi
    _ ≤ r i + r i := add_le_add (heps_le i hi) le_rfl
    _ = 2 * r i := by ring

private theorem addReal_mono {a : EReal} {r s : ℝ} (hrs : r ≤ s) :
    addReal a r ≤ addReal a s := by
  cases a using EReal.rec with
  | bot => rfl
  | coe a =>
      change ((a + r : ℝ) : EReal) ≤ ((a + s : ℝ) : EReal)
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  | top => rfl

/-- A finite extended-real KL window becomes an ordinary real interval after applying
`EReal.toReal`. -/
theorem toReal_sub_mem_Ioo_of_addReal_window
    {a b : EReal} {eta : ℝ} (_heta : 0 < eta)
    (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hlo : a < b) (hhi : b < addReal a eta) :
    b.toReal - a.toReal ∈ Set.Ioo 0 eta := by
  cases a using EReal.rec with
  | bot => exact False.elim (ha_bot rfl)
  | top => exact False.elim (ha_top rfl)
  | coe ar =>
      cases b using EReal.rec with
      | bot => simp at hlo
      | top =>
          change (⊤ : EReal) < ((ar + eta : ℝ) : EReal) at hhi
          simp at hhi
      | coe br =>
          change ((ar : EReal) < (br : EReal)) at hlo
          change ((br : EReal) < ((ar + eta : ℝ) : EReal)) at hhi
          have hlo_real : ar < br := EReal.coe_lt_coe_iff.mp hlo
          have hhi_real : br < ar + eta := EReal.coe_lt_coe_iff.mp hhi
          constructor <;> simp [EReal.toReal_coe] <;> linarith

private theorem desingularizingFunction_finsetSum {ι : Type*}
    {t : Finset ι} (ht : t.Nonempty)
    (eta : ℝ) (etaI : ι → ℝ) (phiI : ι → ℝ → ℝ)
    (heta_pos : 0 < eta) (heta_le : ∀ i ∈ t, eta ≤ etaI i)
    (hphi : ∀ i ∈ t, DesingularizingFunction (etaI i) (phiI i)) :
    DesingularizingFunction eta (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) := by
  classical
  let Sco : Set ℝ := Set.Ico 0 eta
  let Soo : Set ℝ := Set.Ioo 0 eta
  have hSco_convex : Convex ℝ Sco := by simpa [Sco] using convex_Ico (0 : ℝ) eta
  have hfun_eq : (fun x : ℝ ↦ ∑ i ∈ t, phiI i x) = (∑ i ∈ t, phiI i) := by
    funext x
    simp
  have hconc : ConcaveOn ℝ Sco (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) := by
    have hconc_all : ∀ u : Finset ι,
        (∀ i ∈ u, eta ≤ etaI i) →
        (∀ i ∈ u, DesingularizingFunction (etaI i) (phiI i)) →
        ConcaveOn ℝ Sco (fun s : ℝ ↦ ∑ i ∈ u, phiI i s) := by
      intro u hu_eta hu_phi
      induction u using Finset.induction_on with
      | empty =>
          simp [Sco, concaveOn_const (𝕜 := ℝ) (s := Sco) (0 : ℝ) hSco_convex]
      | insert a s has ih =>
          have ha_mem : a ∈ insert a s := by simp
          have hs_mem : ∀ i ∈ s, i ∈ insert a s := fun i hi ↦ Finset.mem_insert_of_mem hi
          have ha_conc : ConcaveOn ℝ Sco (phiI a) := by
            exact ((hu_phi a ha_mem).2.1).subset
              (by
                intro x hx
                exact ⟨hx.1, lt_of_lt_of_le hx.2 (hu_eta a ha_mem)⟩)
              hSco_convex
          have hs_conc : ConcaveOn ℝ Sco (fun x : ℝ ↦ ∑ i ∈ s, phiI i x) :=
            ih (fun i hi ↦ hu_eta i (hs_mem i hi))
              (fun i hi ↦ hu_phi i (hs_mem i hi))
          simpa [Finset.sum_insert has] using ha_conc.add hs_conc
    exact hconc_all t heta_le hphi
  have hzero : (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) 0 = 0 := by
    simp [Finset.sum_eq_zero (fun i hi ↦ (hphi i hi).2.2.1)]
  have hcontDiff : ContDiffOn ℝ 1 (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) Soo := by
    have hcd_all : ∀ u : Finset ι,
        (∀ i ∈ u, eta ≤ etaI i) →
        (∀ i ∈ u, DesingularizingFunction (etaI i) (phiI i)) →
        ContDiffOn ℝ 1 (fun s : ℝ ↦ ∑ i ∈ u, phiI i s) Soo := by
      intro u hu_eta hu_phi
      induction u using Finset.induction_on with
      | empty => simpa using (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) Soo)
      | insert a s has ih =>
          have ha_mem : a ∈ insert a s := by simp
          have hs_mem : ∀ i ∈ s, i ∈ insert a s := fun i hi ↦ Finset.mem_insert_of_mem hi
          have ha_cd : ContDiffOn ℝ 1 (phiI a) Soo :=
            ((hu_phi a ha_mem).2.2.2.1).mono
              (by
                intro x hx
                exact ⟨hx.1, lt_of_lt_of_le hx.2 (hu_eta a ha_mem)⟩)
          have hs_cd : ContDiffOn ℝ 1 (fun x : ℝ ↦ ∑ i ∈ s, phiI i x) Soo :=
            ih (fun i hi ↦ hu_eta i (hs_mem i hi))
              (fun i hi ↦ hu_phi i (hs_mem i hi))
          simpa [Finset.sum_insert has] using ha_cd.add hs_cd
    exact hcd_all t heta_le hphi
  have hcont : ContinuousAt (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) 0 := by
    have hcont_all : ∀ u : Finset ι,
        (∀ i ∈ u, DesingularizingFunction (etaI i) (phiI i)) →
        ContinuousAt (fun s : ℝ ↦ ∑ i ∈ u, phiI i s) 0 := by
      intro u hu_phi
      induction u using Finset.induction_on with
      | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) 0)
      | insert a s has ih =>
          have ha_mem : a ∈ insert a s := by simp
          have hs_mem : ∀ i ∈ s, i ∈ insert a s := fun i hi ↦ Finset.mem_insert_of_mem hi
          have ha_cont : ContinuousAt (phiI a) 0 := (hu_phi a ha_mem).2.2.2.2.1
          have hs_cont : ContinuousAt (fun x : ℝ ↦ ∑ i ∈ s, phiI i x) 0 :=
            ih (fun i hi ↦ hu_phi i (hs_mem i hi))
          simpa [Finset.sum_insert has] using ha_cont.add hs_cont
    exact hcont_all t hphi
  have hderiv_pos : ∀ s ∈ Soo, 0 < deriv (fun x : ℝ ↦ ∑ i ∈ t, phiI i x) s := by
    intro s hs
    have hs_i : ∀ i ∈ t, s ∈ Set.Ioo 0 (etaI i) := by
      intro i hi
      exact ⟨hs.1, lt_of_lt_of_le hs.2 (heta_le i hi)⟩
    have hdiffAt : ∀ i ∈ t, DifferentiableAt ℝ (phiI i) s := by
      intro i hi
      exact (((hphi i hi).2.2.2.1).differentiableOn (by norm_num) s (hs_i i hi)).differentiableAt
        (isOpen_Ioo.mem_nhds (hs_i i hi))
    rw [hfun_eq, deriv_sum hdiffAt]
    exact Finset.sum_pos
      (fun i hi ↦ (hphi i hi).2.2.2.2.2 s (hs_i i hi)) ht
  exact ⟨heta_pos, by simpa [Sco] using hconc, hzero,
    by simpa [Soo] using hcontDiff, hcont, by simpa [Soo] using hderiv_pos⟩

/-- Uniformized KL inequality on a compact set where the function is constant. -/
theorem uniformized_KL (Omega : Set E) (f : E → EReal)
    (hcompact : IsCompact Omega)
    (_hproper : IsProper f) (_hlsc : LowerSemicontinuous f)
    (hconstant : ∀ x ∈ Omega, ∀ y ∈ Omega, f x = f y)
    (hKL : ∀ x ∈ Omega, HasKLPropertyAt f x) :
    ∃ epsilon eta : ℝ, ∃ phi : ℝ → ℝ,
      0 < epsilon ∧ 0 < eta ∧ DesingularizingFunction eta phi ∧
        ∀ xbar ∈ Omega, ∀ x : E,
          Metric.infDist x Omega < epsilon →
          f xbar < f x →
          f x < addReal (f xbar) eta →
          (1 : ENNReal) ≤ ENNReal.ofReal
              (deriv phi ((f x).toReal - (f xbar).toReal)) *
            Metric.infEDist (0 : E) (limitingSubdifferential f x) := by
  classical
  by_cases hOmega_nonempty : Omega.Nonempty
  · choose etaLoc ULoc phiLoc hLoc using fun z hz ↦ (hKL z hz).2
    have hetaLoc : ∀ z, ∀ hz : z ∈ Omega, 0 < etaLoc z hz :=
      fun z hz ↦ (hLoc z hz).1
    have hULoc : ∀ z, ∀ hz : z ∈ Omega, ULoc z hz ∈ nhds z :=
      fun z hz ↦ (hLoc z hz).2.1
    have hphiLoc : ∀ z, ∀ hz : z ∈ Omega,
        DesingularizingFunction (etaLoc z hz) (phiLoc z hz) :=
      fun z hz ↦ (hLoc z hz).2.2.1
    have hineqLoc : ∀ z, ∀ hz : z ∈ Omega, ∀ x ∈ ULoc z hz,
        f z < f x → f x < addReal (f z) (etaLoc z hz) →
        (1 : ENNReal) ≤ ENNReal.ofReal
            (deriv (phiLoc z hz) ((f x).toReal - (f z).toReal)) *
          Metric.infEDist (0 : E) (limitingSubdifferential f x) := by
      intro z hz
      exact (hLoc z hz).2.2.2
    have hball_exists : ∀ z, ∀ hz : z ∈ Omega,
        ∃ rho : ℝ, 0 < rho ∧ Metric.ball z rho ⊆ ULoc z hz := by
      intro z hz
      exact Metric.mem_nhds_iff.mp (hULoc z hz)
    choose rhoLoc hrhoLoc hballLoc using hball_exists
    let cover : E → Set E := fun z ↦
      if hz : z ∈ Omega then Metric.ball z (rhoLoc z hz / 2) else Set.univ
    have hcover_nhds : ∀ z ∈ Omega, cover z ∈ nhds z := by
      intro z hz
      have hpos : 0 < rhoLoc z hz / 2 := by linarith [hrhoLoc z hz]
      simpa [cover, hz] using Metric.ball_mem_nhds z hpos
    rcases hcompact.elim_nhds_subcover cover hcover_nhds with ⟨t, htOmega, hcover⟩
    have hcover_ball : ∀ y ∈ Omega, ∃ i, ∃ hi : i ∈ t,
        dist y i < rhoLoc i (htOmega i hi) / 2 := by
      intro y hy
      rcases Set.mem_iUnion.mp (hcover hy) with ⟨i, hiUnion⟩
      rcases Set.mem_iUnion.mp hiUnion with ⟨hi, hycover⟩
      refine ⟨i, hi, ?_⟩
      simpa [cover, htOmega i hi, Metric.mem_ball] using hycover
    have htNonempty : t.Nonempty := by
      rcases hOmega_nonempty with ⟨y0, hy0⟩
      rcases hcover_ball y0 hy0 with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    let etaI : E → ℝ := fun i ↦ if hi : i ∈ t then etaLoc i (htOmega i hi) else 1
    let phiI : E → ℝ → ℝ := fun i ↦
      if hi : i ∈ t then phiLoc i (htOmega i hi) else fun s : ℝ ↦ s
    let rhoI : E → ℝ := fun i ↦
      if hi : i ∈ t then rhoLoc i (htOmega i hi) / 2 else 1
    have hetaI_pos : ∀ i ∈ t, 0 < etaI i := by
      intro i hi
      simp [etaI, hi, hetaLoc i (htOmega i hi)]
    have hrhoI_pos : ∀ i ∈ t, 0 < rhoI i := by
      intro i hi
      have hpos : 0 < rhoLoc i (htOmega i hi) / 2 := by linarith [hrhoLoc i (htOmega i hi)]
      simpa [rhoI, hi] using hpos
    have hphiI : ∀ i ∈ t, DesingularizingFunction (etaI i) (phiI i) := by
      intro i hi
      simpa [etaI, phiI, hi] using hphiLoc i (htOmega i hi)
    let epsilon : ℝ := t.inf' htNonempty rhoI
    let eta : ℝ := t.inf' htNonempty etaI
    let Phi : ℝ → ℝ := fun s : ℝ ↦ ∑ i ∈ t, phiI i s
    have hepsilon_pos : 0 < epsilon := finset_inf'_pos htNonempty rhoI hrhoI_pos
    have heta_pos : 0 < eta := finset_inf'_pos htNonempty etaI hetaI_pos
    have hepsilon_le : ∀ i ∈ t, epsilon ≤ rhoI i := fun i hi ↦ Finset.inf'_le rhoI hi
    have heta_le : ∀ i ∈ t, eta ≤ etaI i := fun i hi ↦ Finset.inf'_le etaI hi
    have hPhi_desing : DesingularizingFunction eta Phi := by
      simpa [Phi] using
        desingularizingFunction_finsetSum htNonempty eta etaI phiI heta_pos heta_le hphiI
    refine ⟨epsilon, eta, Phi, hepsilon_pos, heta_pos, hPhi_desing, ?_⟩
    intro xbar hxbar x hdist hlo hhi
    have hcover_rhoI : ∀ y ∈ Omega, ∃ i ∈ t, dist y i < rhoI i := by
      intro y hy
      rcases hcover_ball y hy with ⟨i, hi, hdistyi⟩
      exact ⟨i, hi, by simpa [rhoI, hi] using hdistyi⟩
    rcases tube_cover_of_infDist_lt_finset_inf htNonempty (fun i : E ↦ i)
        rhoI hrhoI_pos hcover_rhoI epsilon hepsilon_le hOmega_nonempty x hdist with
      ⟨i, hi, hxi_two⟩
    have hiOmega : i ∈ Omega := htOmega i hi
    have hxi_rho : dist x i < rhoLoc i hiOmega := by
      have hxi' : dist x i < 2 * (rhoLoc i hiOmega / 2) := by
        simpa [rhoI, hi] using hxi_two
      nlinarith [hxi', hrhoLoc i hiOmega]
    have hxU : x ∈ ULoc i hiOmega :=
      hballLoc i hiOmega (by simpa [Metric.mem_ball] using hxi_rho)
    have hfxbar_i : f xbar = f i := hconstant xbar hxbar i hiOmega
    have hlo_i : f i < f x := by simpa [hfxbar_i] using hlo
    have hhi_eta : f x < addReal (f i) eta := by simpa [hfxbar_i] using hhi
    have hhi_i : f x < addReal (f i) (etaI i) :=
      lt_of_lt_of_le hhi_eta (addReal_mono (heta_le i hi))
    have hhi_loc : f x < addReal (f i) (etaLoc i hiOmega) := by
      simpa [etaI, hi] using hhi_i
    have hlocal := hineqLoc i hiOmega x hxU hlo_i hhi_loc
    let s : ℝ := (f x).toReal - (f i).toReal
    let D : ENNReal := Metric.infEDist (0 : E) (limitingSubdifferential f x)
    have hlocal' : (1 : ENNReal) ≤ ENNReal.ofReal (deriv (phiI i) s) * D := by
      simpa [s, D, phiI, hi] using hlocal
    have hfinite_i := finite_at_mem_limitingSubdifferentialDomain (hKL i hiOmega).1
    have hs_eta : s ∈ Set.Ioo 0 eta :=
      toReal_sub_mem_Ioo_of_addReal_window heta_pos hfinite_i.1 hfinite_i.2 hlo_i hhi_eta
    have hs_j : ∀ j ∈ t, s ∈ Set.Ioo 0 (etaI j) := by
      intro j hj
      exact ⟨hs_eta.1, lt_of_lt_of_le hs_eta.2 (heta_le j hj)⟩
    have hdiffAt : ∀ j ∈ t, DifferentiableAt ℝ (phiI j) s := by
      intro j hj
      exact (((hphiI j hj).2.2.2.1).differentiableOn (by norm_num) s (hs_j j hj)).differentiableAt
        (isOpen_Ioo.mem_nhds (hs_j j hj))
    have hderiv_sum : deriv Phi s = ∑ j ∈ t, deriv (phiI j) s := by
      have hPhi_eq : Phi = (∑ j ∈ t, phiI j) := by
        funext r
        simp [Phi]
      rw [hPhi_eq]
      exact deriv_sum hdiffAt
    have hderiv_nonneg : ∀ j ∈ t, 0 ≤ deriv (phiI j) s := by
      intro j hj
      exact le_of_lt ((hphiI j hj).2.2.2.2.2 s (hs_j j hj))
    have hderiv_le : deriv (phiI i) s ≤ deriv Phi s := by
      rw [hderiv_sum]
      exact Finset.single_le_sum hderiv_nonneg hi
    have hmul : ENNReal.ofReal (deriv (phiI i) s) * D ≤
        ENNReal.ofReal (deriv Phi s) * D := by
      gcongr
    exact le_trans hlocal' (by simpa [s, D, hfxbar_i] using hmul)
  · refine ⟨1, 1, fun s : ℝ ↦ s, by norm_num, by norm_num,
      desingularizingFunction_id, ?_⟩
    intro xbar hxbar
    exact False.elim (hOmega_nonempty ⟨xbar, hxbar⟩)

/-- A KL function satisfies the uniformized KL inequality on every compact set on which it is
constant. -/
theorem IsKLFunction.uniformized {f : E → EReal} (hf : IsKLFunction f)
    (Omega : Set E) (hcompact : IsCompact Omega)
    (hOmega_domain : Omega ⊆ limitingSubdifferentialDomain f)
    (hconstant : ∀ x ∈ Omega, ∀ y ∈ Omega, f x = f y) :
    ∃ epsilon eta : ℝ, ∃ phi : ℝ → ℝ,
      0 < epsilon ∧ 0 < eta ∧ DesingularizingFunction eta phi ∧
        ∀ xbar ∈ Omega, ∀ x : E,
          Metric.infDist x Omega < epsilon →
          f xbar < f x →
          f x < addReal (f xbar) eta →
          (1 : ENNReal) ≤ ENNReal.ofReal
              (deriv phi ((f x).toReal - (f xbar).toReal)) *
            Metric.infEDist (0 : E) (limitingSubdifferential f x) := by
  exact uniformized_KL Omega f hcompact hf.1 hf.2.1 hconstant
    (fun x hx ↦ hf.2.2 x (hOmega_domain hx))

end

end ERealFunction
