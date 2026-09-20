import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_2

open Filter
open scoped Topology

namespace BotCsetnek2015

open ERealFunction

theorem desingularizingFunction_id :
    DesingularizingFunction 1 (fun s : ℝ ↦ s) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using
      (concaveOn_id (𝕜 := ℝ) (s := Set.Icc (0 : ℝ) 1)
        (convex_Icc (0 : ℝ) 1))
  · simpa using
      (continuousOn_id :
        ContinuousOn (fun s : ℝ ↦ s) (Set.Icc (0 : ℝ) 1))
  · simpa using
      (differentiableOn_id :
        DifferentiableOn ℝ (fun s : ℝ ↦ s) (Set.Ioo (0 : ℝ) 1))
  · rfl
  · intro s hs
    simp

theorem finset_inf'_pos {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (g : α → ℝ) (hg : ∀ a ∈ s, 0 < g a) :
    0 < s.inf' hs g := by
  rw [Finset.lt_inf'_iff]
  exact hg

theorem tube_cover_of_infDist_lt_finset_inf {m : ℕ}
    {Omega : Set (EuclideanSpace m)}
    {ι : Type*} [DecidableEq ι]
    {t : Finset ι} (_ht : t.Nonempty)
    (center : ι → EuclideanSpace m) (r : ι → ℝ)
    (_hr_pos : ∀ i ∈ t, 0 < r i)
    (hcover : ∀ y ∈ Omega, ∃ i ∈ t, dist y (center i) < r i)
    (epsilon : ℝ)
    (heps_le : ∀ i ∈ t, epsilon ≤ r i)
    (hOmega_nonempty : Omega.Nonempty) :
    ∀ x, distToSet x Omega < epsilon →
      ∃ i ∈ t, dist x (center i) < 2 * r i := by
  intro x hdist
  rw [distToSet] at hdist
  rcases (Metric.infDist_lt_iff hOmega_nonempty).mp hdist with ⟨y, hyOmega, hxy⟩
  rcases hcover y hyOmega with ⟨i, hi, hyi⟩
  refine ⟨i, hi, ?_⟩
  calc
    dist x (center i) ≤ dist x y + dist y (center i) := dist_triangle x y (center i)
    _ < epsilon + r i := add_lt_add hxy hyi
    _ ≤ r i + r i := add_le_add (heps_le i hi) le_rfl
    _ = 2 * r i := by ring

theorem erealAddReal_le_of_le {a : EReal} {r s : ℝ}
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

theorem toReal_sub_mem_Ioo_of_ereal_window
    {a b : EReal} {eta : ℝ} (_heta : 0 < eta)
    (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hlo : a < b) (hhi : b < erealAddReal a eta) :
    (b.toReal - a.toReal) ∈ Set.Ioo 0 eta := by
  cases a using EReal.rec with
  | bot =>
      exact False.elim (ha_bot rfl)
  | top =>
      exact False.elim (ha_top rfl)
  | coe ar =>
      cases b using EReal.rec with
      | bot =>
          simp at hlo
      | top =>
          change (⊤ : EReal) < ((ar + eta : ℝ) : EReal) at hhi
          simp at hhi
      | coe br =>
          change ((ar : EReal) < (br : EReal)) at hlo
          change ((br : EReal) < ((ar + eta : ℝ) : EReal)) at hhi
          have hlo_real : ar < br := EReal.coe_lt_coe_iff.mp hlo
          have hhi_real : br < ar + eta := EReal.coe_lt_coe_iff.mp hhi
          constructor <;> simp [EReal.toReal_coe] <;> linarith

theorem effective_finite_of_limitingSubdifferentialDomain {m : ℕ}
    {f : EuclideanSpace m → EReal} {x : EuclideanSpace m}
    (hx : x ∈ limitingSubdifferentialDomain f) :
    f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  rcases hx with ⟨v, hv⟩
  exact (ERealFunction.mem_effectiveDom_iff f x).mp hv.1

theorem desingularizingFunction_finset_sum_restrict {ι : Type*}
    [DecidableEq ι] {t : Finset ι} (ht : t.Nonempty)
    (eta : ℝ) (etaI : ι → ℝ) (phiI : ι → ℝ → ℝ)
    (heta_pos : 0 < eta)
    (heta_le : ∀ i, i ∈ t → eta ≤ etaI i)
    (hphi : ∀ i, i ∈ t → DesingularizingFunction (etaI i) (phiI i)) :
    DesingularizingFunction eta (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) := by
  classical
  let Scc : Set ℝ := Set.Icc 0 eta
  let Soo : Set ℝ := Set.Ioo 0 eta
  have hScc_convex : Convex ℝ Scc := by
    simpa [Scc] using convex_Icc (0 : ℝ) eta
  have hfun_eq : (fun x : ℝ ↦ ∑ i ∈ t, phiI i x) = (∑ i ∈ t, phiI i) := by
    funext x
    simp
  have hconc :
      ConcaveOn ℝ Scc (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) := by
    have hconc_all :
        ∀ u : Finset ι,
          (∀ i, i ∈ u → eta ≤ etaI i) →
          (∀ i, i ∈ u → DesingularizingFunction (etaI i) (phiI i)) →
          ConcaveOn ℝ Scc (fun s : ℝ ↦ ∑ i ∈ u, phiI i s) := by
      intro u hu_eta hu_phi
      induction u using Finset.induction_on with
      | empty =>
          simp [Scc, concaveOn_const (𝕜 := ℝ) (s := Scc) (0 : ℝ) hScc_convex]
      | insert a s has ih =>
        have ha_mem : a ∈ insert a s := by simp
        have hs_mem : ∀ i ∈ s, i ∈ insert a s := by
          intro i hi
          exact Finset.mem_insert_of_mem hi
        have ha_conc :
            ConcaveOn ℝ Scc (phiI a) := by
          exact ((hu_phi a ha_mem).2.1).subset
            (by
              intro x hx
              exact ⟨hx.1, le_trans hx.2 (hu_eta a ha_mem)⟩)
            hScc_convex
        have hs_conc :
            ConcaveOn ℝ Scc (fun x : ℝ ↦ ∑ i ∈ s, phiI i x) := by
          exact ih (fun i hi ↦ hu_eta i (hs_mem i hi))
            (fun i hi ↦ hu_phi i (hs_mem i hi))
        simpa [Finset.sum_insert has] using ha_conc.add hs_conc
    exact hconc_all t heta_le hphi
  have hcont :
      ContinuousOn (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) Scc := by
    have hcont_all :
        ∀ u : Finset ι,
          (∀ i, i ∈ u → eta ≤ etaI i) →
          (∀ i, i ∈ u → DesingularizingFunction (etaI i) (phiI i)) →
          ContinuousOn (fun s : ℝ ↦ ∑ i ∈ u, phiI i s) Scc := by
      intro u hu_eta hu_phi
      induction u using Finset.induction_on with
      | empty =>
          simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) Scc)
      | insert a s has ih =>
        have ha_mem : a ∈ insert a s := by simp
        have hs_mem : ∀ i ∈ s, i ∈ insert a s := by
          intro i hi
          exact Finset.mem_insert_of_mem hi
        have ha_cont : ContinuousOn (phiI a) Scc := by
          exact ((hu_phi a ha_mem).2.2.1).mono
            (by
              intro x hx
              exact ⟨hx.1, le_trans hx.2 (hu_eta a ha_mem)⟩)
        have hs_cont : ContinuousOn (fun x : ℝ ↦ ∑ i ∈ s, phiI i x) Scc := by
          exact ih (fun i hi ↦ hu_eta i (hs_mem i hi))
            (fun i hi ↦ hu_phi i (hs_mem i hi))
        simpa [Finset.sum_insert has] using ha_cont.add hs_cont
    exact hcont_all t heta_le hphi
  have hdiff :
      DifferentiableOn ℝ (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) Soo := by
    have hdiff_all :
        ∀ u : Finset ι,
          (∀ i, i ∈ u → eta ≤ etaI i) →
          (∀ i, i ∈ u → DesingularizingFunction (etaI i) (phiI i)) →
          DifferentiableOn ℝ (fun s : ℝ ↦ ∑ i ∈ u, phiI i s) Soo := by
      intro u hu_eta hu_phi
      induction u using Finset.induction_on with
      | empty =>
          simpa using
            (differentiableOn_const (c := (0 : ℝ)) :
              DifferentiableOn ℝ (fun _ : ℝ ↦ (0 : ℝ)) Soo)
      | insert a s has ih =>
        have ha_mem : a ∈ insert a s := by simp
        have hs_mem : ∀ i ∈ s, i ∈ insert a s := by
          intro i hi
          exact Finset.mem_insert_of_mem hi
        have ha_diff : DifferentiableOn ℝ (phiI a) Soo := by
          exact ((hu_phi a ha_mem).2.2.2.1).mono
            (by
              intro x hx
              exact ⟨hx.1, lt_of_lt_of_le hx.2 (hu_eta a ha_mem)⟩)
        have hs_diff :
            DifferentiableOn ℝ (fun x : ℝ ↦ ∑ i ∈ s, phiI i x) Soo := by
          exact ih (fun i hi ↦ hu_eta i (hs_mem i hi))
            (fun i hi ↦ hu_phi i (hs_mem i hi))
        simpa [Finset.sum_insert has] using ha_diff.add hs_diff
    exact hdiff_all t heta_le hphi
  have hzero : (fun s : ℝ ↦ ∑ i ∈ t, phiI i s) 0 = 0 := by
    simp [Finset.sum_eq_zero (fun i hi ↦ (hphi i hi).2.2.2.2.1)]
  have hderiv_pos :
      ∀ s ∈ Soo, 0 < deriv (fun x : ℝ ↦ ∑ i ∈ t, phiI i x) s := by
    intro s hs
    have hs_i : ∀ i ∈ t, s ∈ Set.Ioo 0 (etaI i) := by
      intro i hi
      exact ⟨hs.1, lt_of_lt_of_le hs.2 (heta_le i hi)⟩
    have hdiffAt : ∀ i ∈ t, DifferentiableAt ℝ (phiI i) s := by
      intro i hi
      exact ((hphi i hi).2.2.2.1).differentiableAt
        ((isOpen_Ioo.mem_nhds (hs_i i hi)))
    rw [hfun_eq]
    rw [deriv_sum hdiffAt]
    exact Finset.sum_pos
      (fun i hi ↦ (hphi i hi).2.2.2.2.2 s (hs_i i hi)) ht
  exact ⟨heta_pos, by simpa [Scc] using hconc, by simpa [Scc] using hcont,
    by simpa [Soo] using hdiff, hzero, by simpa [Soo] using hderiv_pos⟩

/-- Lemma 2.1: uniformized KL inequality on a compact set where `f` is constant. -/
theorem lemma_2_1_uniformized_KL {m : ℕ} (Omega : Set (EuclideanSpace m))
    (f : EuclideanSpace m → EReal)
    (hcompact : IsCompact Omega)
    (hproper : ERealFunction.IsProper f)
    (hlsc : LowerSemicontinuous f)
    (hconstant : ∀ x ∈ Omega, ∀ y ∈ Omega, f x = f y)
    (hKL : ∀ x ∈ Omega, KLPropertyAt f x) :
    ∃ epsilon eta : ℝ, ∃ phi : ℝ → ℝ,
      0 < epsilon ∧ 0 < eta ∧ DesingularizingFunction eta phi ∧
        ∀ xbar ∈ Omega, ∀ x : EuclideanSpace m,
          distToSet x Omega < epsilon →
          f xbar < f x →
          f x < erealAddReal (f xbar) eta →
          1 ≤ deriv phi ((f x).toReal - (f xbar).toReal) *
            distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x) := by
  classical
  by_cases hOmega_nonempty : Omega.Nonempty
  · choose etaLoc ULoc phiLoc hLoc using fun z hz ↦ (hKL z hz).2
    have hetaLoc : ∀ z, ∀ hz : z ∈ Omega, 0 < etaLoc z hz := by
      intro z hz
      exact (hLoc z hz).1
    have hULoc : ∀ z, ∀ hz : z ∈ Omega, ULoc z hz ∈ nhds z := by
      intro z hz
      exact (hLoc z hz).2.1
    have hphiLoc :
        ∀ z, ∀ hz : z ∈ Omega,
          DesingularizingFunction (etaLoc z hz) (phiLoc z hz) := by
      intro z hz
      exact (hLoc z hz).2.2.1
    have hineqLoc :
        ∀ z, ∀ hz : z ∈ Omega, ∀ x ∈ ULoc z hz,
          f z < f x →
          f x < erealAddReal (f z) (etaLoc z hz) →
          1 ≤ deriv (phiLoc z hz) ((f x).toReal - (f z).toReal) *
            distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x) := by
      intro z hz
      exact (hLoc z hz).2.2.2
    have hball_exists :
        ∀ z, ∀ hz : z ∈ Omega,
          ∃ rho : ℝ, 0 < rho ∧ Metric.ball z rho ⊆ ULoc z hz := by
      intro z hz
      exact Metric.mem_nhds_iff.mp (hULoc z hz)
    choose rhoLoc hrhoLoc hballLoc using hball_exists
    let cover : EuclideanSpace m → Set (EuclideanSpace m) :=
      fun z ↦ if hz : z ∈ Omega then Metric.ball z (rhoLoc z hz / 2) else Set.univ
    have hcover_nhds : ∀ z ∈ Omega, cover z ∈ nhds z := by
      intro z hz
      have hpos : 0 < rhoLoc z hz / 2 := by linarith [hrhoLoc z hz]
      have hball : Metric.ball z (rhoLoc z hz / 2) ∈ nhds z :=
        Metric.ball_mem_nhds z hpos
      simpa [cover, hz] using hball
    rcases hcompact.elim_nhds_subcover cover hcover_nhds with ⟨t, htOmega, hcover⟩
    have hcover_ball :
        ∀ y ∈ Omega, ∃ i, ∃ hi : i ∈ t,
          dist y i < rhoLoc i (htOmega i hi) / 2 := by
      intro y hy
      rcases Set.mem_iUnion.mp (hcover hy) with ⟨i, hiUnion⟩
      rcases Set.mem_iUnion.mp hiUnion with ⟨hi, hycover⟩
      refine ⟨i, hi, ?_⟩
      have hiOmega : i ∈ Omega := htOmega i hi
      simpa [cover, hiOmega, Metric.mem_ball] using hycover
    have htNonempty : t.Nonempty := by
      rcases hOmega_nonempty with ⟨y0, hy0⟩
      rcases hcover_ball y0 hy0 with ⟨i, hi, _⟩
      exact ⟨i, hi⟩
    let etaI : EuclideanSpace m → ℝ :=
      fun i ↦ if hi : i ∈ t then etaLoc i (htOmega i hi) else 1
    let phiI : EuclideanSpace m → ℝ → ℝ :=
      fun i ↦ if hi : i ∈ t then phiLoc i (htOmega i hi) else fun s : ℝ ↦ s
    let rhoI : EuclideanSpace m → ℝ :=
      fun i ↦ if hi : i ∈ t then rhoLoc i (htOmega i hi) / 2 else 1
    have hetaI_pos : ∀ i ∈ t, 0 < etaI i := by
      intro i hi
      simp [etaI, hi, hetaLoc i (htOmega i hi)]
    have hrhoI_pos : ∀ i ∈ t, 0 < rhoI i := by
      intro i hi
      have hpos : 0 < rhoLoc i (htOmega i hi) / 2 := by
        linarith [hrhoLoc i (htOmega i hi)]
      simpa [rhoI, hi] using hpos
    have hphiI : ∀ i ∈ t, DesingularizingFunction (etaI i) (phiI i) := by
      intro i hi
      simpa [etaI, phiI, hi] using hphiLoc i (htOmega i hi)
    let epsilon : ℝ := t.inf' htNonempty rhoI
    let eta : ℝ := t.inf' htNonempty etaI
    let Phi : ℝ → ℝ := fun s : ℝ ↦ ∑ i ∈ t, phiI i s
    have hepsilon_pos : 0 < epsilon := by
      exact finset_inf'_pos htNonempty rhoI hrhoI_pos
    have heta_pos : 0 < eta := by
      exact finset_inf'_pos htNonempty etaI hetaI_pos
    have hepsilon_le : ∀ i ∈ t, epsilon ≤ rhoI i := by
      intro i hi
      exact Finset.inf'_le rhoI hi
    have heta_le : ∀ i ∈ t, eta ≤ etaI i := by
      intro i hi
      exact Finset.inf'_le etaI hi
    have hPhi_desing : DesingularizingFunction eta Phi := by
      simpa [Phi] using
        desingularizingFunction_finset_sum_restrict htNonempty eta etaI phiI
          heta_pos heta_le hphiI
    refine ⟨epsilon, eta, Phi, hepsilon_pos, heta_pos, hPhi_desing, ?_⟩
    intro xbar hxbar x hdist hlo hhi
    have hcover_rhoI : ∀ y ∈ Omega, ∃ i ∈ t, dist y i < rhoI i := by
      intro y hy
      rcases hcover_ball y hy with ⟨i, hi, hdistyi⟩
      refine ⟨i, hi, ?_⟩
      simpa [rhoI, hi] using hdistyi
    rcases tube_cover_of_infDist_lt_finset_inf htNonempty (fun i : EuclideanSpace m ↦ i)
        rhoI hrhoI_pos hcover_rhoI epsilon hepsilon_le hOmega_nonempty x hdist with
      ⟨i, hi, hxi_two⟩
    have hiOmega : i ∈ Omega := htOmega i hi
    have hxi_rho : dist x i < rhoLoc i hiOmega := by
      have hxi' : dist x i < 2 * (rhoLoc i hiOmega / 2) := by
        simpa [rhoI, hi] using hxi_two
      nlinarith [hxi', hrhoLoc i hiOmega]
    have hxU : x ∈ ULoc i hiOmega := by
      exact hballLoc i hiOmega (by simpa [Metric.mem_ball] using hxi_rho)
    have hfxbar_i : f xbar = f i := hconstant xbar hxbar i hiOmega
    have hlo_i : f i < f x := by
      simpa [hfxbar_i] using hlo
    have hhi_eta : f x < erealAddReal (f i) eta := by
      simpa [hfxbar_i] using hhi
    have hhi_i : f x < erealAddReal (f i) (etaI i) := by
      exact lt_of_lt_of_le hhi_eta (erealAddReal_le_of_le (heta_le i hi))
    have hhi_loc : f x < erealAddReal (f i) (etaLoc i hiOmega) := by
      simpa [etaI, hi] using hhi_i
    have hlocal_loc :
        1 ≤ deriv (phiLoc i hiOmega) ((f x).toReal - (f i).toReal) *
          distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x) :=
      hineqLoc i hiOmega x hxU hlo_i hhi_loc
    let s : ℝ := (f x).toReal - (f i).toReal
    let D : ℝ := distToSet (0 : EuclideanSpace m) (limitingSubdifferential f x)
    have hlocal :
        1 ≤ deriv (phiI i) s * D := by
      simpa [s, D, phiI, hi] using hlocal_loc
    have hfinite_i := effective_finite_of_limitingSubdifferentialDomain (hKL i hiOmega).1
    have hs_eta : s ∈ Set.Ioo 0 eta := by
      exact toReal_sub_mem_Ioo_of_ereal_window heta_pos hfinite_i.1 hfinite_i.2
        hlo_i hhi_eta
    have hs_j : ∀ j ∈ t, s ∈ Set.Ioo 0 (etaI j) := by
      intro j hj
      exact ⟨hs_eta.1, lt_of_lt_of_le hs_eta.2 (heta_le j hj)⟩
    have hdiffAt : ∀ j ∈ t, DifferentiableAt ℝ (phiI j) s := by
      intro j hj
      exact ((hphiI j hj).2.2.2.1).differentiableAt
        (isOpen_Ioo.mem_nhds (hs_j j hj))
    have hderiv_sum :
        deriv Phi s = ∑ j ∈ t, deriv (phiI j) s := by
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
    have hD_nonneg : 0 ≤ D := by
      unfold D distToSet
      exact Metric.infDist_nonneg
    have hmul : deriv (phiI i) s * D ≤ deriv Phi s * D :=
      mul_le_mul_of_nonneg_right hderiv_le hD_nonneg
    have hchain : 1 ≤ deriv Phi s * D := le_trans hlocal hmul
    simpa [s, D, hfxbar_i] using hchain
  · refine ⟨1, 1, fun s : ℝ ↦ s, ?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · exact desingularizingFunction_id
    · intro xbar hxbar
      exact False.elim (hOmega_nonempty ⟨xbar, hxbar⟩)

end BotCsetnek2015
