import Mathlib
import Foundation.Hilbert.WeakConvergence
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_5

open Filter
open scoped Topology

namespace BotCsetnek2015

lemma tendsto_infDist_mapClusterPt_of_isCompact {X : Type*} [MetricSpace X]
    {K : Set X} {z : Nat -> X} (hK : IsCompact K) (hzK : forall n, z n ∈ K) :
    Tendsto (fun n : Nat => Metric.infDist (z n) {x | MapClusterPt x atTop z}) atTop
      (nhds 0) := by
  classical
  let S : Set X := {x | MapClusterPt x atTop z}
  have hSnonempty : S.Nonempty := by
    obtain ⟨x, _hxK, hxcluster⟩ :=
      hK.exists_mapClusterPt (u := z) (f := atTop) (by
        exact tendsto_principal.mpr (Eventually.of_forall hzK))
    exact ⟨x, hxcluster⟩
  have hSclosed : IsClosed S := by
    simpa [S, MapClusterPt] using
      (isClosed_setOf_clusterPt : IsClosed {x | ClusterPt x (map z atTop)})
  refine Metric.tendsto_atTop.2 ?_
  intro eps heps
  by_contra hnot
  have hfreqAbs : ∃ᶠ n in atTop, eps ≤ |Metric.infDist (z n) S| := by
    rw [Filter.frequently_atTop]
    simpa [S, Filter.not_eventually, not_lt, Real.dist_eq] using hnot
  have hfreq : ∃ᶠ n in atTop, eps ≤ Metric.infDist (z n) S := by
    exact hfreqAbs.mono (by
      intro n hn
      simpa [abs_of_nonneg (Metric.infDist_nonneg)] using hn)
  let D : Set X := {x | x ∈ K ∧ eps ≤ Metric.infDist x S}
  have hDclosed : IsClosed D := by
    exact hK.isClosed.inter (isClosed_le continuous_const (Metric.continuous_infDist_pt S))
  have hDcompact : IsCompact D := hK.of_isClosed_subset hDclosed (by
    intro x hx
    exact hx.1)
  have hfreqD : ∃ᶠ n in atTop, z n ∈ D := by
    exact hfreq.mono (by
      intro n hn
      exact ⟨hzK n, hn⟩)
  obtain ⟨y, hyD, hycluster⟩ := hDcompact.exists_mapClusterPt_of_frequently hfreqD
  have hyS : y ∈ S := hycluster
  have hzero : Metric.infDist y S = 0 := Metric.infDist_zero_of_mem hyS
  have hpos : eps ≤ Metric.infDist y S := hyD.2
  linarith

lemma omega_eq_mapClusterPt {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (z : Nat -> X) :
    omega z = {x | MapClusterPt x atTop z} := by
  ext x
  constructor
  · intro hx
    exact IsSequentialClusterPt.mapClusterPt (by simpa [omega] using hx)
  · intro hx
    rcases MapClusterPt.tendsto_subseq hx with ⟨phi, hphi, hlim⟩
    exact ⟨phi, hphi, hlim⟩

/-- Cluster-set properties for bounded finite-dimensional sequences with vanishing increments. -/
theorem cluster_set_properties_of_vanishing_increments {m : Nat}
    (z : Nat -> EuclideanSpace m)
    (hbounded : Bornology.IsBounded (Set.range z))
    (hincrements : Tendsto (fun n : Nat => z (n + 1) - z n) atTop
      (nhds (0 : EuclideanSpace m))) :
    (omega z).Nonempty ∧ IsCompact (omega z) ∧ IsConnected (omega z) ∧
      Tendsto (fun n : Nat => Metric.infDist (z n) (omega z)) atTop (nhds 0) := by
  have hstep : Tendsto (fun n : Nat => z n - z (n + 1)) atTop
      (nhds (0 : EuclideanSpace m)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hincrements.neg
  have hcluster := sequenceClusterPointSet_isCompact_isConnected (x := z) hbounded hstep
  have hEq : omega z = {x | MapClusterPt x atTop z} := omega_eq_mapClusterPt z
  have hcompact : IsCompact (omega z) := by
    simpa [hEq] using hcluster.1
  have hconnected : IsConnected (omega z) := by
    simpa [hEq] using hcluster.2
  have hK : IsCompact (closure (Set.range z)) := by
    haveI : ProperSpace (EuclideanSpace m) :=
      FiniteDimensional.proper Real (EuclideanSpace m)
    simpa using hbounded.isCompact_closure
  have hzK : forall n : Nat, z n ∈ closure (Set.range z) := by
    intro n
    exact subset_closure ⟨n, rfl⟩
  have hdistMap := tendsto_infDist_mapClusterPt_of_isCompact
    (K := closure (Set.range z)) (z := z) hK hzK
  have hdist : Tendsto (fun n : Nat => Metric.infDist (z n) (omega z)) atTop
      (nhds 0) := by
    simpa [hEq] using hdistMap
  exact ⟨hconnected.1, hcompact, hconnected, hdist⟩

end BotCsetnek2015
