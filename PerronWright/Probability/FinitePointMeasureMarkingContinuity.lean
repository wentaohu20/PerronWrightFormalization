import PerronWright.Probability.FinitePointMeasureMarking
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform continuity of point-measure tests under near-constant marks -/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FinitePointMeasureMarkingContinuity

open FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
  [MetricSpace E] [MetricSpace A] [CompactSpace E] [CompactSpace A] [BorelSpace E] [BorelSpace A]

/-- One genuine mark neighborhood controls every atom position and every
point count below the cutoff. This follows from actual compact atom-map
images and uniform continuity, not a point-process coupling interface. -/
theorem exists_mark_neighborhood (ν : A) (H : ℕ)
    (F : PointMeasure (E × A) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set A, U ∈ 𝓝 ν ∧ ∀ m ≤ H, ∀ x : Fin m → E, ∀ y : Fin m → A,
      (∀ i, y i ∈ U) →
        |F (ofAtomsPoint (fun i ↦ (x i,y i)))-F (constantMark ν (ofAtomsPoint x))| < ε := by
  have hc (m : Fin (H+1)) : Continuous
      (fun z : Fin m.val → E × A ↦ F (ofAtomsPoint z)) :=
    F.continuous.comp (continuous_ofAtomsPoint m.val)
  have hδ (m : Fin (H+1)) : ∃ δ > 0,
      ∀ z w : Fin m.val → E × A, dist z w < δ →
        dist (F (ofAtomsPoint z)) (F (ofAtomsPoint w)) < ε := by
    obtain ⟨δ,hδ,hp⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous (hc m)) ε hε
    exact ⟨δ,hδ,fun _ _ h ↦ hp h⟩
  choose δ hδpos hδprop using hδ
  let U := {v : A | ∀ m : Fin (H+1), dist v ν < δ m}
  have hU : U ∈ 𝓝 ν :=
    Filter.eventually_all.mpr (fun m ↦ Metric.ball_mem_nhds ν (hδpos m))
  refine ⟨U,hU,?_⟩
  intro m hm x y hy
  let j : Fin (H+1) := ⟨m,Nat.lt_succ_of_le hm⟩
  have hd : dist (fun i ↦ (x i,y i)) (fun i ↦ (x i,ν)) < δ j := by
    apply (dist_pi_lt_iff (hδpos j)).mpr
    intro i
    rw [dist_prod_same_left]
    exact hy i j
  have hh := hδprop j (fun i ↦ (x i,y i)) (fun i ↦ (x i,ν)) hd
  rw [constantMark,mapPoint_ofAtomsPoint]
  change |F (ofAtomsPoint (fun i ↦ (x i,y i)))-F (ofAtomsPoint (fun i ↦ (x i,ν)))| < ε
  simpa only [Real.dist_eq] using hh

omit [CompactSpace E] in
theorem ofFintype_mark_close (ν : A) (H : ℕ)
    (F : PointMeasure (E × A) →ᵇ ℝ) (ε : ℝ) (U : Set A)
    (hU : ∀ m ≤ H, ∀ x : Fin m → E, ∀ y : Fin m → A,
      (∀ i, y i ∈ U) →
        |F (ofAtomsPoint (fun i ↦ (x i,y i)))-F (constantMark ν (ofAtomsPoint x))| < ε)
    {I : Type*} [Fintype I] (hI : Fintype.card I ≤ H) (x : I → E) (y : I → A)
    (hy : ∀ i, y i ∈ U) :
    |F (ofFintype (fun i ↦ (x i,y i)))-F (constantMark ν (ofFintype x))| < ε := by
  rw [ofFintype_eq_ofAtomsPoint,ofFintype_eq_ofAtomsPoint x]
  exact hU (Fintype.card I) hI (fun i ↦ x ((Fintype.equivFin I).symm i))
    (fun i ↦ y ((Fintype.equivFin I).symm i)) (fun i ↦ hy _)

end PerronWright.FinitePointMeasureMarkingContinuity
