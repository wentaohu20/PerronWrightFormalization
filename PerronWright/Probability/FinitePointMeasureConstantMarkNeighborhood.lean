import PerronWright.Probability.FinitePointMeasureMarking
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Near-constant marks over a compact base

Only the position space is compact. Continuity transverse to the compact
constant-mark configurations gives one mark radius for every position
and every point count below the cutoff. The mark space may be noncompact
and need not be locally compact.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1200000

namespace PerronWright.FinitePointMeasureConstantMarkNeighborhood

open FiniteAtomicPointMeasure FinitePointMeasureCompact FinitePointMeasureFintype
open FinitePointMeasureMarking

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
  [MetricSpace E] [MetricSpace A] [CompactSpace E] [BorelSpace E] [BorelSpace A]

theorem exists_uniform_mark_radius (p : A) (H : ℕ)
    (F : PointMeasure (E × A) →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ m ≤ H, ∀ x : Fin m → E, ∀ y : Fin m → A,
      (∀ i, dist (y i) p < δ) →
      |F (ofAtomsPoint (fun i ↦ (x i, y i))) - F (constantMark p (ofAtomsPoint x))| < ε := by
  have hδ (m : Fin (H + 1)) : ∃ δ > 0,
      ∀ x : Fin m.val → E, ∀ y : Fin m.val → A,
      dist y (fun _ ↦ p) < δ →
      |F (ofAtomsPoint (fun i ↦ (x i, y i))) - F (constantMark p (ofAtomsPoint x))| < ε := by
    let f : (Fin m.val → A) → (Fin m.val → E) → ℝ :=
      fun y x ↦ F (ofAtomsPoint (fun i ↦ (x i, y i)))
    have hf : Continuous f.uncurry := by
      apply F.continuous.comp
      apply (continuous_ofAtomsPoint m.val).comp
      exact continuous_pi (fun i ↦
        ((continuous_apply i).comp continuous_snd).prodMk
          ((continuous_apply i).comp continuous_fst))
    obtain ⟨V, hV, hclose⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set (Fin m.val → E))).mem_uniformity_of_prod
        (s := Set.univ) (q := fun _ ↦ p) hf.continuousOn (Set.mem_univ _)
        (Metric.dist_mem_uniformity hε)
    simp only [nhdsWithin_univ] at hV
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨δ, hδ, ?_⟩
    intro x y hy
    have he := hclose y (hsub (Metric.mem_ball.mpr hy)) x (Set.mem_univ _)
    change dist (f y x) (f (fun _ ↦ p) x) < ε at he
    simpa only [f, Real.dist_eq, constantMark,
      mapPoint_ofAtomsPoint, Function.comp_def] using he
  choose δ hδpos hδprop using hδ
  let U : Set A := {v | ∀ m : Fin (H + 1), dist v p < δ m}
  have hU : U ∈ 𝓝 p := Filter.eventually_all.mpr (fun m ↦ Metric.ball_mem_nhds p (hδpos m))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨η, hη, ?_⟩
  intro m hm x y hy
  let j : Fin (H + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  apply hδprop j x y
  exact (dist_pi_lt_iff (hδpos j)).mpr (fun i ↦ hηsub (Metric.mem_ball.mpr (hy i)) j)

theorem ofFintype_mark_close (p : A) (H : ℕ)
    (F : PointMeasure (E × A) →ᵇ ℝ) (ε δ : ℝ)
    (hclose : ∀ m ≤ H, ∀ x : Fin m → E, ∀ y : Fin m → A,
      (∀ i, dist (y i) p < δ) →
      |F (ofAtomsPoint (fun i ↦ (x i, y i))) - F (constantMark p (ofAtomsPoint x))| < ε)
    {I : Type*} [Fintype I] (hI : Fintype.card I ≤ H) (x : I → E) (y : I → A)
    (hy : ∀ i, dist (y i) p < δ) :
    |F (ofFintype (fun i ↦ (x i, y i))) - F (constantMark p (ofFintype x))| < ε := by
  rw [ofFintype_eq_ofAtomsPoint, ofFintype_eq_ofAtomsPoint x]
  exact hclose (Fintype.card I) hI (fun i ↦ x ((Fintype.equivFin I).symm i))
    (fun i ↦ y ((Fintype.equivFin I).symm i)) (fun i ↦ hy _)

end PerronWright.FinitePointMeasureConstantMarkNeighborhood
