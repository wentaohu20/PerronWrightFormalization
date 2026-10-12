import PerronWright.Probability.BrownianFullExcursionMovingCounts
import PerronWright.Probability.BrownianFullHorizonPoissonMarks
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Actual full spatial excursion counts realize the full area-rate marks

Finite collections of actual disjoint full component cells fit in a
path-dependent finite window. The proved full spatial Poisson formula
computes every finite count law; projective uniqueness identifies the
entire rational count family with the true full-area marking law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullExcursionSpatialMarkIdentification

open BrownianPathLaw BrownianFullExcursionSpatialCells BrownianFullExcursionMovingCounts
open BrownianFullHorizonSpatialKernel BrownianFullHorizonSpatialCounts BrownianFullHorizonSpatialSupport
open BrownianFullHorizonExcursionAreas BrownianFullHorizonPoissonMarks

theorem measurable_spatialCounts_fixed (lambda : ℝ) (f : Path) :
    Measurable (fun a : SpatialAtoms ↦ spatialCounts lambda (f,a)) :=
  (measurable_spatialCounts lambda).comp (measurable_const.prodMk measurable_id)

theorem measurable_rationalCount : Measurable rationalCount :=
  measurable_pi_lambda _ (fun q ↦ measurable_pi_apply (Encodable.encode q))

theorem markLaw_map_finite_rationalCounts (lambda : ℝ) (f : Path) (I : Finset ℚ) :
    (markLaw lambda f).map (fun (m : ℕ → ℕ) (q : I) ↦ rationalCount m q.1) =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea q.1 lambda f) := by
  have hi := (markLaw_rationalCounts_independent lambda f).precomp
    (g := fun q : I ↦ (q : ℚ)) Subtype.coe_injective
  have he := hi.map_fun_eq_pi_map (fun q : I ↦
    (measurable_pi_apply (Encodable.encode (q : ℚ))).aemeasurable)
  change (markLaw lambda f).map (fun (m : ℕ → ℕ) (q : I) ↦ rationalCount m q.1) =
    Measure.pi (fun q : I ↦ (markLaw lambda f).map (fun m ↦ rationalCount m q.1)) at he
  rw [he]
  unfold PoissonCountKernel.finiteCountLaw
  congr 1
  funext q
  exact (markLaw_hasLaw_rationalCount lambda f q.1).map_eq

/-- Exact finite laws for counts of the actual full, nonrepeating cells. -/
theorem spatialLaw_map_finite_retained_counts (lambda : ℝ) (f : Path) (I : Finset ℚ) :
    (spatialLaw lambda f).map (fun a (q : I) ↦ spatialCounts lambda (f,a) q.1) =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea q.1 lambda f) := by
  have hcuts : ∀ q : I, ∃ N : ℕ, retainedCell lambda q.1 f ⊆ timeCut N :=
    fun q ↦ exists_retainedCell_subset_timeCut lambda q.1 f
  choose n hn using hcuts
  let N := Finset.univ.sup n
  have hN : ∀ q : I, retainedCell lambda q.1 f ⊆ timeCut N := by
    intro q z hz
    have hq : n q ≤ N := Finset.le_sup (Finset.mem_univ q)
    have ht : z.1 < (n q : ℝ) := hn q hz
    exact ht.trans_le (Nat.cast_le.mpr hq)
  have hd : Pairwise (fun q r : I ↦ Disjoint (retainedCell lambda q.1 f) (retainedCell lambda r.1 f)) :=
    fun q r hqr ↦ retainedCell_pairwise_disjoint lambda f
      (fun h ↦ hqr (Subtype.ext h))
  change (spatialLaw lambda f).map
    (fun a (q : I) ↦ spatialCount a (retainedCell lambda q.1 f)) = _
  rw [spatialLaw_map_count_vector lambda f N (fun q : I ↦ retainedCell lambda q.1 f)
    hd (fun q ↦ measurableSet_retainedCell lambda q.1 f) hN]
  congr 1
  funext q
  rw [intensity_retainedCell]
  exact ENNReal.toNNReal_coe _

/-- The actual full spatial point process realizes the entire full-area
Poisson marking law, not merely each of its finite marginals. -/
theorem spatial_count_law_eq_markLaw (lambda : ℝ) (f : Path) :
    (spatialLaw lambda f).map (fun a ↦ spatialCounts lambda (f,a)) =
      (markLaw lambda f).map rationalCount := by
  let μ := (spatialLaw lambda f).map (fun a ↦ spatialCounts lambda (f,a))
  let ν := (markLaw lambda f).map rationalCount
  have hm (I : Finset ℚ) : μ.map I.restrict =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea q.1 lambda f) := by
    rw [show μ = (spatialLaw lambda f).map (fun a ↦ spatialCounts lambda (f,a)) from rfl,
      Measure.map_map I.measurable_restrict (measurable_spatialCounts_fixed lambda f)]
    exact spatialLaw_map_finite_retained_counts lambda f I
  have hn (I : Finset ℚ) : ν.map I.restrict =
      PoissonCountKernel.finiteCountLaw (fun q : I ↦ retainedArea q.1 lambda f) := by
    rw [show ν = (markLaw lambda f).map rationalCount from rfl,
      Measure.map_map I.measurable_restrict measurable_rationalCount]
    exact markLaw_map_finite_rationalCounts lambda f I
  have hμ : IsProjectiveLimit μ (fun I : Finset ℚ ↦ μ.map I.restrict) := fun _ ↦ rfl
  have hν : IsProjectiveLimit ν (fun I : Finset ℚ ↦ μ.map I.restrict) :=
    fun I ↦ (hn I).trans (hm I).symm
  exact hμ.unique hν

end PerronWright.BrownianFullExcursionSpatialMarkIdentification
