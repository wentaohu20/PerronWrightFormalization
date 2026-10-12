import PerronWright.Probability.BrownianMinimumFutureFirstReturn

/-! # Literal whole stopped-path reconstruction at the actual entrance return

Stopping and shifting the actual source at its positive-time return are
rewritten through its unit prefix and the genuine post-unit passage.
The return's measurability and finite-time identity are proved under the
actual source law, rather than added as stopping-time assumptions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureReturnPathGeometry

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFirstPassagePastFibers
open BrownianMinimumFutureEntranceSource BrownianMinimumFutureFirstReturn
open BrownianFirstPassageUncappedLaw

theorem pastPath_add_splice (T τ : ℝ≥0) (g : Path) :
    pastPath (T+τ) g = splicePath T (pastPath T g,pastPath τ (futurePath T g)) := by
  apply ContinuousMap.ext
  intro t
  change g (min t (T+τ)) = g (min (min t T) T)+(g (T+min (t-T) τ)-g T)
  rw [min_assoc,min_self]
  rcases le_total t T with ht | ht
  · have htotal : t ≤ T+τ := ht.trans (le_add_of_nonneg_right bot_le)
    simp only [min_eq_left ht,min_eq_left htotal,tsub_eq_zero_of_le ht,
      min_eq_left (show (0 : ℝ≥0) ≤ τ from bot_le),add_zero]
    ring
  · have hm : T+min (t-T) τ = min t (T+τ) := by
      rw [← min_add_add_left,add_tsub_cancel_of_le ht]
    rw [min_eq_right ht,hm]
    ring

theorem futurePath_add (T τ : ℝ≥0) (g : Path) :
    futurePath (T+τ) g = futurePath τ (futurePath T g) := by
  apply ContinuousMap.ext
  intro t
  change g ((T+τ)+t)-g (T+τ) = (g (T+(τ+t))-g T)-(g (T+τ)-g T)
  rw [← add_assoc]
  ring

def returnTaggedPast (g : Path) : ℝ≥0 × Path :=
  ((firstReturnZero g).toNNReal,pastPath (firstReturnZero g).toNNReal g)

def returnFuturePath (g : Path) : Path := futurePath (firstReturnZero g).toNNReal g

theorem aemeasurable_returnTaggedPast : AEMeasurable returnTaggedPast unitSourceLaw := by
  have ht := aemeasurable_firstReturnZero.ennreal_toNNReal
  exact ht.prodMk (continuous_joint_pastPath.measurable.comp_aemeasurable
    (ht.prodMk measurable_id.aemeasurable))

theorem aemeasurable_returnFuturePath : AEMeasurable returnFuturePath unitSourceLaw := by
  exact continuous_joint_futurePath.measurable.comp_aemeasurable
    (aemeasurable_firstReturnZero.ennreal_toNNReal.prodMk measurable_id.aemeasurable)

theorem ae_returnTime_eq_post_unit_passage :
    ∀ᵐ g : Path ∂unitSourceLaw,
      (firstReturnZero g).toNNReal = 1+passageTime (-g 1) (futurePath 1 g) := by
  filter_upwards [ae_unitSourceLaw_firstReturn_eq,ae_unitSourceLaw_post_unit_passage_finite]
    with g he hfin
  rw [he,ENNReal.toNNReal_add (by norm_num) hfin,ENNReal.toNNReal_one]
  rfl

theorem ae_returnTaggedPast_reconstruction :
    ∀ᵐ g : Path ∂unitSourceLaw,
      returnTaggedPast g =
        (1+passageTime (-g 1) (futurePath 1 g),
          splicePath 1 (pastPath 1 g,
            pastPath (passageTime (-g 1) (futurePath 1 g)) (futurePath 1 g))) := by
  filter_upwards [ae_returnTime_eq_post_unit_passage] with g hg
  rw [returnTaggedPast,hg,pastPath_add_splice]

theorem ae_returnFuturePath_reconstruction :
    ∀ᵐ g : Path ∂unitSourceLaw,
      returnFuturePath g = passageFuture (-g 1) (futurePath 1 g) := by
  filter_upwards [ae_returnTime_eq_post_unit_passage] with g hg
  rw [returnFuturePath,hg,futurePath_add]
  rfl

end PerronWright.BrownianMinimumFutureReturnPathGeometry
