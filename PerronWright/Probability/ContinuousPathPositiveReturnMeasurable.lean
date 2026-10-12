import PerronWright.Probability.BrownianMinimumFutureReturnPathGeometry

/-! # Global Borel measurability of the literal positive-time return

The hit-set infimum is the decreasing-cutoff infimum of actual passages
after positive deterministic times. This proves measurability on the
entire continuous-path space, including zero or infinite returns; no
positive-prefix or Brownian-law assumption is needed.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathPositiveReturnMeasurable

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassagePastFibers
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry

private def cutoff (n : ℕ) : ℝ≥0 := 1/(n+1)

private theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by
  unfold cutoff
  positivity

private theorem return_le_cutoff_passage (n : ℕ) (g : Path) :
    firstReturnZero g ≤ (cutoff n : ℝ≥0∞)+
      firstPassage (-g (cutoff n)) (futurePath (cutoff n) g) := by
  let a := cutoff n
  by_cases hfin : firstPassage (-g a) (futurePath a g) = ⊤
  · change firstReturnZero g ≤ (a : ℝ≥0∞)+firstPassage (-g a) (futurePath a g)
    rw [hfin,add_top]
    exact le_top
  · let r := (firstPassage (-g a) (futurePath a g)).toNNReal
    have hh := firstPassage_attained (-g a) (futurePath a g) hfin
    change g (a+r)-g a ≤ -g a at hh
    have hhit : g (a+r) ≤ 0 := by linarith
    have hp : 0 < a+r := (cutoff_pos n).trans_le (le_add_of_nonneg_right bot_le)
    have hle : firstReturnZero g ≤ ((a+r : ℝ≥0) : ℝ≥0∞) :=
      sInf_le ⟨a+r,⟨hp,hhit⟩,rfl⟩
    simpa only [ENNReal.coe_add,r,ENNReal.coe_toNNReal hfin] using hle

theorem firstReturnZero_eq_iInf_passages (g : Path) :
    firstReturnZero g = ⨅ n : ℕ,
      ((1/(n+1) : ℝ≥0) : ℝ≥0∞)+
        firstPassage (-g (1/(n+1))) (futurePath (1/(n+1)) g) := by
  change firstReturnZero g = ⨅ n : ℕ, (cutoff n : ℝ≥0∞)+
    firstPassage (-g (cutoff n)) (futurePath (cutoff n) g)
  apply le_antisymm
  · exact le_iInf (fun n ↦ return_le_cutoff_passage n g)
  · apply le_sInf
    rintro x ⟨t,⟨ht,hgt⟩,rfl⟩
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (t : ℝ) from ht)
    have hat : cutoff n ≤ t := by
      have hh : (cutoff n : ℝ) < (t : ℝ) := by
        simpa only [cutoff,NNReal.coe_div,NNReal.coe_one,NNReal.coe_add,NNReal.coe_natCast] using hn
      exact (NNReal.coe_lt_coe.mp hh).le
    have hp : firstPassage (-g (cutoff n)) (futurePath (cutoff n) g) ≤
        ((t-cutoff n : ℝ≥0) : ℝ≥0∞) := by
      apply (firstPassage_le_iff _ _ _).mpr
      refine ⟨t-cutoff n,le_rfl,?_⟩
      rw [futurePath_eval,add_tsub_cancel_of_le hat]
      linarith
    apply iInf_le_of_le n
    calc
      _ ≤ (cutoff n : ℝ≥0∞)+((t-cutoff n : ℝ≥0) : ℝ≥0∞) := add_le_add le_rfl hp
      _ = (t : ℝ≥0∞) := by rw [← ENNReal.coe_add,add_tsub_cancel_of_le hat]

theorem measurable_firstReturnZero : Measurable firstReturnZero := by
  have he : firstReturnZero = fun g : Path ↦ ⨅ n : ℕ,
      ((1/(n+1) : ℝ≥0) : ℝ≥0∞)+
        firstPassage (-g (1/(n+1))) (futurePath (1/(n+1)) g) :=
    funext firstReturnZero_eq_iInf_passages
  rw [he]
  apply Measurable.iInf
  intro n
  exact measurable_const.add (measurable_joint_firstPassage.comp
    ((continuous_eval (1/(n+1))).measurable.neg.prodMk (measurable_futurePath (1/(n+1)))))

theorem measurable_returnTaggedPast : Measurable returnTaggedPast := by
  have ht := measurable_firstReturnZero.ennreal_toNNReal
  exact ht.prodMk (continuous_joint_pastPath.measurable.comp (ht.prodMk measurable_id))

theorem measurable_returnFuturePath : Measurable returnFuturePath :=
  continuous_joint_futurePath.measurable.comp
    (measurable_firstReturnZero.ennreal_toNNReal.prodMk measurable_id)

end PerronWright.ContinuousPathPositiveReturnMeasurable
