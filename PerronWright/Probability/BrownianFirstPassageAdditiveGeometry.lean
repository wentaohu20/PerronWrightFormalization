import PerronWright.Probability.BrownianFirstPassageStrongMarkovFull

/-! # Additive levels for literal continuous first passage

The pathwise decomposition is proved from attained sublevels and continuity,
not assumed as a stopping-time interface. Brownian finiteness and the true
zero starting point then discharge its hypotheses almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageAdditiveGeometry

open BrownianPathLaw ContinuousPathFirstPassage BrownianFirstPassageUncappedLaw
open BrownianFirstPassageZeroDrift BrownianPathIndependentIncrements

theorem passageTime_le_of_level_le (level lower : ℝ) (hlevels : lower ≤ level)
    (f : Path) (hfinite : firstPassage lower f ≠ ⊤) :
    firstPassage level f ≤ firstPassage lower f := by
  have hh := firstPassage_attained lower f hfinite
  have h := (firstPassage_le_iff level f (passageTime lower f)).mpr
    ⟨passageTime lower f,le_rfl,hh.trans hlevels⟩
  rwa [passageTime,ENNReal.coe_toNNReal hfinite] at h

theorem passageTime_add_of_finite (a b : ℝ) (hb : 0 ≤ b) (f : Path)
    (hstart : -a < f 0) (hfinite : firstPassage (-(a+b)) f ≠ ⊤) :
    passageTime (-(a+b)) f =
      passageTime (-a) f + passageTime (-b) (passageFuture (-a) f) := by
  have hl : -(a+b) ≤ -a := by linarith
  have hle := passageTime_le_of_level_le (-a) (-(a+b)) hl f hfinite
  have hfinA : firstPassage (-a) f ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hle
  have hleN : passageTime (-a) f ≤ passageTime (-(a+b)) f := by
    apply ENNReal.coe_le_coe.mp
    change ((firstPassage (-a) f).toNNReal : ℝ≥0∞) ≤
      ((firstPassage (-(a+b)) f).toNNReal : ℝ≥0∞)
    rw [ENNReal.coe_toNNReal hfinA,ENNReal.coe_toNNReal hfinite]
    exact hle
  have hhitA : f (passageTime (-a) f) = -a :=
    firstPassage_exact_level (-a) f hstart hfinA
  have hhitAB : f (passageTime (-(a+b)) f) ≤ -(a+b) :=
    firstPassage_attained (-(a+b)) f hfinite
  have htime : passageTime (-a) f +
      (passageTime (-(a+b)) f - passageTime (-a) f) =
      passageTime (-(a+b)) f := add_tsub_cancel_of_le hleN
  have hfuture : passageFuture (-a) f
      (passageTime (-(a+b)) f - passageTime (-a) f) ≤ -b := by
    rw [passageFuture,futurePath_eval,htime,hhitA]
    linarith
  have hleB := (firstPassage_le_iff (-b) (passageFuture (-a) f)
      (passageTime (-(a+b)) f - passageTime (-a) f)).mpr
    ⟨_,le_rfl,hfuture⟩
  have hfinB : firstPassage (-b) (passageFuture (-a) f) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hleB
  have hleBN : passageTime (-b) (passageFuture (-a) f) ≤
      passageTime (-(a+b)) f - passageTime (-a) f := by
    rwa [← ENNReal.coe_toNNReal hfinB,ENNReal.coe_le_coe] at hleB
  apply le_antisymm
  · have hhitB := firstPassage_attained (-b) (passageFuture (-a) f) hfinB
    have hhit : f (passageTime (-a) f +
        passageTime (-b) (passageFuture (-a) f)) ≤ -(a+b) := by
      change f (passageTime (-a) f +
        passageTime (-b) (passageFuture (-a) f)) - f (passageTime (-a) f) ≤ -b at hhitB
      rw [hhitA] at hhitB
      linarith
    have h := (firstPassage_le_iff (-(a+b)) f
      (passageTime (-a) f + passageTime (-b) (passageFuture (-a) f))).mpr
      ⟨_,le_rfl,hhit⟩
    rwa [← ENNReal.coe_toNNReal hfinite,ENNReal.coe_le_coe] at h
  · calc
      _ ≤ passageTime (-a) f +
          (passageTime (-(a+b)) f - passageTime (-a) f) := add_le_add le_rfl hleBN
      _ = _ := htime

theorem ae_passageTime_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ f ∂pathLaw, passageTime (-(a+b)) f =
      passageTime (-a) f + passageTime (-b) (passageFuture (-a) f) := by
  filter_upwards [ae_firstPassage_ne_top (-(a+b)) (by linarith),
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hfin hf
  exact passageTime_add_of_finite a b hb.le f (by rw [hf]; linarith) hfin

end PerronWright.BrownianFirstPassageAdditiveGeometry
