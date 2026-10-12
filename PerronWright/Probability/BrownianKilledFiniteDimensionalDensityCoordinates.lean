import PerronWright.Probability.BrownianKilledFiniteDimensionalOrderedTimes
import PerronWright.Probability.BrownianPositiveKilledKernel
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Free endpoint coordinates and literal Gaussian product density

The deterministic initial coordinate is omitted. Appending a free endpoint
preserves finite product Lebesgue measure, and the genuine Gaussian-difference
transition densities multiply along the ordered time gaps.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFiniteDimensionalDensityCoordinates

open BrownianPathLaw BrownianKilledFiniteDimensionalCoordinates
open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel

abbrev FreeVector (n : ℕ) := Fin n → ℝ

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def prependInitial (n : ℕ) (a : ℝ) (v : FreeVector n) : EndpointVector n := Fin.cons a v

theorem continuous_prependInitial (n : ℕ) (a : ℝ) : Continuous (prependInitial n a) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [prependInitial,Fin.cons_zero] using (continuous_const : Continuous (fun _ : FreeVector n ↦ a))
  · simpa only [prependInitial,Fin.cons_succ] using (continuous_apply j : Continuous (fun v : FreeVector n ↦ v j))

def dropInitial (n : ℕ) (v : EndpointVector n) : FreeVector n := Fin.tail v

theorem continuous_dropInitial (n : ℕ) : Continuous (dropInitial n) :=
  continuous_pi (fun i ↦ continuous_apply i.succ)

def freeAppend (n : ℕ) (p : FreeVector n × ℝ) : FreeVector (n+1) := Fin.snoc p.1 p.2

theorem continuous_freeAppend (n : ℕ) : Continuous (freeAppend n) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [freeAppend,Fin.snoc_last] using continuous_snd
  · simpa only [freeAppend,Fin.snoc_castSucc,Function.comp_def] using
      (continuous_apply j).comp continuous_fst

theorem dropInitial_append (n : ℕ) (v : EndpointVector n) (y : ℝ) :
    dropInitial (n+1) (appendEndpoint n (v,y)) = freeAppend n (dropInitial n v,y) := by
  have h := Fin.cons_snoc_eq_snoc_cons (v 0) (Fin.tail v) y
  rw [Fin.cons_self_tail] at h
  have he := congrArg Fin.tail h
  rw [Fin.tail_cons] at he
  exact he.symm

def lastState (n : ℕ) (a : ℝ) (v : FreeVector n) : ℝ := prependInitial n a v (Fin.last n)

theorem continuous_lastState (n : ℕ) (a : ℝ) : Continuous (lastState n a) :=
  (continuous_apply _).comp (continuous_prependInitial n a)

theorem lastState_dropInitial (n : ℕ) (a : ℝ) (v : EndpointVector n) (hv : v 0 = a) :
    lastState n a (dropInitial n v) = v (Fin.last n) := by
  have h := Fin.cons_self_tail v
  rw [hv] at h
  exact congrArg (fun w : EndpointVector n ↦ w (Fin.last n)) h

def jointDensity (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector n) : ℝ≥0∞ :=
  ∏ i : Fin n, density (prependInitial n a v i.castSucc) (gaps i.val) (v i)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem measurable_jointDensity (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) :
    Measurable (jointDensity n a gaps) := by
  unfold jointDensity
  have hprep : Measurable (prependInitial n a) := (continuous_prependInitial n a).measurable
  have hp (i : Fin n) : Measurable (fun v : FreeVector n ↦ prependInitial n a v i.castSucc) := by
    have he : Measurable (fun w : EndpointVector n ↦ w i.castSucc) := measurable_pi_apply _
    exact he.comp hprep
  have hi (i : Fin n) : Measurable (fun v : FreeVector n ↦
      density (prependInitial n a v i.castSucc) (gaps i.val) (v i)) := by
    have he : Measurable (fun v : FreeVector n ↦ v i) := measurable_pi_apply _
    have hpair : Measurable (fun v : FreeVector n ↦ (prependInitial n a v i.castSucc,v i)) :=
      (hp i).prodMk he
    have hd : Measurable (fun p : ℝ × ℝ ↦ density p.1 (gaps i.val) p.2) :=
      measurable_joint_density (gaps i.val)
    simpa only [Function.comp_def] using hd.comp hpair
  exact Finset.measurable_prod (f := fun (i : Fin n) (v : FreeVector n) ↦
    density (prependInitial n a v i.castSucc) (gaps i.val) (v i)) Finset.univ (fun i _ ↦ hi i)

@[simp] theorem jointDensity_zero (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector 0) :
    jointDensity 0 a gaps v = 1 := by simp [jointDensity]

theorem jointDensity_append (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector n) (y : ℝ) :
    jointDensity (n+1) a gaps (freeAppend n (v,y)) =
      jointDensity n a gaps v*density (lastState n a v) (gaps n) y := by
  simp only [jointDensity,freeAppend,prependInitial,Fin.cons_snoc_eq_snoc_cons,
    Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last,lastState]

theorem jointDensity_eq_gaussian_product (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) (v : FreeVector n) :
    jointDensity n a gaps v = ∏ i : Fin n, ENNReal.ofReal
      (if 0 < v i then gaussianPDFReal (prependInitial n a v i.castSucc) (gaps i.val) (v i) -
        gaussianPDFReal (-(prependInitial n a v i.castSucc)) (gaps i.val) (v i) else 0) := rfl

theorem jointDensity_eq_zero_of_nonpos_coordinate (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (v : FreeVector n) (i : Fin n) (hi : v i ≤ 0) : jointDensity n a gaps v = 0 := by
  unfold jointDensity
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [density,densityReal,Set.indicator,mem_Ioi,if_neg (not_lt.mpr hi),ENNReal.ofReal_zero]

theorem volume_preserving_freeAppend (n : ℕ) :
    MeasurePreserving (freeAppend n)
      ((volume : Measure (FreeVector n)).prod (volume : Measure ℝ)) volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) (Fin.last n)).symm
  have hs := Measure.measurePreserving_swap (μ := (volume : Measure (FreeVector n)))
    (ν := (volume : Measure ℝ))
  have he := h.comp hs
  change MeasurePreserving (fun p : FreeVector n × ℝ ↦ (Fin.snoc p.1 p.2 : FreeVector (n+1)))
    ((volume : Measure (FreeVector n)).prod (volume : Measure ℝ)) volume
  simpa only [volume_pi,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_last',
    Equiv.coe_fn_mk,Function.comp_def,Prod.swap,freeAppend] using he

theorem lintegral_volume_freeAppend (n : ℕ) {F : FreeVector (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ v : FreeVector n, ∫⁻ y : ℝ, F (freeAppend n (v,y)) := by
  rw [← (volume_preserving_freeAppend n).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp (continuous_freeAppend n).measurable).aemeasurable

end PerronWright.BrownianKilledFiniteDimensionalDensityCoordinates
