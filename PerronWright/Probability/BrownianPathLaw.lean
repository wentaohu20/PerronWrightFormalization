import PerronWright.Probability.BrownianContinuousGaussianLaw
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual constructed Brownian probability law on continuous paths

`Path` is a named copy of the genuine continuous-map space, with its
compact-open (equivalently locally uniform) topology and its actual Borel
sigma algebra. A countable rational-evaluation injection and Lusin--Souslin
prove path-valued measurability. A measurable representative of the
literal constructed process then supplies the genuine probability law.
No path-measurability or Brownian-realization hypothesis is introduced.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPathLaw

open BrownianGaussianSkeleton BrownianContinuousModification BrownianContinuousGaussianLaw
open BrownianContinuousLinearTests

/-- A named copy prevents imposing new measurable-space instances on
Mathlib's general continuous-map type. The topology is literally compact-open. -/
def Path := C(ℝ≥0,ℝ)

instance : TopologicalSpace Path := inferInstanceAs (TopologicalSpace C(ℝ≥0,ℝ))
instance : MeasurableSpace Path := borel Path
instance : BorelSpace Path := ⟨rfl⟩
instance : PolishSpace Path := inferInstanceAs (PolishSpace C(ℝ≥0,ℝ))
instance : FunLike Path ℝ≥0 ℝ := inferInstanceAs (FunLike C(ℝ≥0,ℝ) ℝ≥0 ℝ)
instance : ContinuousEvalConst Path ℝ≥0 ℝ := inferInstanceAs (ContinuousEvalConst C(ℝ≥0,ℝ) ℝ≥0 ℝ)
instance : ContinuousEval Path ℝ≥0 ℝ := inferInstanceAs (ContinuousEval C(ℝ≥0,ℝ) ℝ≥0 ℝ)

def toContinuousMap (f : Path) : C(ℝ≥0,ℝ) := f

theorem continuous_path (f : Path) : Continuous (fun t ↦ f t) :=
  (toContinuousMap f).continuous

theorem continuous_eval (t : ℝ≥0) : Continuous (fun f : Path ↦ f t) :=
  continuous_eval_const t

theorem continuous_joint_eval : Continuous (fun p : Path × ℝ≥0 ↦ p.1 p.2) :=
  (continuous_fst : Continuous (fun p : Path × ℝ≥0 ↦ p.1)).eval continuous_snd

theorem tendsto_path_iff_locallyUniformly {ι : Type*} {l : Filter ι}
    (F : ι → Path) (f : Path) :
    Tendsto F l (𝓝 f) ↔ TendstoLocallyUniformly (fun i t ↦ F i t) (fun t ↦ f t) l :=
  ContinuousMap.tendsto_iff_tendstoLocallyUniformly

def rationalEval (f : Path) (q : RationalTime) : ℝ := f (rationalTimeReal q)

theorem continuous_rationalEval : Continuous rationalEval :=
  continuous_pi (fun q ↦ continuous_eval (rationalTimeReal q))

/-- The countable coordinate map is actually injective, proved using
literal dyadic floors converging to every nonnegative real time. -/
theorem rationalEval_injective : Function.Injective rationalEval := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  have ht : Tendsto (fun n ↦ rationalTimeReal (timeApprox n t)) atTop (𝓝 t) :=
    NNReal.tendsto_coe.mp (timeApprox_tendsto_real t)
  have hf := (continuous_path f).tendsto t |>.comp ht
  have hg := (continuous_path g).tendsto t |>.comp ht
  exact tendsto_nhds_unique hf (hg.congr' (Eventually.of_forall
    (fun n ↦ (congrFun h (timeApprox n t)).symm)))

/-- This establishes compatibility of the actual compact-open Borel
space with countable coordinate measurability, not an assumed equality. -/
theorem rationalEval_measurableEmbedding : MeasurableEmbedding rationalEval :=
  continuous_rationalEval.measurableEmbedding rationalEval_injective

def sampledPath (x : ℕ → ℝ) : Path :=
  ContinuousMap.mkD (fun t ↦ process t x) (0 : C(ℝ≥0,ℝ))

theorem ae_all_sampledPath_eval : ∀ᵐ x ∂rationalLaw, ∀ t : ℝ≥0,
    sampledPath x t = process t x := by
  filter_upwards [ae_continuous_process] with x hx
  intro t
  exact ContinuousMap.mkD_apply_of_continuous hx

theorem aemeasurable_sampledPath : AEMeasurable sampledPath rationalLaw := by
  apply rationalEval_measurableEmbedding.aemeasurable_comp_iff.mp
  have hm : AEMeasurable (fun x (q : RationalTime) ↦ process (rationalTimeReal q) x) rationalLaw :=
    aemeasurable_pi_lambda _ (fun q ↦ aemeasurable_process (rationalTimeReal q))
  apply hm.congr
  filter_upwards [ae_all_sampledPath_eval] with x hx
  exact funext (fun q ↦ (hx (rationalTimeReal q)).symm)

/-- A genuine measurable path-valued representative, differing from the
literal process only on the already proved null exceptional set. -/
def measurablePath : (ℕ → ℝ) → Path := aemeasurable_sampledPath.mk sampledPath

theorem measurable_measurablePath : Measurable measurablePath :=
  aemeasurable_sampledPath.measurable_mk

theorem ae_all_measurablePath_eval : ∀ᵐ x ∂rationalLaw, ∀ t : ℝ≥0,
    measurablePath x t = process t x := by
  filter_upwards [aemeasurable_sampledPath.ae_eq_mk,ae_all_sampledPath_eval] with x hx ht
  intro t
  exact (congrArg (fun f : Path ↦ f t) hx).symm.trans (ht t)

def pathLaw : Measure Path := rationalLaw.map measurablePath

instance : IsProbabilityMeasure pathLaw :=
  Measure.isProbabilityMeasure_map measurable_measurablePath.aemeasurable

theorem pathLaw_eq_map_sampledPath : pathLaw = rationalLaw.map sampledPath := by
  exact Measure.map_congr aemeasurable_sampledPath.ae_eq_mk.symm

theorem hasLaw_measurablePath : HasLaw measurablePath pathLaw rationalLaw :=
  ⟨measurable_measurablePath.aemeasurable,rfl⟩

theorem measurablePath_hasLaw_finite (I : Finset ℝ≥0) :
    HasLaw (fun x ↦ I.restrict (measurablePath x))
      (ProbabilityTheory.BrownianReal.projectiveFamily I) rationalLaw := by
  apply (process_hasLaw_finite I).congr
  filter_upwards [ae_all_measurablePath_eval] with x hx
  exact funext (fun t : I ↦ hx t.val)

/-- Exact finite laws of coordinate evaluation under the actual
probability measure on the actual compact-open continuous-path space. -/
theorem pathLaw_hasLaw_finite (I : Finset ℝ≥0) :
    HasLaw (fun f : Path ↦ I.restrict (fun t ↦ f t))
      (ProbabilityTheory.BrownianReal.projectiveFamily I) pathLaw := by
  have hm : Measurable (fun f : Path ↦ I.restrict (fun t ↦ f t)) :=
    measurable_pi_lambda _ (fun t ↦ (continuous_eval t.val).measurable)
  refine ⟨hm.aemeasurable,?_⟩
  rw [pathLaw,Measure.map_map hm measurable_measurablePath]
  exact (measurablePath_hasLaw_finite I).map_eq

/-- Brownian motion realized by genuine continuous-path coordinate
evaluation under its constructed probability law. Every path is continuous. -/
theorem isBrownian_pathLaw : IsBrownianReal (fun t (f : Path) ↦ f t) pathLaw :=
  ⟨⟨pathLaw_hasLaw_finite⟩,Eventually.of_forall continuous_path⟩

end PerronWright.BrownianPathLaw
