import PerronWright.Probability.BrownianBridgeRegressionKernel
import PerronWright.Probability.ContinuousPathIntervalMinimum

/-! # Genuine whole pinned-bridge Gaussian increment regression

The residual is a literal linear transform of the actual Gaussian
bridge. Its entire continuous-path law is independent of the selected
increment, by zero covariance and the proved rational Borel embedding.
The original bridge is reconstructed pointwise. No independent-residual
or Gaussian-disintegration conclusion is stored as an assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeGaussianRegression

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeRegressionKernel
open BrownianBridgeAreaTiltPathLaw ContinuousPathIntervalMinimum BrownianGaussianSkeleton

def residual (T a b t : ℝ≥0) (f : Path) : ℝ :=
  bridge T t f-slope T a b t*increment T a b f

theorem continuous_residual (T a b t : ℝ≥0) : Continuous (residual T a b t) :=
  (continuous_bridge T t).sub ((continuous_increment T a b).const_mul _)

theorem continuous_sample_residual (T a b : ℝ≥0) (f : Path) :
    Continuous (fun t ↦ residual T a b t f) :=
  (continuous_sample_bridge T f).sub ((continuous_sample_slope T a b).mul continuous_const)

private def augmented (T a b : ℝ≥0) (i : Option ℝ≥0) (f : Path) : ℝ :=
  match i with
  | none => increment T a b f
  | some t => residual T a b t f

private theorem augmented_isGaussianProcess (T a b : ℝ≥0) :
    IsGaussianProcess (augmented T a b) pathLaw := by
  apply (bridge_isGaussianProcess T).of_isGaussianProcess
  intro i
  cases i with
  | none =>
      let I : Finset ℝ≥0 := {a,b}
      let L : (I → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨b,by simp [I]⟩-x ⟨a,by simp [I]⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }
      exact ⟨I,L,fun _ ↦ rfl⟩
  | some t =>
      let I : Finset ℝ≥0 := {t,a,b}
      let L : (I → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨t,by simp [I]⟩-slope T a b t*(x ⟨b,by simp [I]⟩-x ⟨a,by simp [I]⟩)
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }
      exact ⟨I,L,fun _ ↦ rfl⟩

theorem residual_isGaussianProcess (T a b : ℝ≥0) : IsGaussianProcess (residual T a b) pathLaw :=
  (augmented_isGaussianProcess T a b).comp_right Option.some

theorem covariance_residual_increment (T a b t : ℝ≥0) (hT : 0 < T)
    (hab : a < b) (hb : b < T) (ht : t ≤ T) :
    cov[residual T a b t,increment T a b;pathLaw] = 0 := by
  unfold residual
  rw [covariance_fun_sub_left (bridge_hasGaussianLaw T t).memLp_two
    ((increment_hasGaussianLaw T a b).memLp_two.const_mul _)
    (increment_hasGaussianLaw T a b).memLp_two,covariance_const_mul_left,
    covariance_bridge_increment T a b t hT (hab.le.trans hb.le) hb.le ht,
    covariance_self (increment_hasGaussianLaw T a b).aemeasurable,
    variance_increment T a b hT hab.le hb.le]
  unfold BrownianBridgeRegressionKernel.slope
  rw [div_mul_cancel₀ _ (ne_of_gt (gapVariance_pos T a b hT hab hb)),sub_self]

def residualPath (T a b : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ residual T a b (min t T) f,
    (continuous_sample_residual T a b f).comp (continuous_id.min continuous_const)⟩

theorem measurable_residualPath (T a b : ℝ≥0) : Measurable (residualPath T a b) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ residual T a b (min (rationalTimeReal q) T) f)
  exact measurable_pi_lambda _ (fun q ↦ (continuous_residual T a b _).measurable)

theorem residualPath_independent_increment (T a b : ℝ≥0) (hT : 0 < T)
    (hab : a < b) (hb : b < T) : IndepFun (residualPath T a b) (increment T a b) pathLaw := by
  let X : RationalTime → Path → ℝ := fun q ↦ residual T a b (min (rationalTimeReal q) T)
  let Y : Unit → Path → ℝ := fun _ ↦ increment T a b
  have hG : IsGaussianProcess (Sum.elim X Y) pathLaw := by
    have he : Sum.elim X Y = augmented T a b ∘
        (fun i : Sum RationalTime Unit ↦ match i with
          | .inl q => some (min (rationalTimeReal q) T)
          | .inr _ => none) := by funext i; cases i <;> rfl
    rw [he]
    exact (augmented_isGaussianProcess T a b).comp_right _
  have hI : IndepFun (fun f q ↦ X q f) (fun f i ↦ Y i f) pathLaw :=
    hG.indepFun_of_covariance_eq_zero
      (fun _ ↦ (continuous_residual T a b _).measurable.aemeasurable)
      (fun _ ↦ (continuous_increment T a b).measurable.aemeasurable)
      (fun _ _ ↦ covariance_residual_increment T a b _ hT hab hb (min_le_right _ _))
  let : Nonempty Path := ⟨⟨fun _ ↦ 0,continuous_const⟩⟩
  have h := hI.comp rationalEval_measurableEmbedding.measurable_invFun (measurable_pi_apply ())
  have he : (rationalEval_measurableEmbedding.invFun ∘ (fun f q ↦ X q f)) = residualPath T a b := by
    funext f
    exact rationalEval_measurableEmbedding.leftInverse_invFun (residualPath T a b f)
  rw [he] at h
  simpa only [Function.comp_def,Y,id_eq] using h

def residualLaw (T a b : ℝ≥0) : Measure Path := pathLaw.map (residualPath T a b)

instance (T a b : ℝ≥0) : IsProbabilityMeasure (residualLaw T a b) :=
  Measure.isProbabilityMeasure_map (measurable_residualPath T a b).aemeasurable

theorem residual_increment_jointLaw (T a b : ℝ≥0) (hT : 0 < T) (hab : a < b) (hb : b < T) :
    pathLaw.map (fun f ↦ (residualPath T a b f,increment T a b f)) =
      (residualLaw T a b).prod (gaussianReal 0 (Real.toNNReal (gapVariance T a b))) := by
  rw [(residualPath_independent_increment T a b hT hab hb).map_prod_eq_prod_map_map
    (measurable_residualPath T a b).aemeasurable (continuous_increment T a b).measurable.aemeasurable,
    (hasLaw_increment T a b hT hab.le hb.le).map_eq]
  rfl

theorem reconstruct_stoppedBridgePath (T a b : ℝ≥0) (f : Path) :
    perturbedPath (residualPath T a b f) (slopePath T a b) (increment T a b f) = stoppedBridgePath T f := by
  apply ContinuousMap.ext
  intro t
  change bridge T (min t T) f-slope T a b (min t T)*increment T a b f+
    slope T a b (min t T)*increment T a b f = bridge T (min t T) f
  ring

end PerronWright.BrownianBridgeGaussianRegression
