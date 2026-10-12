import PerronWright.Probability.BrownianPositiveBridgeJointMomentLimits
import PerronWright.Probability.BrownianPositiveBridgeAreaMomentBounds
import Mathlib.MeasureTheory.Integral.Pi

/-! # Literal area powers as finite time-cube integrals

The continuous-path area is integrated over the actual interval. Finite
product integration gives its powers, and positivity of the genuine
conditioned bridge permits Tonelli without a finite-moment premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaTimeMoments

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteCoordinateMoments

def timeCube (T : ℝ≥0) (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ ↦ volume.restrict (Ioc (0 : ℝ) (T : ℝ)))

instance timeCube_isFinite (T : ℝ≥0) (d : ℕ) : IsFiniteMeasure (timeCube T d) := by
  unfold timeCube
  infer_instance

theorem timeCube_univ (T : ℝ≥0) (d : ℕ) :
    timeCube T d univ = ENNReal.ofReal (T : ℝ)^d := by
  simp [timeCube,Measure.pi_univ,Real.volume_Ioc]

def heightProduct {d : ℕ} (τ : Fin d → ℝ) (g : Path) : ℝ :=
  ∏ i, g (Real.toNNReal (τ i))

theorem continuous_joint_heightProduct (d : ℕ) :
    Continuous (fun p : (Fin d → ℝ)×Path ↦ heightProduct p.1 p.2) := by
  unfold heightProduct
  apply continuous_finsetProd
  intro i _
  exact continuous_joint_eval.comp
    (continuous_snd.prodMk (continuous_real_toNNReal.comp ((continuous_apply i).comp continuous_fst)))

theorem measurable_joint_heightProduct (d : ℕ) :
    Measurable (fun p : (Fin d → ℝ)×Path ↦ ENNReal.ofReal (heightProduct p.1 p.2)) :=
  (continuous_joint_heightProduct d).measurable.ennreal_ofReal

theorem ae_timeCube_coordinates (T : ℝ≥0) (d : ℕ) :
    ∀ᵐ τ ∂timeCube T d, ∀ i, τ i ∈ Ioc (0 : ℝ) (T : ℝ) := by
  apply eventually_all.mpr
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioc)

theorem heightProduct_nonneg {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ) (g : Path)
    (hτ : ∀ i, τ i ∈ Ioc (0 : ℝ) (T : ℝ))
    (hg : ∀ t : ℝ≥0, t ≤ T → 0 ≤ g t) : 0 ≤ heightProduct τ g := by
  apply Finset.prod_nonneg
  intro i _
  exact hg _ (Real.toNNReal_le_iff_le_coe.mpr (hτ i).2)

theorem path_heightProduct_integrable (T : ℝ≥0) (d : ℕ) (g : Path) :
    Integrable (fun τ ↦ heightProduct τ g) (timeCube T d) := by
  unfold heightProduct timeCube
  apply Integrable.fintype_prod (f := fun (_ : Fin d) (r : ℝ) ↦ g (Real.toNNReal r))
  intro i
  exact (((continuous_path g).comp continuous_real_toNNReal).intervalIntegrable 0 T).1

theorem pathArea_pow_eq_cube_integral (T : ℝ≥0) (d : ℕ) (g : Path) :
    pathArea T g^d = ∫ τ, heightProduct τ g ∂timeCube T d := by
  have h := integral_fintype_prod_eq_pow (ι := Fin d)
    (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ))) (fun r : ℝ ↦ g (Real.toNNReal r))
  simp only [Fintype.card_fin] at h
  have hA : (∫ r in Ioc (0 : ℝ) (T : ℝ), g (Real.toNNReal r)) = pathArea T g :=
    (intervalIntegral.integral_of_le T.property).symm
  rw [hA] at h
  exact h.symm

theorem pathArea_pow_eq_cube_lintegral (T : ℝ≥0) (d : ℕ) (g : Path)
    (hg : ∀ t : ℝ≥0, t ≤ T → 0 ≤ g t) :
    ENNReal.ofReal (pathArea T g^d) =
      ∫⁻ τ, ENNReal.ofReal (heightProduct τ g) ∂timeCube T d := by
  rw [pathArea_pow_eq_cube_integral]
  apply ofReal_integral_eq_lintegral_ofReal (path_heightProduct_integrable T d g)
  filter_upwards [ae_timeCube_coordinates T d] with τ hτ
  exact heightProduct_nonneg T τ g hτ hg

def sourceTimeMoment (a : ℝ) (T : ℝ≥0) (d : ℕ) (τ : Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ g : Path, ENNReal.ofReal (heightProduct τ g) ∂positiveBridgeLaw a T

theorem measurable_sourceTimeMoment (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Measurable (sourceTimeMoment a T d) := by
  let := positiveBridgeLaw_isProbability a ha T hT
  exact (measurable_joint_heightProduct d).lintegral_prod_right

theorem actual_area_moment_eq_time_integral (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    (∫⁻ g : Path, ENNReal.ofReal (pathArea T g^d) ∂positiveBridgeLaw a T) =
      ∫⁻ τ, sourceTimeMoment a T d τ ∂timeCube T d := by
  let := positiveBridgeLaw_isProbability a ha T hT
  have hm : Measurable (fun p : Path×(Fin d → ℝ) ↦
      ENNReal.ofReal (heightProduct p.2 p.1)) :=
    (measurable_joint_heightProduct d).comp measurable_swap
  calc
    _ = ∫⁻ g : Path, (∫⁻ τ, ENNReal.ofReal (heightProduct τ g) ∂timeCube T d)
        ∂positiveBridgeLaw a T := by
      apply lintegral_congr_ae
      filter_upwards [ae_positiveBridgeLaw_strictly_positive a T] with g hg
      exact pathArea_pow_eq_cube_lintegral T d g (fun t ht ↦ (hg t ht).le)
    _ = _ := lintegral_lintegral_swap hm.aemeasurable

theorem heightProduct_le_radius_pow (d : ℕ) (τ : Fin d → ℝ) (g : Path) :
    ENNReal.ofReal (heightProduct τ g) ≤
      ENNReal.ofReal (radius (fun i ↦ g (Real.toNNReal (τ i)))^d) := by
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ |heightProduct τ g| := le_abs_self _
    _ ≤ _ := by
      simpa [monomial,heightProduct] using
        abs_monomial_le_radius_pow (fun _ : Fin d ↦ 1) (fun i ↦ g (Real.toNNReal (τ i)))

theorem eventually_uniform_sourceTimeMoment_bound (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ τ ∂timeCube T d,
      sourceTimeMoment a T d τ ≤ jointMomentBound T d d := by
  filter_upwards [eventually_uniform_finite_coordinate_moment T hT d d] with a hb
  filter_upwards [ae_timeCube_coordinates T d] with τ hτ
  exact (lintegral_mono (fun g ↦ heightProduct_le_radius_pow d τ g)).trans
    (hb (fun i ↦ Real.toNNReal (τ i))
      (fun i ↦ Real.toNNReal_le_iff_le_coe.mpr (hτ i).2))

theorem eventually_area_time_integral_bound (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ τ, sourceTimeMoment a T d τ ∂timeCube T d) ≤
        jointMomentBound T d d*ENNReal.ofReal (T : ℝ)^d := by
  filter_upwards [eventually_uniform_sourceTimeMoment_bound T hT d] with a hb
  calc
    _ ≤ ∫⁻ τ : Fin d → ℝ, jointMomentBound T d d ∂timeCube T d := lintegral_mono_ae hb
    _ = _ := by rw [lintegral_const,timeCube_univ]

end PerronWright.BrownianPositiveBridgeAreaTimeMoments
