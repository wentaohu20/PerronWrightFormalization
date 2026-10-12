import PerronWright.Probability.BrownianPathLaw
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.BrownianMotion.Basic

/-! # Actual past and future Brownian continuous paths

The proved Gaussian weak-Markov identities are applied to the constructed
Brownian law and upgraded from coordinate processes to genuine compact-open
path Borel laws. The entire forward-increment path has the original path law
and is independent of the entire stopped past. Sign symmetry then proves
law preservation by literal reflection at every fixed time. There is no
stopping-time reflection or strong-Markov premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPathIndependentIncrements

open BrownianPathLaw BrownianGaussianSkeleton

def pastPath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ f (min t T),(continuous_path f).comp (continuous_id.min continuous_const)⟩

def futurePath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ f (T+t)-f T,((continuous_path f).comp (continuous_const.add continuous_id)).sub
    continuous_const⟩

def negPath (f : Path) : Path := ⟨fun t ↦ -f t,(continuous_path f).neg⟩

@[simp] theorem pastPath_eval (T t : ℝ≥0) (f : Path) : pastPath T f t = f (min t T) := rfl
@[simp] theorem futurePath_eval (T t : ℝ≥0) (f : Path) : futurePath T f t = f (T+t)-f T := rfl
@[simp] theorem negPath_eval (t : ℝ≥0) (f : Path) : negPath f t = -f t := rfl

theorem continuous_pastPath (T : ℝ≥0) : Continuous (pastPath T) := by
  let p : C(ℝ≥0,ℝ≥0) := ⟨fun t ↦ min t T,continuous_id.min continuous_const⟩
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ f.comp p)
  exact ContinuousMap.continuous_precomp p

theorem continuous_futurePath (T : ℝ≥0) : Continuous (futurePath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.eval (continuous_const.add continuous_snd)).sub
    ((continuous_eval T).comp continuous_fst)

theorem continuous_negPath : Continuous negPath := by
  change Continuous (fun f : C(ℝ≥0,ℝ) ↦ -f)
  exact continuous_id.neg

theorem measurable_pastPath (T : ℝ≥0) : Measurable (pastPath T) :=
  (continuous_pastPath T).measurable

theorem measurable_futurePath (T : ℝ≥0) : Measurable (futurePath T) :=
  (continuous_futurePath T).measurable

theorem measurable_negPath : Measurable negPath := continuous_negPath.measurable

def pastLaw (T : ℝ≥0) : Measure Path := pathLaw.map (pastPath T)

instance pastLaw_isProbability (T : ℝ≥0) : IsProbabilityMeasure (pastLaw T) :=
  Measure.isProbabilityMeasure_map (measurable_pastPath T).aemeasurable

/-- Equality of actual path laws follows from the proved finite Brownian
laws and the genuine rational-evaluation measurable embedding. -/
theorem map_eq_pathLaw_of_preBrownian (F : Path → Path) (hF : Measurable F)
    (hB : IsPreBrownianReal (fun t f ↦ F f t) pathLaw) : pathLaw.map F = pathLaw := by
  have hX : Measurable (fun f : Path ↦ fun t : ℝ≥0 ↦ F f t) :=
    measurable_pi_lambda _ (fun t ↦ (continuous_eval t).measurable.comp hF)
  have hY : Measurable (fun f : Path ↦ fun t : ℝ≥0 ↦ f t) :=
    measurable_pi_lambda _ (fun t ↦ (continuous_eval t).measurable)
  have hfull : pathLaw.map (fun f : Path ↦ fun t : ℝ≥0 ↦ F f t) =
      pathLaw.map (fun f : Path ↦ fun t : ℝ≥0 ↦ f t) :=
    (map_eq_iff_forall_finset_map_restrict_eq hX.aemeasurable hY.aemeasurable).mpr
      (fun I ↦ (hB.hasLaw I).map_eq.trans (pathLaw_hasLaw_finite I).map_eq.symm)
  let R : (ℝ≥0 → ℝ) → RationalTime → ℝ := fun x q ↦ x (rationalTimeReal q)
  have hR : Measurable R := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have he := congrArg (Measure.map R) hfull
  rw [Measure.map_map hR hX,Measure.map_map hR hY] at he
  apply rationalEval_measurableEmbedding.map_injective
  rw [Measure.map_map continuous_rationalEval.measurable hF]
  exact he

theorem futurePath_law (T : ℝ≥0) : pathLaw.map (futurePath T) = pathLaw := by
  apply map_eq_pathLaw_of_preBrownian _ (measurable_futurePath T)
  exact isBrownian_pathLaw.toIsPreBrownianReal.shift T

theorem negPath_law : pathLaw.map negPath = pathLaw := by
  apply map_eq_pathLaw_of_preBrownian _ measurable_negPath
  exact isBrownian_pathLaw.toIsPreBrownianReal.neg

/-- Coordinate independence really implies independence in the actual
path Borel sigma algebra, by injectivity of the product embedding. -/
theorem indepFun_paths_of_rational {X Y : Path → Path}
    (hX : Measurable X) (hY : Measurable Y)
    (hI : IndepFun (rationalEval ∘ X) (rationalEval ∘ Y) pathLaw) : IndepFun X Y pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mpr
  let e := Prod.map rationalEval rationalEval
  have he : MeasurableEmbedding e := rationalEval_measurableEmbedding.prodMap
    rationalEval_measurableEmbedding
  apply he.map_injective
  rw [Measure.map_map he.measurable (hX.prodMk hY),
    ← Measure.map_prod_map (pathLaw.map X) (pathLaw.map Y)
      continuous_rationalEval.measurable continuous_rationalEval.measurable,
    Measure.map_map continuous_rationalEval.measurable hX,
    Measure.map_map continuous_rationalEval.measurable hY]
  exact hI.map_prod_eq_prod_map_map
    (continuous_rationalEval.measurable.comp hX).aemeasurable
    (continuous_rationalEval.measurable.comp hY).aemeasurable

/-- Entire continuous forward increments are independent of the entire
continuous stopped past under the actually constructed Brownian law. -/
theorem past_future_independent (T : ℝ≥0) : IndepFun (pastPath T) (futurePath T) pathLaw := by
  apply indepFun_paths_of_rational (measurable_pastPath T) (measurable_futurePath T)
  let P : (Iic T → ℝ) → RationalTime → ℝ :=
    fun x q ↦ x ⟨min (rationalTimeReal q) T,by exact min_le_right (rationalTimeReal q) T⟩
  let Q : (ℝ≥0 → ℝ) → RationalTime → ℝ := fun x q ↦ x (rationalTimeReal q)
  have hP : Measurable P := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have hQ : Measurable Q := measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  exact (isBrownian_pathLaw.toIsPreBrownianReal.indepFun_shift T).symm.comp hP hQ

theorem past_future_jointLaw (T : ℝ≥0) :
    pathLaw.map (fun f ↦ (pastPath T f,futurePath T f)) = (pastLaw T).prod pathLaw := by
  rw [(past_future_independent T).map_prod_eq_prod_map_map
    (measurable_pastPath T).aemeasurable (measurable_futurePath T).aemeasurable,futurePath_law]
  rfl

def splicePath (T : ℝ≥0) (p : Path × Path) : Path :=
  ⟨fun t ↦ p.1 (min t T)+p.2 (t-T),
    ((continuous_path p.1).comp (continuous_id.min continuous_const)).add
      ((continuous_path p.2).comp (continuous_id.sub continuous_const))⟩

@[simp] theorem splicePath_eval (T t : ℝ≥0) (p : Path × Path) :
    splicePath T p t = p.1 (min t T)+p.2 (t-T) := rfl

theorem continuous_splicePath (T : ℝ≥0) : Continuous (splicePath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.eval (continuous_snd.min continuous_const)).add
    (continuous_fst.snd.eval (continuous_snd.sub continuous_const))

theorem measurable_splicePath (T : ℝ≥0) : Measurable (splicePath T) :=
  (continuous_splicePath T).measurable

theorem futurePath_tsub (T t : ℝ≥0) (f : Path) :
    futurePath T f (t-T) = f t-f (min t T) := by
  rw [futurePath_eval]
  rcases le_total t T with h | h
  · simp only [tsub_eq_zero_of_le h,add_zero,min_eq_left h,sub_self]
  · rw [add_tsub_cancel_of_le h,min_eq_right h]

theorem splice_past_future (T : ℝ≥0) (f : Path) :
    splicePath T (pastPath T f,futurePath T f) = f := by
  apply ContinuousMap.ext
  intro t
  rw [splicePath_eval,pastPath_eval,min_assoc,min_self,futurePath_tsub]
  ring

theorem splice_product_law (T : ℝ≥0) :
    ((pastLaw T).prod pathLaw).map (splicePath T) = pathLaw := by
  rw [← past_future_jointLaw T,Measure.map_map (measurable_splicePath T)
    ((measurable_pastPath T).prodMk (measurable_futurePath T))]
  have he : splicePath T ∘ (fun f ↦ (pastPath T f,futurePath T f)) = (id : Path → Path) :=
    funext (fun f ↦ splice_past_future T f)
  rw [he,Measure.map_id]

def reflectionPath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ 2*f (min t T)-f t,
    (((continuous_path f).comp (continuous_id.min continuous_const)).const_mul 2).sub
      (continuous_path f)⟩

@[simp] theorem reflectionPath_eval (T t : ℝ≥0) (f : Path) :
    reflectionPath T f t = 2*f (min t T)-f t := rfl

theorem continuous_reflectionPath (T : ℝ≥0) : Continuous (reflectionPath T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.eval (continuous_snd.min continuous_const)).const_mul 2).sub
    (continuous_fst.eval continuous_snd)

theorem measurable_reflectionPath (T : ℝ≥0) : Measurable (reflectionPath T) :=
  (continuous_reflectionPath T).measurable

theorem splice_past_neg_future (T : ℝ≥0) (f : Path) :
    splicePath T (pastPath T f,negPath (futurePath T f)) = reflectionPath T f := by
  apply ContinuousMap.ext
  intro t
  rw [splicePath_eval,pastPath_eval,min_assoc,min_self,negPath_eval,futurePath_tsub,
    reflectionPath_eval]
  ring

/-- Literal path reflection after every fixed time preserves the genuine
Brownian path probability law, derived from actual independent increments. -/
theorem reflectionPath_law (T : ℝ≥0) : pathLaw.map (reflectionPath T) = pathLaw := by
  have hS : Measurable (Prod.map (id : Path → Path) negPath) := measurable_id.prodMap measurable_negPath
  have he : reflectionPath T = splicePath T ∘ Prod.map (id : Path → Path) negPath ∘
      (fun f ↦ (pastPath T f,futurePath T f)) := by
    funext f
    exact (splice_past_neg_future T f).symm
  rw [he,← Measure.map_map (measurable_splicePath T)
    (hS.comp ((measurable_pastPath T).prodMk (measurable_futurePath T))),
    ← Measure.map_map hS ((measurable_pastPath T).prodMk (measurable_futurePath T)),
    past_future_jointLaw T,
    ← Measure.map_prod_map (pastLaw T) pathLaw measurable_id measurable_negPath,
    Measure.map_id,negPath_law,splice_product_law]

end PerronWright.BrownianPathIndependentIncrements
