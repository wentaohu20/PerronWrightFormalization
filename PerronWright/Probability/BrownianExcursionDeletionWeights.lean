import PerronWright.Probability.BrownianExcursionDeletionGeometry
import PerronWright.Probability.ContinuousExcursionDeletionSection
import PerronWright.Probability.BrownianExcursionTuplePoissonWeights
import Mathlib.Logic.Embedding.Basic

/-! # Actual surviving area and all-order Poisson sums under deletion

The equivalence reselects rational representatives of the transported
connected intervals. Their literal complete areas and lengths agree,
so every injective-tuple Poisson weight sum is preserved by reindexing.
Neither a stochastic deletion law nor a finite moment is assumed.
-/

open MeasureTheory Topology Set
open scoped Classical NNReal BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionDeletionWeights

open BrownianPathLaw BrownianPathReflectionLaw BrownianFullHorizonExcursionAreas
open FullHorizonExcursionComponents FullHorizonExcursionSection
open ContinuousPathIntervalDeletion ContinuousExcursionDeletionComponents
open ContinuousExcursionDeletionSection BrownianExcursionDeletionGeometry
open BrownianExcursionTuplePoissonWeights (poissonWeight)

def survivingRepresentatives (q lambda : ℝ) (f : Path) :=
  {r : ℚ // Representative (driftedReflectionPath lambda f) r ∧
    component (driftedReflectionPath lambda f) (r : ℝ) ≠ component (driftedReflectionPath lambda f) q}

def remainingRepresentatives (q lambda : ℝ) (f : Path) :=
  {r : ℚ // Representative (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) r}

private theorem length_area_eq_of_components_eq (lambda : ℝ) (f : Path) (x y : ℝ)
    (hx : x ∈ positiveSet (driftedReflectionPath lambda f))
    (hy : y ∈ positiveSet (driftedReflectionPath lambda f))
    (he : component (driftedReflectionPath lambda f) x = component (driftedReflectionPath lambda f) y)
    (hb : BddAbove (component (driftedReflectionPath lambda f) y)) :
    FullHorizonExcursionComponents.length x (driftedReflectionPath lambda f) =
      FullHorizonExcursionComponents.length y (driftedReflectionPath lambda f) ∧
        excursionArea x lambda f = excursionArea y lambda f := by
  have hbx : BddAbove (component (driftedReflectionPath lambda f) x) := he.symm ▸ hb
  constructor
  · simp only [FullHorizonExcursionComponents.length,leftEndpoint,rightEndpoint,if_pos hx,if_pos hy,he]
  · apply NNReal.eq
    rw [excursionArea_eq_component_integral hbx,excursionArea_eq_component_integral hb,he]

theorem surviving_area_equiv_exists (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hbq : BddAbove (component (driftedReflectionPath lambda f) q))
    (hfinite : ∀ r : ℚ, BddAbove (component (driftedReflectionPath lambda f) (r : ℝ))) :
    ∃ E : survivingRepresentatives q lambda f ≃ remainingRepresentatives q lambda f,
      ∀ r,
        FullHorizonExcursionComponents.length ((E r).1 : ℝ)
            (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) =
          FullHorizonExcursionComponents.length (r.1 : ℝ) (driftedReflectionPath lambda f) ∧
        excursionArea ((E r).1 : ℝ) (deletedParameter q lambda f) (deletedPath q lambda f) =
          excursionArea (r.1 : ℝ) lambda f := by
  let R := driftedReflectionPath lambda f
  let a := leftTime q lambda f
  let l := cutLength q lambda f
  have hqR : q ∈ positiveSet R := hq
  have hbR : BddAbove (component R q) := hbq
  have hab : a+l = rightTime q lambda f := by
    apply add_tsub_cancel_of_le
    apply NNReal.coe_le_coe.mp
    rw [coe_leftTime,coe_rightTime]
    exact ((endpoint_bounds hq hbq).2.1.trans (endpoint_bounds hq hbq).2.2).le
  have hz : R a = 0 := leftEndpoint_zero hq hbq (ContinuousPathReflection.reflected_zero _)
  have hend : R (a+l) = 0 := by rw [hab]; exact rightEndpoint_zero hq hbq
  have hc : component R q = Ioo (a : ℝ) (a+l : ℝ≥0) := by
    rw [component_eq_Ioo hqR hbR,hab]
    simp only [R,a,coe_leftTime,coe_rightTime]
  obtain ⟨E,hE⟩ := representativeEquiv_exists R a l q hz hend hc
  have hd := deleted_reflection_eq q lambda f hq hbq
  let C : {r : ℚ // Representative (deletionPath a l R) r} ≃ remainingRepresentatives q lambda f :=
    Equiv.subtypeEquivRight
      (p := fun r : ℚ ↦ Representative (deletionPath a l R) r)
      (q := fun r : ℚ ↦ Representative
        (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) r)
      (fun r ↦ by rw [hd])
  let EE : survivingRepresentatives q lambda f ≃ remainingRepresentatives q lambda f := E.trans C
  refine ⟨EE,?_⟩
  intro r
  have hcomp : component
      (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) ((EE r).1 : ℝ) =
        component (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))
          (eraseTime a l (r.1 : ℝ)) := by
    change component
        (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) ((E r).1 : ℝ) =
      component (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))
        (eraseTime a l (r.1 : ℝ))
    have hd' : driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f) =
        deletionPath a l R := hd
    rw [hd']
    exact (hE r).trans (transported_component R a l q r.1 hz hend hc r.2.1.1 r.2.2).symm
  have hrnew : ((EE r).1 : ℝ) ∈ positiveSet
      (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) := (EE r).2.1
  have hranchor : eraseTime a l (r.1 : ℝ) ∈ positiveSet
      (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f)) :=
    (component_nonempty_iff _ _).mp (hcomp ▸ ((component_nonempty_iff _ _).mpr hrnew))
  by_cases hra : (r.1 : ℝ) < a
  · have hw := remaining_before_length_area q lambda r.1 f hq hbq r.2.1.1 (hfinite r.1) hra
    have hca := component_before_deletion R a l r.1 r.2.1.1 hra hz
    have hbnew : BddAbove (component
        (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))
          (eraseTime a l (r.1 : ℝ))) := by
      rw [eraseTime,if_pos hra,hd,hca]
      exact hfinite r.1
    have haeq := length_area_eq_of_components_eq (deletedParameter q lambda f) (deletedPath q lambda f)
      (EE r).1 (eraseTime a l r.1) hrnew hranchor hcomp hbnew
    simp only [eraseTime,if_pos hra] at haeq
    exact ⟨haeq.1.trans hw.1,haeq.2.trans hw.2⟩
  · have hbr : (rightTime q lambda f : ℝ) < (r.1 : ℝ) := by
      rw [← hab]
      exact (surviving_anchor_side R a l q r.1 hz hend hc r.2.1.1 r.2.2).resolve_left hra
    have hw := remaining_after_length_area q lambda r.1 f hq hbq r.2.1.1 (hfinite r.1) hbr
    have hca := component_after_deletion R a l r.1 r.2.1.1 (by rwa [hab]) hz hend
    have hbnew : BddAbove (component
        (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))
          (eraseTime a l (r.1 : ℝ))) := by
      rw [eraseTime,if_neg hra,hd,hca]
      obtain ⟨z,hz⟩ := hfinite r.1
      refine ⟨z-l,?_⟩
      rintro t ⟨u,hu,rfl⟩
      exact sub_le_sub_right (hz hu) _
    have haeq := length_area_eq_of_components_eq (deletedParameter q lambda f) (deletedPath q lambda f)
      (EE r).1 (eraseTime a l r.1) hrnew hranchor hcomp hbnew
    simp only [eraseTime,if_neg hra] at haeq
    exact ⟨haeq.1.trans hw.1,haeq.2.trans hw.2⟩

theorem surviving_poisson_tuple_sum (q lambda : ℝ) (f : Path)
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hbq : BddAbove (component (driftedReflectionPath lambda f) q))
    (hfinite : ∀ r : ℚ, BddAbove (component (driftedReflectionPath lambda f) (r : ℝ)))
    (d : ℕ) (marks : Fin d → ℕ) (H : (Fin d → ℝ) → ℝ≥0∞) :
    (∑' e : Fin d ↪ survivingRepresentatives q lambda f,
      H (fun i ↦ FullHorizonExcursionComponents.length ((e i).1 : ℝ) (driftedReflectionPath lambda f)) *
        ∏ i, poissonWeight (excursionArea ((e i).1 : ℝ) lambda f) (marks i)) =
    ∑' e : Fin d ↪ remainingRepresentatives q lambda f,
      H (fun i ↦ FullHorizonExcursionComponents.length ((e i).1 : ℝ)
          (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))) *
        ∏ i, poissonWeight (excursionArea ((e i).1 : ℝ)
          (deletedParameter q lambda f) (deletedPath q lambda f)) (marks i) := by
  obtain ⟨E,hE⟩ := surviving_area_equiv_exists q lambda f hq hbq hfinite
  let V := Equiv.embeddingCongr (Equiv.refl (Fin d)) E
  calc
    _ = ∑' e : Fin d ↪ survivingRepresentatives q lambda f,
        H (fun i ↦ FullHorizonExcursionComponents.length (((V e) i).1 : ℝ)
            (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))) *
          ∏ i, poissonWeight (excursionArea (((V e) i).1 : ℝ)
            (deletedParameter q lambda f) (deletedPath q lambda f)) (marks i) := by
      apply tsum_congr
      intro e
      have hl : (fun i ↦ FullHorizonExcursionComponents.length (((V e) i).1 : ℝ)
          (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))) =
          (fun i ↦ FullHorizonExcursionComponents.length ((e i).1 : ℝ) (driftedReflectionPath lambda f)) :=
        funext (fun i ↦ (hE (e i)).1)
      rw [hl]
      congr 1
      symm
      apply Finset.prod_congr rfl
      intro i _
      exact congrArg (fun A : ℝ≥0 ↦ poissonWeight A (marks i)) (hE (e i)).2
    _ = _ := V.tsum_eq (fun e : Fin d ↪ remainingRepresentatives q lambda f ↦
      H (fun i ↦ FullHorizonExcursionComponents.length ((e i).1 : ℝ)
          (driftedReflectionPath (deletedParameter q lambda f) (deletedPath q lambda f))) *
        ∏ i, poissonWeight (excursionArea ((e i).1 : ℝ)
          (deletedParameter q lambda f) (deletedPath q lambda f)) (marks i))

end PerronWright.BrownianExcursionDeletionWeights
