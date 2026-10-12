import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Pi

/-!
Finite simultaneous Fubini for blocks of variables indexed by a
dependent family.  This is the measure-theoretic input for integrating
all degree-two core components at once after fixing branch types.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

theorem integral_piSigma_prod_blocks
    {K : Type*} [Fintype K]
    {J : K → Type*} [∀ k, Fintype (J k)]
    {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (f : (k : K) → (J k → S) → ℝ) :
    (∫ x : (Σ k, J k) → S,
        ∏ k : K, f k (fun j => x ⟨k, j⟩)
        ∂Measure.pi (fun _ : Σ k, J k => μ)) =
      ∏ k : K,
        ∫ y : J k → S, f k y
          ∂Measure.pi (fun _ : J k => μ) := by
  let e : (((Σ k, J k) → S) ≃ᵐ ((k : K) → J k → S)) :=
    MeasurableEquiv.piCurry (fun _ _ => S)
  have hmap :
      (Measure.pi (fun _ : Σ k, J k => μ)).map e =
        Measure.pi (fun k : K => Measure.pi (fun _ : J k => μ)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_piCurry
        (μ := fun (k : K) (_j : J k) => μ))
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Σ k, J k => μ))
      (Measure.pi (fun k : K => Measure.pi (fun _ : J k => μ))) :=
    ⟨e.measurable, hmap⟩
  calc
    _ = ∫ y : (k : K) → J k → S,
        ∏ k : K, f k (y k)
        ∂Measure.pi (fun k : K => Measure.pi (fun _ : J k => μ)) := by
      exact hmp.integral_comp' (fun y => ∏ k : K, f k (y k))
    _ = _ := integral_fintype_prod_eq_prod f

#print axioms PerronWright.GraphCore.integral_piSigma_prod_blocks

end PerronWright.GraphCore
