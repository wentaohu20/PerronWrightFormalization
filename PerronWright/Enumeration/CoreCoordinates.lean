import PerronWright.Enumeration.CoreWeightFactor
import PerronWright.Enumeration.CoreBlockIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
Canonical coordinate grouping of the actual finite 2-core into its
branch vertices and all degree-two connected-component vertices.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

abbrev coreBranchIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {v : V // G.degree v ≠ 2}

/-- The coordinate index of a finite graph is exactly its non-degree-two
vertices plus the disjoint union of all degree-two components. -/
def coreCoordinateEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (coreBranchIndex G ⊕
      (Σ C : (twoGraph G).ConnectedComponent, C)) ≃ V :=
  (Equiv.sumCongr (Equiv.refl (coreBranchIndex G))
    ((componentVertexEquiv (twoGraph G)).trans
      (Equiv.subtypeEquivRight
        (fun v : V => by simp)))).trans
    (Equiv.sumCompl (fun v : V => G.degree v ≠ 2))

/-- Regroup a genuine core's type vector into its branch types and
the type vectors of all degree-two components. -/
def coreCoordinateMeasurableEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Type*} [MeasurableSpace S] :
    (V → S) ≃ᵐ
      (coreBranchIndex G → S) ×
        ((Σ C : (twoGraph G).ConnectedComponent, C) → S) :=
  (MeasurableEquiv.piCongrLeft (fun _ : V => S)
    (coreCoordinateEquiv G)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : coreBranchIndex G ⊕
        (Σ C : (twoGraph G).ConnectedComponent, C) => S))

/-- The regrouping preserves the literal independent product type
law; no asymptotic or probabilistic independence assumption is added. -/
theorem coreCoordinate_measurePreserving
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (twoGraph G).ConnectedComponent]
    [∀ C : (twoGraph G).ConnectedComponent, Fintype C]
    {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [SigmaFinite μ] :
    MeasurePreserving (coreCoordinateMeasurableEquiv G)
      (Measure.pi (fun _ : V => μ))
      ((Measure.pi (fun _ : coreBranchIndex G => μ)).prod
        (Measure.pi
          (fun _ : Σ C : (twoGraph G).ConnectedComponent, C => μ))) := by
  exact (measurePreserving_sumPiEquivProdPi
    (fun _ : coreBranchIndex G ⊕
      (Σ C : (twoGraph G).ConnectedComponent, C) => μ)).comp
    ((measurePreserving_piCongrLeft
      (fun _ : V => μ) (coreCoordinateEquiv G)).symm)

/-- Conditional on branch types, all genuine degree-two component
coordinates integrate simultaneously as independent product blocks. -/
theorem integral_core_component_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (twoGraph G).ConnectedComponent]
    [∀ C : (twoGraph G).ConnectedComponent, Fintype C]
    {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (B : (coreBranchIndex G → S) → ℝ)
    (F : (C : (twoGraph G).ConnectedComponent) →
      (coreBranchIndex G → S) → (C → S) → ℝ)
    (hInt : Integrable
      (fun p : (coreBranchIndex G → S) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → S) =>
        B p.1 * ∏ C : (twoGraph G).ConnectedComponent,
          F C p.1 (fun j => p.2 ⟨C, j⟩))
      ((Measure.pi (fun _ : coreBranchIndex G => μ)).prod
        (Measure.pi
          (fun _ : Σ C : (twoGraph G).ConnectedComponent, C => μ)))) :
    (∫ x : V → S,
      B (coreCoordinateMeasurableEquiv G x).1 *
        ∏ C : (twoGraph G).ConnectedComponent,
          F C (coreCoordinateMeasurableEquiv G x).1
            (fun j => (coreCoordinateMeasurableEquiv G x).2 ⟨C, j⟩)
      ∂Measure.pi (fun _ : V => μ)) =
      ∫ b : coreBranchIndex G → S,
        B b * ∏ C : (twoGraph G).ConnectedComponent,
          (∫ y : C → S, F C b y
            ∂Measure.pi (fun _ : C => μ))
        ∂Measure.pi (fun _ : coreBranchIndex G => μ) := by
  have hmp := coreCoordinate_measurePreserving G μ
  calc
    _ = ∫ p : (coreBranchIndex G → S) ×
          ((Σ C : (twoGraph G).ConnectedComponent, C) → S),
        B p.1 * ∏ C : (twoGraph G).ConnectedComponent,
          F C p.1 (fun j => p.2 ⟨C, j⟩)
        ∂((Measure.pi (fun _ : coreBranchIndex G => μ)).prod
          (Measure.pi
            (fun _ : Σ C : (twoGraph G).ConnectedComponent, C => μ))) := by
        exact hmp.integral_comp'
          (fun p : (coreBranchIndex G → S) ×
              ((Σ C : (twoGraph G).ConnectedComponent, C) → S) =>
            B p.1 * ∏ C : (twoGraph G).ConnectedComponent,
              F C p.1 (fun j => p.2 ⟨C, j⟩))
    _ = ∫ b : coreBranchIndex G → S,
          ∫ p : (Σ C : (twoGraph G).ConnectedComponent, C) → S,
            B b * ∏ C : (twoGraph G).ConnectedComponent,
              F C b (fun j => p ⟨C, j⟩)
            ∂Measure.pi
              (fun _ : Σ C : (twoGraph G).ConnectedComponent, C => μ)
          ∂Measure.pi (fun _ : coreBranchIndex G => μ) := by
        exact integral_prod _ hInt
    _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with b
        rw [integral_const_mul,
          integral_piSigma_prod_blocks μ (fun C => F C b)]

#print axioms PerronWright.GraphCore.coreCoordinateEquiv
#print axioms PerronWright.GraphCore.integral_core_component_blocks

end PerronWright.GraphCore
