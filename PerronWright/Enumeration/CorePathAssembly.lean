import PerronWright.Enumeration.CorePathIntegral

/-!
# Simultaneous assembly of all actual path components

This module applies the exact component-to-path-kernel transfer to
every degree-two connected component of an acyclic two-graph at once.
The path lengths and endpoint stubs are selected from the finite graph
itself, so the resulting formula for the literal compact-BJR graph
weight requires no abstract endpoint map or component-factorization
interface.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

/-- Simultaneously choose the intrinsic length and two actual boundary
stubs of every degree-two component and replace every conditional
component integral by the corresponding analytic path kernel. -/
theorem exists_graphWeight_eq_integral_corePathKernels
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    [Fintype (twoGraph G).ConnectedComponent]
    (hacyc : (twoGraph G).IsAcyclic)
    (s₀ : S) :
    ∃ n : (twoGraph G).ConnectedComponent → ℕ,
      (∀ C : (twoGraph G).ConnectedComponent,
        Fintype.card C = n C + 1) ∧
      ∃ qL qR : ∀ C : (twoGraph G).ConnectedComponent,
          {q // q ∈ componentBoundaryStubs G C},
        (∀ C, qL C ≠ qR C) ∧
        M.graphWeight t G =
          ∫ b : coreBranchIndex G → S,
            graphCoreBranchFactor M t G s₀ b *
              ∏ C : (twoGraph G).ConnectedComponent,
                pathKernel M t (n C + 1)
                  (b (componentBoundaryStubBranchIndex G C (qL C)),
                    b (componentBoundaryStubBranchIndex G C (qR C)))
            ∂Measure.pi (fun _ : coreBranchIndex G => M.mu) := by
  have hchoice := fun C : (twoGraph G).ConnectedComponent =>
    exists_componentPathOrder_with_boundaryStubs G hacyc C
  choose n hn e qL qR hne hL hR using hchoice
  refine ⟨n, hn, qL, qR, hne, ?_⟩
  rw [graphWeight_eq_integral_coreComponentFactors M t G s₀]
  apply integral_congr_ae
  filter_upwards [] with b
  congr 1
  apply Finset.prod_congr rfl
  intro C _
  exact integral_graphCoreComponentFactor_eq_pathKernel_of_order
    M t G hacyc s₀ C b (e C) (qL C) (qR C)
      (hne C) (hL C) (hR C)

end PerronWright.GraphCore
