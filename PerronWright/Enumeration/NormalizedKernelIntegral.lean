import PerronWright.Enumeration.KernelGraphWeight

/-!
# Exact normalized finite-kernel integral

The literal core-path assembly, branch-coordinate measure relabelling, and
bounded kernel endpoint table are combined into one exact formula for every
actual connected positive-surplus core.
-/

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory
open scoped Classical

set_option linter.style.haveILetI false in
/-- Every actual connected minimum-degree-two graph of positive surplus has
an exact integral representation over a bounded normalized finite
multigraph. The returned edge length is zero on direct branch edges and is
the number of edges in the corresponding suppressed degree-two path
otherwise. -/
theorem exists_graphWeight_eq_normalizedKernelIntegral
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {k : ℕ}
    (G : SimpleGraph (Fin k))
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = k + ell) (s₀ : S) :
    ∃ (nv : Fin (2 * ell + 1)) (ne : Fin (3 * ell + 1))
      (table : Fin ne.val → Sym2 (Fin nv.val))
      (length : Fin ne.val → ℕ),
      M.graphWeight t G =
        ∫ x : Fin nv.val → S,
          (∏ i : Fin nv.val,
              Real.exp (-t * M.degreeFunction (x i))) *
            ∏ j : Fin ne.val,
              pathKernelEdgeFactor M t (length j) x (table j)
          ∂Measure.pi (fun _ : Fin nv.val => M.mu) := by
  classical
  let hacyc : (twoGraph G).IsAcyclic :=
    degreeTwo_induced_isAcyclic G hconn hmin hell (by simpa using hs)
  letI : Fintype (twoGraph G).ConnectedComponent := Fintype.ofFinite _
  letI : ∀ C : (twoGraph G).ConnectedComponent, Fintype C :=
    fun C => Fintype.ofFinite C
  letI : Fintype {e : Sym2 (Fin k) // e ∈ directBranchEdges G} :=
    FinsetCoe.fintype (directBranchEdges G)
  obtain ⟨nv, ne, eB, eE, table, htable⟩ :=
    exists_exact_bounded_kernel_relabeling G hconn hmin hell (by simpa using hs)
  letI : Fintype (KernelEdgeLabel G) := by
    dsimp only [KernelEdgeLabel]
    infer_instance
  obtain ⟨n, _hn, qL, qR, hne, hweight⟩ :=
    exists_graphWeight_eq_integral_corePathKernels M t G hacyc s₀
  let edgeLength : KernelEdgeLabel G → ℕ
    | Sum.inl C => n C + 1
    | Sum.inr _ => 0
  let length : Fin ne.val → ℕ := fun j => edgeLength (eE.symm j)
  refine ⟨nv, ne, table, length, ?_⟩
  rw [hweight]
  rw [integral_coreBranch_relabel M G hmin eB]
  apply integral_congr_ae
  filter_upwards [] with x
  let b : coreBranchIndex G → S :=
    fun c => x (eB (coreBranchEquivBranching G hmin c))
  change
    graphCoreBranchFactor M t G s₀ b *
        ∏ C : (twoGraph G).ConnectedComponent,
          pathKernel M t (n C + 1)
            (b (componentBoundaryStubBranchIndex G C (qL C)),
              b (componentBoundaryStubBranchIndex G C (qR C))) = _
  rw [graphCoreBranchFactor_relabel_eq_kernelFactors
    M t G hmin hacyc s₀ eB x]
  have hcomp :
      (∏ C : (twoGraph G).ConnectedComponent,
          pathKernel M t (n C + 1)
            (b (componentBoundaryStubBranchIndex G C (qL C)),
              b (componentBoundaryStubBranchIndex G C (qR C)))) =
        ∏ C : (twoGraph G).ConnectedComponent,
          pathKernelEdgeFactor M t (n C + 1) x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G))) := by
    apply Finset.prod_congr rfl
    intro C _
    simpa [b] using
      (pathKernelEdgeFactor_kernelBranchEndpoints_inl
        M t G hmin hacyc C (qL C) (qR C) (hne C) eB b).symm
  rw [hcomp]
  let actualFactor : KernelEdgeLabel G → ℝ := fun e =>
    pathKernelEdgeFactor M t (edgeLength e) x
      (Sym2.map eB (kernelBranchEndpoints G hmin hacyc e))
  have hsplit :
      (∏ e : KernelEdgeLabel G, actualFactor e) =
        (∏ C : (twoGraph G).ConnectedComponent,
          pathKernelEdgeFactor M t (n C + 1) x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inl C : KernelEdgeLabel G)))) *
        ∏ d : {e // e ∈ directBranchEdges G},
          pathKernelEdgeFactor M t 0 x
            (Sym2.map eB
              (kernelBranchEndpoints G hmin hacyc
                (Sum.inr d : KernelEdgeLabel G))) := by
    change
      (∏ e : (twoGraph G).ConnectedComponent ⊕
          {d // d ∈ directBranchEdges G}, actualFactor e) = _
    rw [Fintype.prod_sum_type]
  have hrelabel :
      (∏ e : KernelEdgeLabel G, actualFactor e) =
        ∏ j : Fin ne.val,
          pathKernelEdgeFactor M t (length j) x (table j) := by
    exact Fintype.prod_equiv eE
      actualFactor
      (fun j : Fin ne.val =>
        pathKernelEdgeFactor M t (length j) x (table j))
      (fun e => by
        have hlen : length (eE e) = edgeLength e := by
          simp [length]
        rw [hlen, htable e])
  rw [← hrelabel, hsplit]
  ring

end PerronWright.GraphCore
