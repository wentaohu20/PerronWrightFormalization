import PerronWright.Enumeration.DegreeTwoWeight

noncomputable section

namespace PerronWright.GraphCore

/-- The path response with `m` internal degree-two vertices.  The
first edge enters one internal vertex with its exact isolation weight;
all subsequent internal vertices are integrated by continuous-kernel
composition.  Thus `m = 0` is one edge and `m = 1` is exactly the
two-edge response already obtained by suppressing one vertex. -/
def pathKernel
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) : ℕ → C(S × S, ℝ)
  | 0 => pathSecondKernel M t
  | m + 1 => KernelMap.comp M.mu (pathFirstKernel M t) (pathKernel M t m)

theorem pathKernel_zero
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) :
    pathKernel M t 0 = pathSecondKernel M t := rfl

theorem pathKernel_one
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) :
    pathKernel M t 1 = path2ContinuousKernel M t := rfl

/-- Exact integral recurrence for all positive path lengths, with no
formal generating-function assumption. -/
theorem pathKernel_succ_apply
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (m : ℕ) (a b : S) :
    pathKernel M t (m + 1) (a, b) =
      ∫ y : S, (t * M.kernel a y) *
        Real.exp (-t * M.degreeFunction y) *
        pathKernel M t m (y, b) ∂M.mu := by
  rw [pathKernel, KernelMap.comp_apply]
  rfl

#print axioms PerronWright.GraphCore.pathKernel_succ_apply

end PerronWright.GraphCore

