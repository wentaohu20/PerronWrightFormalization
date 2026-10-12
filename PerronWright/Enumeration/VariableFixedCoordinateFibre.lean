import PerronWright.Enumeration.VariableKernelLoopOrientationBooleanAction
import PerronWright.Enumeration.VariableKernelLoopOrientationGraph
import PerronWright.Enumeration.VariablePositiveEdgePathIso
import PerronWright.Enumeration.VariableSubdivisionLengthRecovery

/-!
# The bounded-kernel fixed-coordinate loop-orientation fibre

This file collects the exact interfaces needed for the last, fixed-coordinate
part of the cubic subdivision fibre calculation.  Simultaneously reversing
any finite set of loop coordinates leaves the reconstructed labelled graph
unchanged.  Conversely, once a recovered positive-edge component has been
fixed, its path coordinate has only the two expected possibilities: the
canonical coordinate and its reversal.  Fixing the first boundary coordinate
removes the latter possibility.

The remaining global fibre theorem only has to identify the recovered kernel
vertex and edge coordinates.  After those coordinates have been fixed, the
results below isolate precisely the Boolean loop ambiguity.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical symmDiff

/-- The singleton Boolean orientation equivalence is the original
single-loop reversal equivalence. -/
theorem boundedKernelLoopOrientationSetSlotEquiv_singleton
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (e : BoundedKernelLoopEdge K) :
    boundedKernelLoopOrientationSetSlotEquiv L {e} =
      boundedKernelLoopEdgeSlotReverseEquiv L e := by
  apply Equiv.ext
  intro z
  cases z with
  | inl v => rfl
  | inr p =>
      rcases p with ⟨f, i⟩
      by_cases hfe : f = e.1
      · subst f
        rw [boundedKernelLoopOrientationSetSlotEquiv_loop_mem L {e} e (by simp),
          boundedKernelLoopEdgeSlotReverseEquiv_same]
      · by_cases hf : ((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag
        · let d : BoundedKernelLoopEdge K := ⟨f, hf⟩
          have hde : d ≠ e := by
            intro h
            apply hfe
            exact congrArg Subtype.val h
          rw [show
              (.inr ⟨f, i⟩ : BoundedKernelSubdivisionSlot L) =
                .inr ⟨d.1, i⟩ by rfl,
            boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L {e} d (by simpa),
            boundedKernelLoopEdgeSlotReverseEquiv_other L e f hfe]
        · rw [boundedKernelLoopOrientationSetSlotEquiv_nonloop L {e} f hf,
            boundedKernelLoopEdgeSlotReverseEquiv_other L e f hfe]

/-- Reversing a singleton loop set agrees exactly with `reverseLoop`. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_singleton
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K) :
    D.reverseLoops {e} = D.reverseLoop e := by
  cases D with
  | mk profile labels =>
      simp only [reverseLoops, reverseLoop]
      congr 1
      exact congrArg (fun E => E.trans labels)
        (boundedKernelLoopOrientationSetSlotEquiv_singleton profile e)

/-- Adjoining one new loop to a Boolean orientation set is the same as first
reversing that loop and then applying the old orientation set. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_insert
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : BoundedKernelLoopEdge K)
    (A : Finset (BoundedKernelLoopEdge K))
    (he : e ∉ A) :
    D.reverseLoops (insert e A) = (D.reverseLoop e).reverseLoops A := by
  have hset : ({e} ∆ A : Finset (BoundedKernelLoopEdge K)) = insert e A := by
    ext d
    by_cases hde : d = e
    · subst d
      simp [Finset.mem_symmDiff, he]
    · simp [Finset.mem_symmDiff, hde]
  calc
    D.reverseLoops (insert e A) = D.reverseLoops ({e} ∆ A) := by rw [hset]
    _ = (D.reverseLoops {e}).reverseLoops A :=
      (D.reverseLoops_reverseLoops {e} A).symm
    _ = (D.reverseLoop e).reverseLoops A := by
      rw [D.reverseLoops_singleton e]

/-- Every simultaneous loop-orientation reversal preserves the reconstructed
labelled simple graph. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_reconstructedGraph
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    (D.reverseLoops A).reconstructedGraph = D.reconstructedGraph := by
  induction A using Finset.induction_on generalizing D with
  | empty =>
      rw [D.reverseLoops_empty]
  | @insert e A he ih =>
      rw [D.reverseLoops_insert e A he]
      calc
        ((D.reverseLoop e).reverseLoops A).reconstructedGraph =
            (D.reverseLoop e).reconstructedGraph := ih (D.reverseLoop e)
        _ = D.reconstructedGraph := D.reverseLoop_reconstructedGraph e

/-- Edge-finset form of simultaneous loop-orientation invariance. -/
theorem BoundedKernelSubdivisionDatum.reverseLoops_reconstructedGraph_edgeFinset
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (A : Finset (BoundedKernelLoopEdge K)) :
    (D.reverseLoops A).reconstructedGraph.edgeFinset =
      D.reconstructedGraph.edgeFinset := by
  rw [D.reverseLoops_reconstructedGraph A]

/-- Boolean form of path-coordinate rigidity on one recovered positive
kernel edge.  `false` denotes the canonical coordinate and `true` its
reversal. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_compare_bool
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (q : SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph) :
    ∃ reverse : Bool, ∀ i,
      q i = D.positiveEdgePathIso K e (if reverse then i.rev else i) := by
  rcases D.positiveEdgePathIso_compare K e q with h | h
  · exact ⟨false, by simpa using h⟩
  · exact ⟨true, by simpa using h⟩

/-- A family of coordinates on all recovered positive kernel-edge components
admits a simultaneous Boolean orientation choice.  This is the pointwise
comparison used when assembling the fixed-coordinate fibre. -/
theorem BoundedKernelSubdivisionDatum.exists_positiveEdgePathOrientation
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (q : ∀ e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val},
      SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
        (D.positiveEdgeComponent K e).toSimpleGraph) :
    ∃ reverse :
        {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val} → Bool,
      ∀ e i,
        q e i = D.positiveEdgePathIso K e
          (if reverse e then i.rev else i) := by
  choose reverse hreverse using
    fun e => D.positiveEdgePathIso_compare_bool K e (q e)
  exact ⟨reverse, hreverse⟩

/-- Once the first boundary coordinate has been fixed, a positive-edge path
coordinate is the canonical one, rather than its reversal.  In the eventual
fibre theorem this disposes of every non-loop orientation after the ordered
kernel endpoints have been fixed. -/
theorem BoundedKernelSubdivisionDatum.positiveEdgePathIso_compare_anchored
    {k ell : ℕ}
    (K : LabelledBoundedKernel ell)
    (D : BoundedKernelSubdivisionDatum k K)
    (e : {e : Fin K.shape.2.1.val // 0 < (D.profile.length e).val})
    (q : SimpleGraph.pathGraph (D.profile.length e.1).val ≃g
      (D.positiveEdgeComponent K e).toSimpleGraph)
    (hfirst : q ⟨0, e.2⟩ =
      D.positiveEdgePathIso K e ⟨0, e.2⟩) :
    ∀ i, q i = D.positiveEdgePathIso K e i :=
  D.positiveEdgePathIso_eq_of_same_first K e q hfirst

/-- Assembly of the fixed-coordinate fibre.  Once the length profile and
branch labels agree, every non-loop coordinate is anchored, and each loop
coordinate is known to be either the given order or its reversal, all those
pointwise comparisons assemble into one simultaneous `reverseLoops` action.

This statement deliberately starts after recovered kernel-edge coordinates
have been identified.  That separation is necessary in the presence of
parallel kernel edges, which the reconstructed simple graph alone does not
canonically distinguish. -/
theorem exists_boundedKernel_reverseLoops_eq_of_fixed_coordinates
    {k ell : ℕ}
    {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K)
    (labels labels' : BoundedKernelSubdivisionSlot L ≃ Fin k)
    (hbranch : ∀ v : Fin K.shape.1.val,
      labels' (.inl v) = labels (.inl v))
    (hnonloop : ∀ (f : Fin K.shape.2.1.val),
      ¬((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag →
        ∀ i : Fin (L.length f).val,
          labels' (.inr ⟨f, i⟩) = labels (.inr ⟨f, i⟩))
    (hloop : ∀ e : BoundedKernelLoopEdge K,
      (∀ i : Fin (L.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) = labels (.inr ⟨e.1, i⟩)) ∨
      (∀ i : Fin (L.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) =
          labels (.inr ⟨e.1, Fin.rev i⟩))) :
    ∃ A : Finset (BoundedKernelLoopEdge K),
      ((⟨L, labels⟩ : BoundedKernelSubdivisionDatum k K).reverseLoops A) =
        ⟨L, labels'⟩ := by
  have horient : ∀ e : BoundedKernelLoopEdge K,
      ∃ reverse : Bool, ∀ i : Fin (L.length e.1).val,
        labels' (.inr ⟨e.1, i⟩) =
          labels (.inr ⟨e.1, if reverse then Fin.rev i else i⟩) := by
    intro e
    rcases hloop e with h | h
    · exact ⟨false, by simpa using h⟩
    · exact ⟨true, by simpa using h⟩
  choose reverse hreverse using horient
  let A : Finset (BoundedKernelLoopEdge K) :=
    Finset.univ.filter fun e => reverse e = true
  refine ⟨A, ?_⟩
  change BoundedKernelSubdivisionDatum.mk L
      ((boundedKernelLoopOrientationSetSlotEquiv L A).trans labels) =
    BoundedKernelSubdivisionDatum.mk L labels'
  apply congrArg (fun f : BoundedKernelSubdivisionSlot L ≃ Fin k =>
    BoundedKernelSubdivisionDatum.mk L f)
  apply Equiv.ext
  intro z
  cases z with
  | inl v =>
      change labels (.inl v) = labels' (.inl v)
      exact (hbranch v).symm
  | inr p =>
      rcases p with ⟨f, i⟩
      by_cases hf : ((boundedKernelFiniteMultiGraph K.shape).endpoints f).IsDiag
      · let e : BoundedKernelLoopEdge K := ⟨f, hf⟩
        by_cases hr : reverse e = true
        · have heA : e ∈ A := by simp [A, hr]
          change labels
              (boundedKernelLoopOrientationSetSlotEquiv L A (.inr ⟨e.1, i⟩)) =
            labels' (.inr ⟨e.1, i⟩)
          rw [boundedKernelLoopOrientationSetSlotEquiv_loop_mem L A e heA]
          have h := (hreverse e i).symm
          simpa [hr] using h
        · have heA : e ∉ A := by simp [A, hr]
          have hrfalse : reverse e = false := Bool.eq_false_of_not_eq_true hr
          change labels
              (boundedKernelLoopOrientationSetSlotEquiv L A (.inr ⟨e.1, i⟩)) =
            labels' (.inr ⟨e.1, i⟩)
          rw [boundedKernelLoopOrientationSetSlotEquiv_loop_not_mem L A e heA]
          have h := (hreverse e i).symm
          simpa [hrfalse] using h
      · change labels
            (boundedKernelLoopOrientationSetSlotEquiv L A (.inr ⟨f, i⟩)) =
          labels' (.inr ⟨f, i⟩)
        rw [boundedKernelLoopOrientationSetSlotEquiv_nonloop L A f hf]
        exact (hnonloop f hf i).symm

end PerronWright.GraphCore
