import PerronWright.Enumeration.VariableKernelCoordinateMultiplicity
import PerronWright.Enumeration.VariableKernelConnectivity

/-!
# Exact degree geometry of variable-valence subdivisions

Endpoint occurrences of the bounded multigraph embed into incident edges of
the reconstructed simple graph.  Together with the global handshake
identity, this proves saturation of all local lower bounds: internal path
slots have degree exactly two and branch slots retain exactly their kernel
multidegree.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical BigOperators

/-- Select one of the two canonically ordered endpoint occurrences. -/
def boundedKernelEndpointAt
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (side : Fin 2) : Fin K.shape.1.val :=
  if side.val = 0 then
    (boundedKernelOrderedEndpoints K.shape e).1
  else
    (boundedKernelOrderedEndpoints K.shape e).2

/-- A literal endpoint occurrence; a loop has two occurrences. -/
abbrev BoundedKernelEndpointOccurrence
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (u : Fin K.shape.1.val) :=
  {p : Fin K.shape.2.1.val × Fin 2 //
    boundedKernelEndpointAt K p.1 p.2 = u}

noncomputable instance boundedKernelEndpointOccurrenceFintype
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (u : Fin K.shape.1.val) :
    Fintype (BoundedKernelEndpointOccurrence K u) := by
  unfold BoundedKernelEndpointOccurrence
  infer_instance

private theorem boundedEndpointSide_card_eq_count
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (u : Fin K.shape.1.val) :
    Fintype.card {side : Fin 2 // boundedKernelEndpointAt K e side = u} =
      (K.shape.2.2 e).toMultiset.count u := by
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  have hc := congrArg
    (fun z : Sym2 (Fin K.shape.1.val) ↦ z.toMultiset.count u)
    (boundedKernelOrderedEndpoints_mk K e)
  rw [← hc]
  have hm :
      s((boundedKernelOrderedEndpoints K.shape e).1,
        (boundedKernelOrderedEndpoints K.shape e).2).toMultiset =
        (↑[(boundedKernelOrderedEndpoints K.shape e).1,
          (boundedKernelOrderedEndpoints K.shape e).2] :
          Multiset (Fin K.shape.1.val)) := rfl
  rw [hm, Multiset.coe_count]
  by_cases ha : (boundedKernelOrderedEndpoints K.shape e).1 = u <;>
    by_cases hb : (boundedKernelOrderedEndpoints K.shape e).2 = u <;>
    simp [boundedKernelEndpointAt, ha, hb]

/-- Endpoint occurrences are counted by the literal multigraph degree. -/
theorem boundedKernelEndpointOccurrence_card
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (u : Fin K.shape.1.val) :
    Fintype.card (BoundedKernelEndpointOccurrence K u) =
      (boundedKernelFiniteMultiGraph K.shape).degree u := by
  let E := Equiv.subtypeProdEquivSigmaSubtype
    (fun (e : Fin K.shape.2.1.val) (side : Fin 2) ↦
      boundedKernelEndpointAt K e side = u)
  calc
    Fintype.card (BoundedKernelEndpointOccurrence K u) =
        Fintype.card
          (Σ e : Fin K.shape.2.1.val,
            {side : Fin 2 // boundedKernelEndpointAt K e side = u}) :=
      Fintype.card_congr E
    _ = ∑ e : Fin K.shape.2.1.val,
          Fintype.card {side : Fin 2 //
            boundedKernelEndpointAt K e side = u} := by
      rw [Fintype.card_sigma]
    _ = ∑ e : Fin K.shape.2.1.val,
          (K.shape.2.2 e).toMultiset.count u := by
      apply Finset.sum_congr rfl
      intro e _
      exact boundedEndpointSide_card_eq_count K e u
    _ = (boundedKernelFiniteMultiGraph K.shape).degree u := by
      unfold PerronWright.FiniteMultiGraph.degree boundedKernelFiniteMultiGraph
      apply Finset.sum_congr rfl
      intro e _
      exact (finiteMultiGraph_incidence_eq_count (K.shape.2.2 e) u).symm

/-- Reconstructed edge slot adjacent to one endpoint occurrence. -/
def BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {u : Fin K.shape.1.val}
    (p : BoundedKernelEndpointOccurrence K u) :
    BoundedKernelSubdivisionEdgeSlot D :=
  if p.1.2.val = 0 then
    ⟨p.1.1, (0 : Fin ((D.profile.length p.1.1).val + 1))⟩
  else
    ⟨p.1.1, Fin.last (D.profile.length p.1.1).val⟩

@[simp] theorem BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_fst
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {u : Fin K.shape.1.val}
    (p : BoundedKernelEndpointOccurrence K u) :
    (D.endpointOccurrenceEdgeSlot p).1 = p.1.1 := by
  by_cases h : p.1.2.val = 0 <;>
    simp [BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot, h]

theorem BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_eq_start
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {u : Fin K.shape.1.val}
    (p : BoundedKernelEndpointOccurrence K u)
    (h : p.1.2.val = 0) :
    D.endpointOccurrenceEdgeSlot p =
      ⟨p.1.1, (0 : Fin ((D.profile.length p.1.1).val + 1))⟩ := by
  simp [BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot, h]
  rfl

theorem BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_eq_end
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    {u : Fin K.shape.1.val}
    (p : BoundedKernelEndpointOccurrence K u)
    (h : p.1.2.val ≠ 0) :
    D.endpointOccurrenceEdgeSlot p =
      ⟨p.1.1, Fin.last (D.profile.length p.1.1).val⟩ := by
  simp [BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot, h]
  rfl

/-- Distinct endpoint occurrences give distinct reconstructed edge slots;
the two sides of a loop are separated by the loop-length restriction. -/
theorem BoundedKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_injective
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    Function.Injective (D.endpointOccurrenceEdgeSlot (u := u)) := by
  rintro ⟨⟨e, i⟩, hi⟩ ⟨⟨f, j⟩, hj⟩ hslot
  have hef : e = f := by
    have h := congrArg Sigma.fst hslot
    have he := D.endpointOccurrenceEdgeSlot_fst
      (⟨⟨e, i⟩, hi⟩ : BoundedKernelEndpointOccurrence K u)
    have hf := D.endpointOccurrenceEdgeSlot_fst
      (⟨⟨f, j⟩, hj⟩ : BoundedKernelEndpointOccurrence K u)
    change (D.endpointOccurrenceEdgeSlot
      (⟨⟨e, i⟩, hi⟩ : BoundedKernelEndpointOccurrence K u)).1 = e at he
    change (D.endpointOccurrenceEdgeSlot
      (⟨⟨f, j⟩, hj⟩ : BoundedKernelEndpointOccurrence K u)).1 = f at hf
    calc
      e = (D.endpointOccurrenceEdgeSlot
          (⟨⟨e, i⟩, hi⟩ : BoundedKernelEndpointOccurrence K u)).1 :=
        he.symm
      _ = (D.endpointOccurrenceEdgeSlot
          (⟨⟨f, j⟩, hj⟩ : BoundedKernelEndpointOccurrence K u)).1 := h
      _ = f := hf
  subst f
  let pi : BoundedKernelEndpointOccurrence K u := ⟨⟨e, i⟩, hi⟩
  let pj : BoundedKernelEndpointOccurrence K u := ⟨⟨e, j⟩, hj⟩
  have hslot' : D.endpointOccurrenceEdgeSlot pi =
      D.endpointOccurrenceEdgeSlot pj := hslot
  have hij : i = j := by
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · exact Fin.ext (hi0.trans hj0.symm)
      · exfalso
        have ha : (boundedKernelOrderedEndpoints K.shape e).1 = u := by
          simpa [boundedKernelEndpointAt, hi0] using hi
        have hb : (boundedKernelOrderedEndpoints K.shape e).2 = u := by
          simpa [boundedKernelEndpointAt, hj0] using hj
        have hloop : (K.shape.2.2 e).IsDiag := by
          rw [← boundedKernelOrderedEndpoints_mk K e, Sym2.mk_isDiag_iff]
          exact ha.trans hb.symm
        have hlen := D.profile.loopLength e hloop
        have hpi0 : pi.1.2.val = 0 := by simpa [pi] using hi0
        have hpj0 : pj.1.2.val ≠ 0 := by simpa [pj] using hj0
        have hs :
            (⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ :
              BoundedKernelSubdivisionEdgeSlot D) =
            ⟨e, Fin.last (D.profile.length e).val⟩ := by
          exact (D.endpointOccurrenceEdgeSlot_eq_start pi hpi0).symm.trans
            (hslot'.trans (D.endpointOccurrenceEdgeSlot_eq_end pj hpj0))
        have hv := congrArg
          (fun a : BoundedKernelSubdivisionEdgeSlot D ↦ a.2.val) hs
        change 0 = (D.profile.length e).val at hv
        omega
    · by_cases hj0 : j.val = 0
      · exfalso
        have ha : (boundedKernelOrderedEndpoints K.shape e).1 = u := by
          simpa [boundedKernelEndpointAt, hj0] using hj
        have hb : (boundedKernelOrderedEndpoints K.shape e).2 = u := by
          simpa [boundedKernelEndpointAt, hi0] using hi
        have hloop : (K.shape.2.2 e).IsDiag := by
          rw [← boundedKernelOrderedEndpoints_mk K e, Sym2.mk_isDiag_iff]
          exact ha.trans hb.symm
        have hlen := D.profile.loopLength e hloop
        have hpi0 : pi.1.2.val ≠ 0 := by simpa [pi] using hi0
        have hpj0 : pj.1.2.val = 0 := by simpa [pj] using hj0
        have hs :
            (⟨e, Fin.last (D.profile.length e).val⟩ :
              BoundedKernelSubdivisionEdgeSlot D) =
            ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ := by
          exact (D.endpointOccurrenceEdgeSlot_eq_end pi hpi0).symm.trans
            (hslot'.trans (D.endpointOccurrenceEdgeSlot_eq_start pj hpj0))
        have hv := congrArg
          (fun a : BoundedKernelSubdivisionEdgeSlot D ↦ a.2.val) hs
        change (D.profile.length e).val = 0 at hv
        omega
      · apply Fin.ext
        have hii := i.isLt
        have hjj := j.isLt
        omega
  apply Subtype.ext
  exact Prod.ext rfl hij

/-- The branch label occurs in the edge emitted by an endpoint occurrence. -/
theorem BoundedKernelSubdivisionDatum.branchLabel_mem_occurrenceEdge
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val)
    (p : BoundedKernelEndpointOccurrence K u) :
    D.branchLabel u ∈ D.subdivisionEdge (D.endpointOccurrenceEdgeSlot p) := by
  rcases p with ⟨⟨e, side⟩, hp⟩
  by_cases hs : side.val = 0
  · have hfirst : (boundedKernelOrderedEndpoints K.shape e).1 = u := by
      simpa [boundedKernelEndpointAt, hs] using hp
    rw [D.endpointOccurrenceEdgeSlot_eq_start ⟨⟨e, side⟩, hp⟩ hs]
    unfold BoundedKernelSubdivisionDatum.subdivisionEdge
    change D.branchLabel u ∈
      s(D.pathVertex e (0 : Fin ((D.profile.length e).val + 2)),
        D.pathVertex e (0 : Fin ((D.profile.length e).val + 1)).succ)
    rw [D.pathVertex_zero, hfirst]
    exact Sym2.mem_mk_left _ _
  · have hsecond : (boundedKernelOrderedEndpoints K.shape e).2 = u := by
      simpa [boundedKernelEndpointAt, hs] using hp
    rw [D.endpointOccurrenceEdgeSlot_eq_end ⟨⟨e, side⟩, hp⟩ hs]
    unfold BoundedKernelSubdivisionDatum.subdivisionEdge
    change D.branchLabel u ∈
      s(D.pathVertex e (Fin.last (D.profile.length e).val).castSucc,
        D.pathVertex e (Fin.succ (Fin.last (D.profile.length e).val)))
    rw [D.pathVertex_last, hsecond]
    exact Sym2.mem_mk_right _ _

/-- Endpoint occurrences embed into reconstructed incident edges. -/
noncomputable def BoundedKernelSubdivisionDatum.endpointOccurrenceIncidentEdge
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    BoundedKernelEndpointOccurrence K u →
      {z // z ∈ D.reconstructedGraph.incidenceFinset (D.branchLabel u)} :=
  fun p ↦ ⟨D.subdivisionEdge (D.endpointOccurrenceEdgeSlot p), by
    rw [D.reconstructedGraph.incidenceFinset_eq_filter]
    apply Finset.mem_filter.mpr
    refine ⟨?_, D.branchLabel_mem_occurrenceEdge u p⟩
    rw [D.reconstructedGraph_edgeFinset_eq_image]
    exact Finset.mem_image.mpr
      ⟨D.endpointOccurrenceEdgeSlot p, Finset.mem_univ _, rfl⟩⟩

theorem BoundedKernelSubdivisionDatum.endpointOccurrenceIncidentEdge_injective
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    Function.Injective (D.endpointOccurrenceIncidentEdge u) := by
  intro p q hpq
  apply D.endpointOccurrenceEdgeSlot_injective u
  apply D.subdivisionEdge_injective
  exact congrArg Subtype.val hpq

/-- Subdivision does not lower the degree of a branch vertex. -/
theorem BoundedKernelSubdivisionDatum.kernelDegree_le_branchVertex_degree
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    (boundedKernelFiniteMultiGraph K.shape).degree u ≤
      D.reconstructedGraph.degree (D.branchLabel u) := by
  rw [← boundedKernelEndpointOccurrence_card K u,
    ← D.reconstructedGraph.card_incidenceFinset_eq_degree]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (D.endpointOccurrenceIncidentEdge u)
    (D.endpointOccurrenceIncidentEdge_injective u)

/-- Local degree forced by one subdivision slot. -/
def BoundedKernelSubdivisionDatum.slotBaseDegree
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    BoundedKernelSubdivisionSlot D.profile → ℕ
  | .inl u => (boundedKernelFiniteMultiGraph K.shape).degree u
  | .inr _ => 2

theorem BoundedKernelSubdivisionDatum.slotBaseDegree_le
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (z : BoundedKernelSubdivisionSlot D.profile) :
    D.slotBaseDegree z ≤ D.reconstructedGraph.degree (D.labels z) := by
  rcases z with u | ⟨e, i⟩
  · exact D.kernelDegree_le_branchVertex_degree u
  · exact D.internalVertex_degree_ge_two e i

/-- The local lower bounds already exhaust the global degree sum. -/
theorem BoundedKernelSubdivisionDatum.sum_slotBaseDegree
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    (∑ z : BoundedKernelSubdivisionSlot D.profile, D.slotBaseDegree z) =
      2 * (k + ell) := by
  change
    (∑ z : Fin K.shape.1.val ⊕
        Σ e : Fin K.shape.2.1.val, Fin (D.profile.length e).val,
      match z with
      | .inl u => (boundedKernelFiniteMultiGraph K.shape).degree u
      | .inr _ => 2) = 2 * (k + ell)
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [(boundedKernelFiniteMultiGraph K.shape).sum_degree,
    ← Finset.sum_mul]
  have htotal := D.profile.totalLength
  have hexcess := K.excess
  omega

theorem BoundedKernelSubdivisionDatum.sum_slotDegrees
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K) :
    (∑ z : BoundedKernelSubdivisionSlot D.profile,
      D.reconstructedGraph.degree (D.labels z)) = 2 * (k + ell) := by
  calc
    _ = ∑ x : Fin k, D.reconstructedGraph.degree x :=
      D.labels.sum_comp (fun x ↦ D.reconstructedGraph.degree x)
    _ = 2 * D.reconstructedGraph.edgeFinset.card :=
      D.reconstructedGraph.sum_degrees_eq_twice_card_edges
    _ = 2 * (k + ell) := by rw [D.reconstructedGraph_edgeFinset_card]

/-- Every local degree lower bound is saturated. -/
theorem BoundedKernelSubdivisionDatum.slot_degree_eq_base
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (z : BoundedKernelSubdivisionSlot D.profile) :
    D.reconstructedGraph.degree (D.labels z) = D.slotBaseDegree z := by
  have hsum :
      (∑ z : BoundedKernelSubdivisionSlot D.profile, D.slotBaseDegree z) =
        ∑ z : BoundedKernelSubdivisionSlot D.profile,
          D.reconstructedGraph.degree (D.labels z) := by
    rw [D.sum_slotBaseDegree, D.sum_slotDegrees]
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun z (_ : z ∈
        (Finset.univ : Finset (BoundedKernelSubdivisionSlot D.profile))) ↦
      D.slotBaseDegree_le z)).mp hsum
  exact (heq z (Finset.mem_univ z)).symm

/-- Internal subdivision labels have degree exactly two. -/
theorem BoundedKernelSubdivisionDatum.internalVertex_degree_eq_two
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (e : Fin K.shape.2.1.val)
    (i : Fin (D.profile.length e).val) :
    D.reconstructedGraph.degree (D.pathLabel e i) = 2 := by
  have h := D.slot_degree_eq_base
    (.inr ⟨e, i⟩ : BoundedKernelSubdivisionSlot D.profile)
  change D.reconstructedGraph.degree
    (D.labels (.inr ⟨e, i⟩ : BoundedKernelSubdivisionSlot D.profile)) = 2 at h
  exact h

/-- Branch labels retain their exact kernel multidegree. -/
theorem BoundedKernelSubdivisionDatum.branchVertex_degree_eq_kernelDegree
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (u : Fin K.shape.1.val) :
    D.reconstructedGraph.degree (D.branchLabel u) =
      (boundedKernelFiniteMultiGraph K.shape).degree u := by
  have h := D.slot_degree_eq_base
    (.inl u : BoundedKernelSubdivisionSlot D.profile)
  change D.reconstructedGraph.degree
    (D.labels (.inl u : BoundedKernelSubdivisionSlot D.profile)) =
      (boundedKernelFiniteMultiGraph K.shape).degree u at h
  exact h

/-- A reconstructed vertex has degree two exactly when its original label
comes from an internal path slot. -/
theorem BoundedKernelSubdivisionDatum.degree_eq_two_iff_exists_pathLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (x : Fin k) :
    D.reconstructedGraph.degree x = 2 ↔
      ∃ (e : Fin K.shape.2.1.val) (i : Fin (D.profile.length e).val),
        x = D.pathLabel e i := by
  constructor
  · intro hx
    cases hslot : D.labels.symm x with
    | inl u =>
        have hlabel : D.branchLabel u = x := by
          unfold BoundedKernelSubdivisionDatum.branchLabel
          calc
            D.labels (.inl u) = D.labels (D.labels.symm x) := by rw [hslot]
            _ = x := D.labels.apply_symm_apply x
        have hdegree := D.branchVertex_degree_eq_kernelDegree u
        rw [hlabel, hx] at hdegree
        have hmin := K.minDegree u
        omega
    | inr p =>
        rcases p with ⟨e, i⟩
        refine ⟨e, i, ?_⟩
        unfold BoundedKernelSubdivisionDatum.pathLabel
        calc
          x = D.labels (D.labels.symm x) := (D.labels.apply_symm_apply x).symm
          _ = D.labels (.inr ⟨e, i⟩) := by rw [hslot]
  · rintro ⟨e, i, rfl⟩
    exact D.internalVertex_degree_eq_two e i

/-- Branching vertices of the reconstruction are exactly branch labels. -/
theorem BoundedKernelSubdivisionDatum.mem_branchingVertices_iff_exists_branchLabel
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (D : BoundedKernelSubdivisionDatum k K)
    (x : Fin k) :
    x ∈ branchingVertices D.reconstructedGraph ↔
      ∃ u : Fin K.shape.1.val, x = D.branchLabel u := by
  have hmin := D.reconstructedGraph_minDegree_two
  rw [mem_branchingVertices_iff_degree_ne_two D.reconstructedGraph hmin x]
  constructor
  · intro hx
    cases hslot : D.labels.symm x with
    | inl u =>
        refine ⟨u, ?_⟩
        unfold BoundedKernelSubdivisionDatum.branchLabel
        calc
          x = D.labels (D.labels.symm x) := (D.labels.apply_symm_apply x).symm
          _ = D.labels (.inl u) := by rw [hslot]
    | inr p =>
        rcases p with ⟨e, i⟩
        exfalso
        apply hx
        have hlabel : D.pathLabel e i = x := by
          unfold BoundedKernelSubdivisionDatum.pathLabel
          calc
            D.labels (.inr ⟨e, i⟩) = D.labels (D.labels.symm x) := by rw [hslot]
            _ = x := D.labels.apply_symm_apply x
        rw [← hlabel]
        exact D.internalVertex_degree_eq_two e i
  · rintro ⟨u, rfl⟩ htwo
    rw [D.branchVertex_degree_eq_kernelDegree u] at htwo
    have hminK := K.minDegree u
    omega

end PerronWright.GraphCore
