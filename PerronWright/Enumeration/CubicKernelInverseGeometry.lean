import PerronWright.Enumeration.CubicKernelConnectivity
import PerronWright.Enumeration.CubicKernelValence

/-!
# Exact degree geometry of cubic-kernel subdivisions

This module embeds the literal endpoint occurrences of a cubic multigraph
kernel into the incident edges of its reconstructed simple subdivision.
The resulting branch-degree lower bound, together with the internal
degree-two lower bound and the global handshake identity, is saturated:
every internal subdivision label has degree exactly two, while every branch
label has degree exactly three (equivalently, its original kernel degree).

These results are unconditional consequences of the concrete reconstruction
data.  No inverse classification of actual cores by subdivision data is
assumed here.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Select the first or second normalized endpoint of a kernel edge. -/
def cubicKernelEndpointAt
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) (side : Fin 2) : Fin (2 * ell) :=
  if side.val = 0 then
    (cubicKernelOrderedEndpoints H e).1
  else
    (cubicKernelOrderedEndpoints H e).2

/-- A literal endpoint occurrence.  Thus a loop has two occurrences at its
single endpoint, one for each side. -/
abbrev CubicKernelEndpointOccurrence
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (u : Fin (2 * ell)) :=
  {p : Fin (3 * ell) × Fin 2 // cubicKernelEndpointAt H p.1 p.2 = u}

noncomputable instance cubicKernelEndpointOccurrenceFintype
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (u : Fin (2 * ell)) :
    Fintype (CubicKernelEndpointOccurrence H u) := by
  unfold CubicKernelEndpointOccurrence
  infer_instance

private theorem endpointSide_card_eq_count
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (e : Fin (3 * ell)) (u : Fin (2 * ell)) :
    Fintype.card {side : Fin 2 // cubicKernelEndpointAt H e side = u} =
      (H.endpoints e).toMultiset.count u := by
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  have hc := congrArg
    (fun z : Sym2 (Fin (2 * ell)) ↦ z.toMultiset.count u)
    (cubicKernelOrderedEndpoints_mk H e)
  rw [← hc]
  have hm :
      s((cubicKernelOrderedEndpoints H e).1,
        (cubicKernelOrderedEndpoints H e).2).toMultiset =
        (↑[(cubicKernelOrderedEndpoints H e).1,
          (cubicKernelOrderedEndpoints H e).2] :
          Multiset (Fin (2 * ell))) := rfl
  rw [hm, Multiset.coe_count]
  by_cases ha : (cubicKernelOrderedEndpoints H e).1 = u <;>
    by_cases hb : (cubicKernelOrderedEndpoints H e).2 = u <;>
    simp [cubicKernelEndpointAt, ha, hb]

/-- Endpoint occurrences are counted by the literal multigraph degree. -/
theorem cubicKernelEndpointOccurrence_card
    {ell : ℕ}
    (H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell))
    (u : Fin (2 * ell)) :
    Fintype.card (CubicKernelEndpointOccurrence H u) = H.degree u := by
  let E := Equiv.subtypeProdEquivSigmaSubtype
    (fun (e : Fin (3 * ell)) (side : Fin 2) ↦
      cubicKernelEndpointAt H e side = u)
  calc
    Fintype.card (CubicKernelEndpointOccurrence H u) =
        Fintype.card
          (Σ e : Fin (3 * ell),
            {side : Fin 2 // cubicKernelEndpointAt H e side = u}) :=
      Fintype.card_congr E
    _ = ∑ e : Fin (3 * ell),
          Fintype.card {side : Fin 2 //
            cubicKernelEndpointAt H e side = u} := by rw [Fintype.card_sigma]
    _ = ∑ e : Fin (3 * ell),
          (H.endpoints e).toMultiset.count u := by
      apply Finset.sum_congr rfl
      intro e _
      exact endpointSide_card_eq_count H e u
    _ = H.degree u := by
      unfold PerronWright.FiniteMultiGraph.degree
      apply Finset.sum_congr rfl
      intro e _
      exact (finiteMultiGraph_incidence_eq_count (H.endpoints e) u).symm

/-- The reconstructed edge slot adjacent to an endpoint occurrence. -/
def CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {u : Fin (2 * ell)}
    (p : CubicKernelEndpointOccurrence H u) :
    Σ e : Fin (3 * ell), Fin ((D.profile.length e).val + 1) :=
  if p.1.2.val = 0 then
    ⟨p.1.1, (0 : Fin ((D.profile.length p.1.1).val + 1))⟩
  else
    ⟨p.1.1, Fin.last (D.profile.length p.1.1).val⟩

@[simp]
theorem CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_fst
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {u : Fin (2 * ell)}
    (p : CubicKernelEndpointOccurrence H u) :
    (D.endpointOccurrenceEdgeSlot p).1 = p.1.1 := by
  by_cases h : p.1.2.val = 0
  · unfold CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
    simp only [h]
    rfl
  · unfold CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
    simp only [h]
    rfl

theorem CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_eq_start
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {u : Fin (2 * ell)}
    (p : CubicKernelEndpointOccurrence H u)
    (h : p.1.2.val = 0) :
    D.endpointOccurrenceEdgeSlot p =
      ⟨p.1.1, (0 : Fin ((D.profile.length p.1.1).val + 1))⟩ := by
  unfold CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
  simp only [h, if_pos]

theorem CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_eq_end
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {u : Fin (2 * ell)}
    (p : CubicKernelEndpointOccurrence H u)
    (h : p.1.2.val ≠ 0) :
    D.endpointOccurrenceEdgeSlot p =
      ⟨p.1.1, Fin.last (D.profile.length p.1.1).val⟩ := by
  unfold CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
  simp only [h]
  rfl

/-- Distinct endpoint occurrences give distinct reconstructed edge slots.
For the two sides of a loop this is exactly where `loopLength` is used. -/
theorem CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot_injective
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (u : Fin (2 * ell)) :
    Function.Injective (D.endpointOccurrenceEdgeSlot (u := u)) := by
  rintro ⟨⟨e, i⟩, hi⟩ ⟨⟨f, j⟩, hj⟩ hslot
  have hef : e = f := by
    have h := congrArg Sigma.fst hslot
    have he := D.endpointOccurrenceEdgeSlot_fst
      (⟨⟨e, i⟩, hi⟩ : CubicKernelEndpointOccurrence H u)
    have hf := D.endpointOccurrenceEdgeSlot_fst
      (⟨⟨f, j⟩, hj⟩ : CubicKernelEndpointOccurrence H u)
    change (D.endpointOccurrenceEdgeSlot
      (⟨⟨e, i⟩, hi⟩ : CubicKernelEndpointOccurrence H u)).1 = e at he
    change (D.endpointOccurrenceEdgeSlot
      (⟨⟨f, j⟩, hj⟩ : CubicKernelEndpointOccurrence H u)).1 = f at hf
    calc
      e = (D.endpointOccurrenceEdgeSlot
          (⟨⟨e, i⟩, hi⟩ : CubicKernelEndpointOccurrence H u)).1 :=
        he.symm
      _ = (D.endpointOccurrenceEdgeSlot
          (⟨⟨f, j⟩, hj⟩ : CubicKernelEndpointOccurrence H u)).1 := h
      _ = f := hf
  subst f
  let pi : CubicKernelEndpointOccurrence H u := ⟨⟨e, i⟩, hi⟩
  let pj : CubicKernelEndpointOccurrence H u := ⟨⟨e, j⟩, hj⟩
  have hslot' : D.endpointOccurrenceEdgeSlot pi =
      D.endpointOccurrenceEdgeSlot pj := hslot
  have hij : i = j := by
    by_cases hi0 : i.val = 0
    · by_cases hj0 : j.val = 0
      · apply Fin.ext
        exact hi0.trans hj0.symm
      · exfalso
        have ha : (cubicKernelOrderedEndpoints H e).1 = u := by
          simpa [cubicKernelEndpointAt, hi0] using hi
        have hb : (cubicKernelOrderedEndpoints H e).2 = u := by
          simpa [cubicKernelEndpointAt, hj0] using hj
        have hloop : (H.endpoints e).IsDiag := by
          rw [← cubicKernelOrderedEndpoints_mk H e, Sym2.mk_isDiag_iff]
          exact ha.trans hb.symm
        have hlen := D.profile.loopLength e hloop
        have hpi0 : pi.1.2.val = 0 := by simpa [pi] using hi0
        have hpj0 : pj.1.2.val ≠ 0 := by simpa [pj] using hj0
        have hslotEndpoints :
            (⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ :
              Σ f : Fin (3 * ell),
                Fin ((D.profile.length f).val + 1)) =
            ⟨e, Fin.last (D.profile.length e).val⟩ := by
          calc
            _ = D.endpointOccurrenceEdgeSlot pi :=
              (D.endpointOccurrenceEdgeSlot_eq_start pi hpi0).symm
            _ = D.endpointOccurrenceEdgeSlot pj := hslot'
            _ = _ := D.endpointOccurrenceEdgeSlot_eq_end pj hpj0
        have hv' := congrArg
          (fun q : Σ f : Fin (3 * ell),
              Fin ((D.profile.length f).val + 1) ↦ q.2.val)
          hslotEndpoints
        change 0 = (D.profile.length e).val at hv'
        have hlen0 : (D.profile.length e).val = 0 := by
          exact hv'.symm
        omega
    · by_cases hj0 : j.val = 0
      · exfalso
        have ha : (cubicKernelOrderedEndpoints H e).1 = u := by
          simpa [cubicKernelEndpointAt, hj0] using hj
        have hb : (cubicKernelOrderedEndpoints H e).2 = u := by
          simpa [cubicKernelEndpointAt, hi0] using hi
        have hloop : (H.endpoints e).IsDiag := by
          rw [← cubicKernelOrderedEndpoints_mk H e, Sym2.mk_isDiag_iff]
          exact ha.trans hb.symm
        have hlen := D.profile.loopLength e hloop
        have hpi0 : pi.1.2.val ≠ 0 := by simpa [pi] using hi0
        have hpj0 : pj.1.2.val = 0 := by simpa [pj] using hj0
        have hslotEndpoints :
            (⟨e, Fin.last (D.profile.length e).val⟩ :
              Σ f : Fin (3 * ell),
                Fin ((D.profile.length f).val + 1)) =
            ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩ := by
          calc
            _ = D.endpointOccurrenceEdgeSlot pi :=
              (D.endpointOccurrenceEdgeSlot_eq_end pi hpi0).symm
            _ = D.endpointOccurrenceEdgeSlot pj := hslot'
            _ = _ := D.endpointOccurrenceEdgeSlot_eq_start pj hpj0
        have hv' := congrArg
          (fun q : Σ f : Fin (3 * ell),
              Fin ((D.profile.length f).val + 1) ↦ q.2.val)
          hslotEndpoints
        change (D.profile.length e).val = 0 at hv'
        have hlen0 : (D.profile.length e).val = 0 := by
          exact hv'
        omega
      · apply Fin.ext
        have hii := i.isLt
        have hjj := j.isLt
        omega
  apply Subtype.ext
  exact Prod.ext rfl hij

/-- The branch label occurs in the reconstructed edge selected by an endpoint
occurrence. -/
theorem CubicKernelSubdivisionDatum.branchLabel_mem_occurrenceEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (u : Fin (2 * ell))
    (p : CubicKernelEndpointOccurrence H u) :
    D.branchLabel u ∈ D.subdivisionEdge (D.endpointOccurrenceEdgeSlot p) := by
  rcases p with ⟨⟨e, side⟩, hp⟩
  by_cases hs : side.val = 0
  · have hfirst : (cubicKernelOrderedEndpoints H e).1 = u := by
      simpa [cubicKernelEndpointAt, hs] using hp
    unfold CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
    simp only [hs, if_pos]
    unfold CubicKernelSubdivisionDatum.subdivisionEdge
    change D.branchLabel u ∈
      s(D.pathVertex e (0 : Fin ((D.profile.length e).val + 2)),
        D.pathVertex e (0 : Fin ((D.profile.length e).val + 1)).succ)
    rw [D.pathVertex_zero, hfirst]
    exact Sym2.mem_mk_left _ _
  · have hsecond : (cubicKernelOrderedEndpoints H e).2 = u := by
      simpa [cubicKernelEndpointAt, hs] using hp
    unfold CubicKernelSubdivisionDatum.endpointOccurrenceEdgeSlot
    simp only [hs]
    unfold CubicKernelSubdivisionDatum.subdivisionEdge
    change D.branchLabel u ∈
      s(D.pathVertex e (Fin.last (D.profile.length e).val).castSucc,
        D.pathVertex e (Fin.succ (Fin.last (D.profile.length e).val)))
    rw [D.pathVertex_last, hsecond]
    exact Sym2.mem_mk_right _ _

/-- Endpoint occurrences embed into reconstructed incident edges. -/
noncomputable def CubicKernelSubdivisionDatum.endpointOccurrenceIncidentEdge
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (u : Fin (2 * ell)) :
    CubicKernelEndpointOccurrence H u →
      {z // z ∈ D.reconstructedGraph.incidenceFinset (D.branchLabel u)} :=
  fun p ↦ ⟨D.subdivisionEdge (D.endpointOccurrenceEdgeSlot p), by
    rw [D.reconstructedGraph.incidenceFinset_eq_filter]
    apply Finset.mem_filter.mpr
    refine ⟨?_, D.branchLabel_mem_occurrenceEdge u p⟩
    rw [D.reconstructedGraph_edgeFinset_eq_image']
    exact Finset.mem_image.mpr
      ⟨D.endpointOccurrenceEdgeSlot p, Finset.mem_univ _, rfl⟩⟩

theorem CubicKernelSubdivisionDatum.endpointOccurrenceIncidentEdge_injective
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (u : Fin (2 * ell)) :
    Function.Injective (D.endpointOccurrenceIncidentEdge u) := by
  intro p q hpq
  apply D.endpointOccurrenceEdgeSlot_injective u
  apply D.subdivisionEdge_injective
  exact congrArg Subtype.val hpq

/-- Subdivision does not lower a branch vertex degree. -/
theorem CubicKernelSubdivisionDatum.kernelDegree_le_branchVertex_degree
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (u : Fin (2 * ell)) :
    H.degree u ≤ D.reconstructedGraph.degree (D.branchLabel u) := by
  rw [← cubicKernelEndpointOccurrence_card H u,
    ← D.reconstructedGraph.card_incidenceFinset_eq_degree]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (D.endpointOccurrenceIncidentEdge u)
    (D.endpointOccurrenceIncidentEdge_injective u)

/-- The degree forced at a subdivision slot before the global handshake
identity is used: three at a cubic-kernel vertex and two on an internal
path slot. -/
def CubicKernelSubdivisionDatum.slotBaseDegree
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    CubicKernelSubdivisionSlot D.profile → ℕ
  | .inl _ => 3
  | .inr _ => 2

theorem CubicKernelSubdivisionDatum.slotBaseDegree_le
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (z : CubicKernelSubdivisionSlot D.profile) :
    D.slotBaseDegree z ≤
      D.reconstructedGraph.degree (D.labels z) := by
  rcases z with u | ⟨e, i⟩
  · change 3 ≤ D.reconstructedGraph.degree (D.branchLabel u)
    rw [← K.cubic u]
    exact D.kernelDegree_le_branchVertex_degree u
  · exact D.internalVertex_degree_ge_two e i

/-- The sum of the local lower bounds already exhausts the reconstructed
degree sum. -/
theorem CubicKernelSubdivisionDatum.sum_slotBaseDegree
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    (∑ z : CubicKernelSubdivisionSlot D.profile,
      D.slotBaseDegree z) = 2 * (k + ell) := by
  change
    (∑ z : Fin (2 * ell) ⊕
        Σ e : Fin (3 * ell), Fin (D.profile.length e).val,
      match z with
      | .inl _ => 3
      | .inr _ => 2) = 2 * (k + ell)
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← Finset.sum_mul]
  have htotal := D.profile.totalLength
  omega

theorem CubicKernelSubdivisionDatum.sum_slotDegrees
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H) :
    (∑ z : CubicKernelSubdivisionSlot D.profile,
      D.reconstructedGraph.degree (D.labels z)) = 2 * (k + ell) := by
  calc
    (∑ z : CubicKernelSubdivisionSlot D.profile,
        D.reconstructedGraph.degree (D.labels z)) =
        ∑ x : Fin k, D.reconstructedGraph.degree x :=
      D.labels.sum_comp (fun x ↦ D.reconstructedGraph.degree x)
    _ = 2 * D.reconstructedGraph.edgeFinset.card :=
      D.reconstructedGraph.sum_degrees_eq_twice_card_edges
    _ = 2 * (k + ell) := by
      rw [D.reconstructedGraph_edgeFinset_card_eq]

theorem CubicKernelSubdivisionDatum.slot_degree_eq_base
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (z : CubicKernelSubdivisionSlot D.profile) :
    D.reconstructedGraph.degree (D.labels z) = D.slotBaseDegree z := by
  have hsum :
      (∑ z : CubicKernelSubdivisionSlot D.profile, D.slotBaseDegree z) =
        ∑ z : CubicKernelSubdivisionSlot D.profile,
          D.reconstructedGraph.degree (D.labels z) := by
    rw [D.sum_slotBaseDegree, D.sum_slotDegrees]
  have heq := (Finset.sum_eq_sum_iff_of_le
    (fun z (_ : z ∈
        (Finset.univ : Finset (CubicKernelSubdivisionSlot D.profile))) ↦
      D.slotBaseDegree_le K z)).mp hsum
  exact (heq z (Finset.mem_univ z)).symm

/-- Every internal subdivision label has degree exactly two. -/
theorem CubicKernelSubdivisionDatum.internalVertex_degree_eq_two
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (e : Fin (3 * ell))
    (i : Fin (D.profile.length e).val) :
    D.reconstructedGraph.degree (D.pathLabel e i) = 2 := by
  have h := D.slot_degree_eq_base K
    (.inr ⟨e, i⟩ : CubicKernelSubdivisionSlot D.profile)
  change D.reconstructedGraph.degree
    (D.labels (.inr ⟨e, i⟩ : CubicKernelSubdivisionSlot D.profile)) = 2 at h
  exact h

/-- Every cubic-kernel branch label retains the exact kernel degree. -/
theorem CubicKernelSubdivisionDatum.branchVertex_degree_eq_kernelDegree
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (u : Fin (2 * ell)) :
    D.reconstructedGraph.degree (D.branchLabel u) = K.graph.degree u := by
  have h := D.slot_degree_eq_base K
    (.inl u : CubicKernelSubdivisionSlot D.profile)
  change D.reconstructedGraph.degree
    (D.labels (.inl u : CubicKernelSubdivisionSlot D.profile)) = 3 at h
  rw [K.cubic u]
  exact h

theorem CubicKernelSubdivisionDatum.branchVertex_degree_eq_three
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (u : Fin (2 * ell)) :
    D.reconstructedGraph.degree (D.branchLabel u) = 3 := by
  rw [D.branchVertex_degree_eq_kernelDegree K u, K.cubic u]

/-- A reconstructed vertex has degree two exactly when its original label
comes from an internal slot of one of the subdivided kernel edges. -/
theorem CubicKernelSubdivisionDatum.degree_eq_two_iff_exists_pathLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (x : Fin k) :
    D.reconstructedGraph.degree x = 2 ↔
      ∃ (e : Fin (3 * ell)) (i : Fin (D.profile.length e).val),
        x = D.pathLabel e i := by
  constructor
  · intro hx
    cases hslot : D.labels.symm x with
    | inl u =>
        have hlabel : D.branchLabel u = x := by
          unfold CubicKernelSubdivisionDatum.branchLabel
          calc
            D.labels (.inl u) = D.labels (D.labels.symm x) := by
              rw [hslot]
            _ = x := D.labels.apply_symm_apply x
        have hthree := D.branchVertex_degree_eq_three K u
        rw [hlabel] at hthree
        omega
    | inr p =>
        rcases p with ⟨e, i⟩
        refine ⟨e, i, ?_⟩
        unfold CubicKernelSubdivisionDatum.pathLabel
        calc
          x = D.labels (D.labels.symm x) :=
            (D.labels.apply_symm_apply x).symm
          _ = D.labels (.inr ⟨e, i⟩) := by rw [hslot]
  · rintro ⟨e, i, rfl⟩
    exact D.internalVertex_degree_eq_two K e i

/-- A reconstructed vertex has degree three exactly when its original label
comes from a branch slot of the cubic kernel. -/
theorem CubicKernelSubdivisionDatum.degree_eq_three_iff_exists_branchLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (x : Fin k) :
    D.reconstructedGraph.degree x = 3 ↔
      ∃ u : Fin (2 * ell), x = D.branchLabel u := by
  constructor
  · intro hx
    cases hslot : D.labels.symm x with
    | inl u =>
        refine ⟨u, ?_⟩
        unfold CubicKernelSubdivisionDatum.branchLabel
        calc
          x = D.labels (D.labels.symm x) :=
            (D.labels.apply_symm_apply x).symm
          _ = D.labels (.inl u) := by rw [hslot]
    | inr p =>
        rcases p with ⟨e, i⟩
        have hlabel : D.pathLabel e i = x := by
          unfold CubicKernelSubdivisionDatum.pathLabel
          calc
            D.labels (.inr ⟨e, i⟩) = D.labels (D.labels.symm x) := by
              rw [hslot]
            _ = x := D.labels.apply_symm_apply x
        have htwo := D.internalVertex_degree_eq_two K e i
        rw [hlabel] at htwo
        omega
  · rintro ⟨u, rfl⟩
    exact D.branchVertex_degree_eq_three K u

/-- The branching vertices of a cubic-kernel subdivision are exactly the
original labels assigned to the kernel-vertex slots. -/
theorem CubicKernelSubdivisionDatum.mem_branchingVertices_iff_exists_branchLabel
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph)
    (x : Fin k) :
    x ∈ branchingVertices D.reconstructedGraph ↔
      ∃ u : Fin (2 * ell), x = D.branchLabel u := by
  rw [show x ∈ branchingVertices D.reconstructedGraph ↔
      D.reconstructedGraph.degree x = 3 by
    simp only [branchingVertices, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hx
      cases hslot : D.labels.symm x with
      | inl u =>
          have hlabel : D.branchLabel u = x := by
            unfold CubicKernelSubdivisionDatum.branchLabel
            calc
              D.labels (.inl u) = D.labels (D.labels.symm x) := by
                rw [hslot]
              _ = x := D.labels.apply_symm_apply x
          rw [← hlabel]
          exact D.branchVertex_degree_eq_three K u
      | inr p =>
          rcases p with ⟨e, i⟩
          have hlabel : D.pathLabel e i = x := by
            unfold CubicKernelSubdivisionDatum.pathLabel
            calc
              D.labels (.inr ⟨e, i⟩) = D.labels (D.labels.symm x) := by
                rw [hslot]
              _ = x := D.labels.apply_symm_apply x
          have htwo := D.internalVertex_degree_eq_two K e i
          rw [hlabel] at htwo
          omega
    · intro hx
      omega]
  exact D.degree_eq_three_iff_exists_branchLabel K x


end PerronWright.GraphCore
