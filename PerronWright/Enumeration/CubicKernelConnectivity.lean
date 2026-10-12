import PerronWright.Enumeration.CubicKernelReconstruction
import PerronWright.Enumeration.CubicKernelValence
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Connectivity and minimum degree of cubic-kernel reconstructions

This file proves that subdividing a connected cubic kernel preserves
connectivity and gives every reconstructed vertex degree at least two.  The
terminal interface packages those facts together with the exact edge count
proved in `CubicKernelReconstruction`.
-/

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Every consecutive pair along a reconstructed kernel path is adjacent. -/
theorem CubicKernelSubdivisionDatum.pathEdge_adj_unconditional
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (q : CubicKernelSubdivisionEdgeSlot D) :
    D.reconstructedGraph.Adj
      (D.pathVertex q.1 q.2.castSucc)
      (D.pathVertex q.1 q.2.succ) := by
  apply D.pathEdge_adj q
  intro h
  apply D.pathSlot_castSucc_ne_succ q.1 q.2
  exact (D.pathVertex_eq_iff_pathSlot_eq
    (e := q.1) (f := q.1) (i := q.2.castSucc) (j := q.2.succ)).mp h

/-- The canonical path graph maps to the reconstructed graph along every
subdivided kernel edge. -/
def CubicKernelSubdivisionDatum.pathHom
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    SimpleGraph.pathGraph ((D.profile.length e).val + 2) →g
      D.reconstructedGraph where
  toFun := D.pathVertex e
  map_rel' := by
    intro i j hij
    rw [SimpleGraph.pathGraph_adj] at hij
    rcases hij with hij | hij
    · let q : Fin ((D.profile.length e).val + 1) :=
        ⟨i.val, by have := j.isLt; omega⟩
      have hi : q.castSucc = i := by
        apply Fin.ext
        rfl
      have hj : q.succ = j := by
        apply Fin.ext
        exact hij
      rw [← hi, ← hj]
      exact D.pathEdge_adj_unconditional ⟨e, q⟩
    · let q : Fin ((D.profile.length e).val + 1) :=
        ⟨j.val, by have := i.isLt; omega⟩
      have hj : q.castSucc = j := by
        apply Fin.ext
        rfl
      have hi : q.succ = i := by
        apply Fin.ext
        exact hij
      rw [← hi, ← hj]
      exact (D.pathEdge_adj_unconditional ⟨e, q⟩).symm

/-- Any two positions on one subdivided kernel edge are reachable in the
reconstructed graph. -/
theorem CubicKernelSubdivisionDatum.pathVertex_reachable
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i j : Fin ((D.profile.length e).val + 2)) :
    D.reconstructedGraph.Reachable (D.pathVertex e i) (D.pathVertex e j) := by
  exact (SimpleGraph.pathGraph_preconnected _ i j).map (D.pathHom e)

/-- The labels of the two branch endpoints of every kernel edge remain
reachable after subdivision. -/
theorem CubicKernelSubdivisionDatum.branchEndpoints_reachable
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) :
    D.reconstructedGraph.Reachable
      (D.branchLabel (cubicKernelOrderedEndpoints H e).1)
      (D.branchLabel (cubicKernelOrderedEndpoints H e).2) := by
  have h := D.pathVertex_reachable e
      (0 : Fin ((D.profile.length e).val + 2))
      (Fin.succ (Fin.last (D.profile.length e).val))
  rw [D.pathVertex_zero, D.pathVertex_last] at h
  exact h

/-- Every kernel-support adjacency lifts to reachability of the corresponding
branch labels in the reconstructed graph. -/
theorem CubicKernelSubdivisionDatum.kernelAdj_branchLabel_reachable
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    {u v : Fin (2 * ell)}
    (huv : (finiteMultiGraphSupportGraph H).Adj u v) :
    D.reconstructedGraph.Reachable (D.branchLabel u) (D.branchLabel v) := by
  rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases huv with ⟨⟨e, he⟩, _⟩
  have hord :
      s((cubicKernelOrderedEndpoints H e).1,
        (cubicKernelOrderedEndpoints H e).2) = s(u, v) := by
    rw [cubicKernelOrderedEndpoints_mk]
    exact he
  rcases Sym2.eq_iff.mp hord with h | h
  · simpa [h.1, h.2] using D.branchEndpoints_reachable e
  · simpa [h.1, h.2] using (D.branchEndpoints_reachable e).symm

/-- Connectivity of the kernel connects all reconstructed branch labels. -/
theorem CubicKernelSubdivisionDatum.branchLabels_reachable
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hH : (finiteMultiGraphSupportGraph H).Connected)
    (u v : Fin (2 * ell)) :
    D.reconstructedGraph.Reachable (D.branchLabel u) (D.branchLabel v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  apply (SimpleGraph.reachable_iff_reflTransGen u v).mp (hH u v) |>.lift'
      D.branchLabel
  intro a b hab
  exact (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (D.kernelAdj_branchLabel_reachable hab)

/-- Every subdivision slot is connected to a branch vertex. -/
theorem CubicKernelSubdivisionDatum.slot_reachable_branch
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (z : CubicKernelSubdivisionSlot D.profile) :
    ∃ v : Fin (2 * ell),
      D.reconstructedGraph.Reachable (D.labels z) (D.branchLabel v) := by
  rcases z with v | ⟨e, i⟩
  · exact ⟨v, SimpleGraph.Reachable.rfl⟩
  · refine ⟨(cubicKernelOrderedEndpoints H e).1, ?_⟩
    have h := D.pathVertex_reachable e
      (Fin.succ i.castSucc)
      (0 : Fin ((D.profile.length e).val + 2))
    simpa [CubicKernelSubdivisionDatum.pathVertex_internal,
      CubicKernelSubdivisionDatum.pathVertex_zero,
      CubicKernelSubdivisionDatum.pathLabel] using h

/-- Subdivision of a connected cubic kernel is connected. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_connected
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hH : (finiteMultiGraphSupportGraph H).Connected) :
    D.reconstructedGraph.Connected := by
  let _ : Nonempty (Fin k) := hH.nonempty.map D.branchLabel
  refine ⟨?_⟩
  intro x y
  let zx := D.labels.symm x
  let zy := D.labels.symm y
  obtain ⟨u, hxu⟩ := D.slot_reachable_branch zx
  obtain ⟨v, hyv⟩ := D.slot_reachable_branch zy
  have hx : D.labels zx = x := D.labels.apply_symm_apply x
  have hy : D.labels zy = y := D.labels.apply_symm_apply y
  rw [hx] at hxu
  rw [hy] at hyv
  exact hxu.trans (D.branchLabels_reachable hH u v) |>.trans hyv.symm

/-- Every internal subdivision vertex has two distinct path neighbors. -/
theorem CubicKernelSubdivisionDatum.internalVertex_degree_ge_two
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell))
    (i : Fin (D.profile.length e).val) :
    2 ≤ D.reconstructedGraph.degree (D.pathLabel e i) := by
  let q₀ : CubicKernelSubdivisionEdgeSlot D :=
    ⟨e, ⟨i.val, by have := i.isLt; omega⟩⟩
  let q₁ : CubicKernelSubdivisionEdgeSlot D :=
    ⟨e, ⟨i.val + 1, by have := i.isLt; omega⟩⟩
  let y := D.pathVertex e q₀.2.castSucc
  let z := D.pathVertex e q₁.2.succ
  have h₀center : q₀.2.succ = Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  have h₁center : q₁.2.castSucc = Fin.succ i.castSucc := by
    apply Fin.ext
    rfl
  have hyx : D.reconstructedGraph.Adj y (D.pathLabel e i) := by
    have h := D.pathEdge_adj_unconditional q₀
    rw [h₀center, D.pathVertex_internal] at h
    exact h
  have hxz : D.reconstructedGraph.Adj (D.pathLabel e i) z := by
    have h := D.pathEdge_adj_unconditional q₁
    rw [h₁center, D.pathVertex_internal] at h
    exact h
  have hq : q₀ ≠ q₁ := by
    intro h
    have hval := congrArg (fun q : CubicKernelSubdivisionEdgeSlot D ↦ q.2.val) h
    simp [q₀, q₁] at hval
  have hyz : y ≠ z := by
    intro hyz
    apply hq
    apply D.subdivisionEdge_injective
    have he₀ : D.subdivisionEdge q₀ = s(y, D.pathLabel e i) := by
      unfold CubicKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q₀.2.castSucc,
        D.pathVertex e q₀.2.succ) = _
      rw [h₀center, D.pathVertex_internal]
    have he₁ : D.subdivisionEdge q₁ = s(D.pathLabel e i, z) := by
      unfold CubicKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q₁.2.castSucc,
        D.pathVertex e q₁.2.succ) = _
      rw [h₁center, D.pathVertex_internal]
    rw [he₀, he₁, hyz]
    exact Sym2.eq_swap
  have hcard : 1 < (D.reconstructedGraph.neighborFinset
      (D.pathLabel e i)).card := by
    apply Finset.one_lt_card_iff.mpr
    exact ⟨y, z,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hyx.symm,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hxz, hyz⟩
  rw [D.reconstructedGraph.card_neighborFinset_eq_degree] at hcard
  omega

/-- An occurrence of a branch vertex in a kernel endpoint pair supplies an
actual reconstructed neighbor and remembers the responsible edge slot. -/
theorem CubicKernelSubdivisionDatum.kernelEndpoint_neighbor
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (e : Fin (3 * ell)) (u : Fin (2 * ell))
    (hue : u ∈ H.endpoints e) :
    ∃ (q : CubicKernelSubdivisionEdgeSlot D) (y : Fin k),
      q.1 = e ∧
      D.reconstructedGraph.Adj (D.branchLabel u) y ∧
      D.subdivisionEdge q = s(D.branchLabel u, y) := by
  rw [← cubicKernelOrderedEndpoints_mk H e, Sym2.mem_iff] at hue
  rcases hue with hue | hue
  · let q : CubicKernelSubdivisionEdgeSlot D :=
      ⟨e, (0 : Fin ((D.profile.length e).val + 1))⟩
    let y := D.pathVertex e q.2.succ
    have hstart : D.pathVertex e q.2.castSucc = D.branchLabel u := by
      have hq0 : q.2.castSucc =
          (0 : Fin ((D.profile.length e).val + 2)) := by
        apply Fin.ext
        rfl
      rw [hq0, D.pathVertex_zero, hue]
    refine ⟨q, y, rfl, ?_, ?_⟩
    · rw [← hstart]
      exact D.pathEdge_adj_unconditional q
    · unfold CubicKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q.2.castSucc,
        D.pathVertex e q.2.succ) = _
      rw [hstart]
  · let q : CubicKernelSubdivisionEdgeSlot D :=
      ⟨e, Fin.last (D.profile.length e).val⟩
    let y := D.pathVertex e q.2.castSucc
    have hend : D.pathVertex e q.2.succ = D.branchLabel u := by
      have hqLast : q.2.succ =
          Fin.succ (Fin.last (D.profile.length e).val) := by
        apply Fin.ext
        rfl
      rw [hqLast, D.pathVertex_last, hue]
    refine ⟨q, y, rfl, ?_, ?_⟩
    · rw [← hend]
      exact (D.pathEdge_adj_unconditional q).symm
    · unfold CubicKernelSubdivisionDatum.subdivisionEdge
      change s(D.pathVertex e q.2.castSucc,
        D.pathVertex e q.2.succ) = _
      rw [hend]
      exact Sym2.eq_swap

/-- A branch vertex in a cubic connected kernel has at least two distinct
neighbors after subdivision.  The proof uses one non-loop support edge and
the remaining endpoint incidence forced by cubic valence. -/
theorem CubicKernelSubdivisionDatum.branchVertex_degree_ge_two
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hcubic : ∀ v, H.degree v = 3)
    (hconn : (finiteMultiGraphSupportGraph H).Connected)
    (u : Fin (2 * ell)) :
    2 ≤ D.reconstructedGraph.degree (D.branchLabel u) := by
  have htwo : 2 ≤ 2 * ell := by
    have hu := u.isLt
    omega
  let _ : Nontrivial (Fin (2 * ell)) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_fin]
    omega
  obtain ⟨v, huv⟩ := hconn.preconnected.exists_adj_of_nontrivial u
  rw [finiteMultiGraphSupportGraph, SimpleGraph.fromEdgeSet_adj] at huv
  rcases huv with ⟨⟨e, he⟩, huvne⟩
  have heuv : H.endpoints e = s(u, v) := he
  have hecount : (H.endpoints e).toMultiset.count u = 1 := by
    rw [heuv]
    simp [Sym2.toMultiset, huvne]
  have hsum : ∑ f : Fin (3 * ell),
      (H.endpoints f).toMultiset.count u = 3 := by
    simpa only [PerronWright.FiniteMultiGraph.degree,
      finiteMultiGraph_incidence_eq_count] using hcubic u
  have hrest : ∑ f ∈ (Finset.univ.erase e),
      (H.endpoints f).toMultiset.count u = 2 := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin (3 * ell))))
      (f := fun f ↦ (H.endpoints f).toMultiset.count u)
      (Finset.mem_univ e)
    rw [hecount] at hsplit
    rw [← hsplit] at hsum
    omega
  have hrestNe : (∑ f ∈ (Finset.univ.erase e),
      (H.endpoints f).toMultiset.count u) ≠ 0 := by
    omega
  obtain ⟨f, hfmem, hfcount⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrestNe
  have hfe : f ≠ e := (Finset.mem_erase.mp hfmem).1
  have huf : u ∈ H.endpoints f := by
    rw [← Sym2.mem_toMultiset]
    exact Multiset.count_pos.mp (Nat.pos_of_ne_zero hfcount)
  have hue : u ∈ H.endpoints e := by
    rw [heuv]
    exact Sym2.mem_mk_left u v
  obtain ⟨q, y, hqe, hy, hqy⟩ := D.kernelEndpoint_neighbor e u hue
  obtain ⟨r, z, hrf, hz, hrz⟩ := D.kernelEndpoint_neighbor f u huf
  have hqr : q ≠ r := by
    intro h
    apply hfe
    calc
      f = r.1 := hrf.symm
      _ = q.1 := congrArg Sigma.fst h.symm
      _ = e := hqe
  have hyz : y ≠ z := by
    intro hyz
    apply hqr
    apply D.subdivisionEdge_injective
    rw [hqy, hrz, hyz]
  have hcard : 1 < (D.reconstructedGraph.neighborFinset
      (D.branchLabel u)).card := by
    apply Finset.one_lt_card_iff.mpr
    exact ⟨y, z,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hy,
      (D.reconstructedGraph.mem_neighborFinset _ _).mpr hz, hyz⟩
  rw [D.reconstructedGraph.card_neighborFinset_eq_degree] at hcard
  omega

/-- Every reconstructed vertex has degree at least two. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_minDegree_two
    {k ell : ℕ}
    {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (D : CubicKernelSubdivisionDatum k ell H)
    (hcubic : ∀ v, H.degree v = 3)
    (hconn : (finiteMultiGraphSupportGraph H).Connected) :
    ∀ x, 2 ≤ D.reconstructedGraph.degree x := by
  intro x
  let z := D.labels.symm x
  have hx : D.labels z = x := D.labels.apply_symm_apply x
  rcases z with v | ⟨e, i⟩
  · rw [← hx]
    exact D.branchVertex_degree_ge_two hcubic hconn v
  · rw [← hx]
    exact D.internalVertex_degree_ge_two e i

/-- The three graph-theoretic outputs needed from one subdivision datum,
packaged against the project's connected cubic-kernel structure. -/
theorem CubicKernelSubdivisionDatum.reconstructedGraph_admissible
    {k ell : ℕ}
    (K : LabelledConnectedCubicKernel ell)
    (D : CubicKernelSubdivisionDatum k ell K.graph) :
    D.reconstructedGraph.Connected ∧
      (∀ x, 2 ≤ D.reconstructedGraph.degree x) ∧
      D.reconstructedGraph.edgeFinset.card = k + ell := by
  exact ⟨D.reconstructedGraph_connected K.connected,
    D.reconstructedGraph_minDegree_two K.cubic K.connected,
    D.reconstructedGraph_edgeFinset_card_eq⟩


end PerronWright.GraphCore

