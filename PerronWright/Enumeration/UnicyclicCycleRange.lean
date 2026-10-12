import PerronWright.Enumeration.UnicyclicCycleIso
import PerronWright.Enumeration.UnicyclicCycleMultiplicity
import Mathlib.GroupTheory.Perm.Fin

/-!
# Exact range of the orientation-forgetting map

This file identifies the range of full cyclic permutations with the labelled
connected two-regular simple graphs, and hence with the admissible
surplus-zero attachment cores.
-/

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore
namespace FullCyclePerm

/-- The standard positive orientation of the cycle on `Fin q`. -/
def standardCyclePerm (q : ℕ) (hq : 2 ≤ q) : FullCyclePerm q :=
  ⟨finRotate q, cycleType_finRotate_of_le hq⟩

/-- Forgetting the orientation of `finRotate` gives the standard cycle graph. -/
theorem graph_standardCyclePerm {q : ℕ} (hq : 3 ≤ q) :
    graph (standardCyclePerm q (by omega)) = SimpleGraph.cycleGraph q := by
  let _ : NeZero q := ⟨by omega⟩
  ext x y
  rw [graph_adj_iff, SimpleGraph.cycleGraph_adj']
  change (finRotate q x = y ∨ finRotate q y = x) ↔ _
  rw [finRotate_apply, finRotate_apply]
  have hone : ((1 : Fin q) : ℕ) = 1 := by
    change 1 % q = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hxy : (x - y).val = 1 ↔ x - y = (1 : Fin q) := by
    rw [Fin.ext_iff]
    rw [hone]
  have hyx : (y - x).val = 1 ↔ y - x = (1 : Fin q) := by
    rw [Fin.ext_iff]
    rw [hone]
  rw [hxy, hyx]
  simp only [sub_eq_iff_eq_add']
  aesop

/-- Relabel a full cyclic permutation by conjugation. -/
def conjugate {q : ℕ} (e : Equiv.Perm (Fin q))
    (σ : FullCyclePerm q) : FullCyclePerm q :=
  ⟨e * σ.1 * e⁻¹, by
    simpa only [Equiv.Perm.cycleType_conj] using σ.2⟩

@[simp]
theorem coe_conjugate {q : ℕ} (e : Equiv.Perm (Fin q))
    (σ : FullCyclePerm q) :
    (conjugate e σ).1 = e * σ.1 * e⁻¹ := rfl

/-- Conjugating an oriented cycle only relabels its underlying graph. -/
def graphIsoConjugate {q : ℕ} (e : Equiv.Perm (Fin q))
    (σ : FullCyclePerm q) : graph σ ≃g graph (conjugate e σ) where
  __ := e
  map_rel_iff' := by
    intro x y
    rw [graph_adj_iff, graph_adj_iff]
    change
      ((e * σ.1 * e⁻¹) (e x) = e y ∨
        (e * σ.1 * e⁻¹) (e y) = e x) ↔
        (σ.1 x = y ∨ σ.1 y = x)
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
      e.symm_apply_apply, e.injective.eq_iff]

theorem graph_conjugate_eq_of_iso {q : ℕ} {H : SimpleGraph (Fin q)}
    (σ : FullCyclePerm q) (e : graph σ ≃g H) :
    graph (conjugate e.toEquiv σ) = H := by
  ext x y
  obtain ⟨x, rfl⟩ := e.toEquiv.surjective x
  obtain ⟨y, rfl⟩ := e.toEquiv.surjective y
  exact (graphIsoConjugate e.toEquiv σ).map_rel_iff.trans
    e.map_rel_iff.symm

/-- The standard oriented cycle, with its orientation forgotten, is graph
isomorphic to `cycleGraph`. -/
def graphStandardIsoCycleGraph {q : ℕ} (hq : 3 ≤ q) :
    graph (standardCyclePerm q (by omega)) ≃g SimpleGraph.cycleGraph q := by
  rw [graph_standardCyclePerm hq]

/-- Every full cyclic permutation gives a labelled copy of the standard
cycle graph. -/
theorem nonempty_cycleGraph_iso_graph {q : ℕ} (hq : 3 ≤ q)
    (σ : FullCyclePerm q) :
    Nonempty (SimpleGraph.cycleGraph q ≃g graph σ) := by
  let σ₀ := standardCyclePerm q (by omega)
  have htype : σ₀.1.cycleType = σ.1.cycleType := by
    rw [σ₀.2, σ.2]
  obtain ⟨e, he⟩ := isConj_iff.mp
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr htype)
  have hconj : conjugate e σ₀ = σ := by
    apply Subtype.ext
    exact he
  let e₁ : graph σ₀ ≃g graph σ := by
    simpa only [hconj] using graphIsoConjugate e σ₀
  exact ⟨(graphStandardIsoCycleGraph hq).symm.trans e₁⟩

theorem cycleGraph_connected_of_three_le {q : ℕ} (hq : 3 ≤ q) :
    (SimpleGraph.cycleGraph q).Connected := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hq
  exact SimpleGraph.cycleGraph_connected

theorem cycleGraph_degree_eq_two_of_three_le {q : ℕ} (hq : 3 ≤ q)
    (v : Fin q) :
    (SimpleGraph.cycleGraph q).degree v = 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hq
  exact SimpleGraph.cycleGraph_degree_three_le

/-- The unoriented graph of a full cycle is connected and two-regular. -/
theorem graph_connected_and_forall_degree_eq_two {q : ℕ} (hq : 3 ≤ q)
    (σ : FullCyclePerm q) :
    (graph σ).Connected ∧ ∀ v, (graph σ).degree v = 2 := by
  obtain ⟨e⟩ := nonempty_cycleGraph_iso_graph hq σ
  constructor
  · exact e.connected_iff.mp (cycleGraph_connected_of_three_le hq)
  · intro v
    obtain ⟨x, rfl⟩ := e.toEquiv.surjective v
    exact (e.degree_eq x).trans (cycleGraph_degree_eq_two_of_three_le hq x)

/-- Every connected two-regular labelled graph is obtained by forgetting the
orientation of a full cyclic permutation. -/
theorem exists_graph_eq_of_connected_forall_degree_eq_two
    {q : ℕ} (hq : 3 ≤ q) (H : SimpleGraph (Fin q))
    (hconn : H.Connected) (hdeg : ∀ v, H.degree v = 2) :
    ∃ σ : FullCyclePerm q, graph σ = H := by
  obtain ⟨e⟩ :=
    nonempty_cycleGraph_iso_of_connected_forall_degree_eq_two H hconn hdeg
  let σ₀ := standardCyclePerm q (by omega)
  let e₀ : graph σ₀ ≃g H :=
    (graphStandardIsoCycleGraph hq).trans e
  exact ⟨conjugate e₀.toEquiv σ₀, graph_conjugate_eq_of_iso σ₀ e₀⟩

/-- Exact membership characterization of the orientation-forgetting range. -/
theorem mem_graphRange_iff_connected_forall_degree_eq_two
    {q : ℕ} (hq : 3 ≤ q) (H : SimpleGraph (Fin q)) :
    H ∈ graphRange q ↔ H.Connected ∧ ∀ v, H.degree v = 2 := by
  constructor
  · intro hH
    rcases Finset.mem_image.mp hH with ⟨σ, -, rfl⟩
    exact graph_connected_and_forall_degree_eq_two hq σ
  · rintro ⟨hconn, hdeg⟩
    obtain ⟨σ, hσ⟩ :=
      exists_graph_eq_of_connected_forall_degree_eq_two hq H hconn hdeg
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩

/-- The finite collection of connected two-regular labelled graphs. -/
def connectedTwoRegularGraphs (q : ℕ) : Finset (SimpleGraph (Fin q)) := by
  classical
  exact Finset.univ.filter fun H ↦ H.Connected ∧ ∀ v, H.degree v = 2

theorem graphRange_eq_connectedTwoRegularGraphs {q : ℕ} (hq : 3 ≤ q) :
    graphRange q = connectedTwoRegularGraphs q := by
  ext H
  simp only [connectedTwoRegularGraphs, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact mem_graphRange_iff_connected_forall_degree_eq_two hq H

theorem mem_graphRange_iff_isAdmissibleAttachmentCore_zero
    {q : ℕ} (hq : 3 ≤ q) (H : SimpleGraph (Fin q)) :
    H ∈ graphRange q ↔ IsAdmissibleAttachmentCore q 0 H :=
  (mem_graphRange_iff_connected_forall_degree_eq_two hq H).trans
    (isAdmissibleAttachmentCore_zero_iff_connected_forall_degree_eq_two H).symm

/-- The orientation-forgetting range is exactly the full admissible
surplus-zero core family. -/
theorem graphRange_eq_admissibleAttachmentCores_zero
    {q : ℕ} (hq : 3 ≤ q) :
    graphRange q = admissibleAttachmentCores q 0 := by
  ext H
  rw [mem_admissibleAttachmentCores]
  exact mem_graphRange_iff_isAdmissibleAttachmentCore_zero hq H

end FullCyclePerm
end GraphCore
end PerronWright
