import PerronWright.Enumeration.UnicyclicCore

open scoped Classical
noncomputable section

namespace PerronWright
namespace GraphCore

/-- A connected finite simple graph in which every vertex has degree two is
isomorphic to the standard cycle on the same labelled vertex cardinality. -/
theorem nonempty_cycleGraph_iso_of_connected_forall_degree_eq_two
    {q : ℕ} (H : SimpleGraph (Fin q))
    (hconn : H.Connected) (hdeg : ∀ v, H.degree v = 2) :
    Nonempty (SimpleGraph.cycleGraph q ≃g H) := by
  classical
  have hsumdeg : (∑ v : Fin q, H.degree v) = 2 * q := by
    simp_rw [hdeg]
    simp [mul_comm]
  have hedge_twice : 2 * q = 2 * H.edgeFinset.card := by
    calc
      2 * q = ∑ v : Fin q, H.degree v := hsumdeg.symm
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hedge : H.edgeFinset.card = q := by omega
  have hnotacy : ¬ H.IsAcyclic := by
    intro hacy
    have htree : H.IsTree := ⟨hconn, hacy⟩
    have hcard := htree.card_edgeFinset
    rw [hedge, Fintype.card_fin] at hcard
    omega
  have hcycle : ∃ (v : Fin q) (c : H.Walk v v), c.IsCycle := by
    by_contra h
    apply hnotacy
    intro v c hc
    exact h ⟨v, c, hc⟩
  obtain ⟨v, c, hc⟩ := hcycle
  let n := c.length
  have hn : 3 ≤ n := hc.three_le_length
  have hcontained :
      SimpleGraph.IsContained (SimpleGraph.cycleGraph n) H :=
    (SimpleGraph.cycleGraph_isContained_iff hn).mpr ⟨v, c, hc, rfl⟩
  obtain ⟨f⟩ := hcontained
  have htwo : IsTwoCore H (Set.range f) :=
    isTwoCore_copy_range H (SimpleGraph.cycleGraph n) f
      (cycleGraph_isTwoCore n hn)
  have hrange_deg : ∀ x ∈ Set.range f, H.degree x = 2 := by
    intro x _
    exact hdeg x
  have hclosed :
      ∀ x ∈ Set.range f, ∀ y, H.Adj x y → y ∈ Set.range f :=
    isTwoCore_closed_of_degree_two H htwo hrange_deg
  have hrange_nonempty : (Set.range f).Nonempty := by
    let x : Fin n := ⟨0, by omega⟩
    exact ⟨f x, ⟨x, rfl⟩⟩
  have hrange : Set.range f = Set.univ :=
    closed_nonempty_eq_univ_of_connected H hconn hrange_nonempty hclosed
  have hsurj : Function.Surjective f := by
    intro y
    have hy : y ∈ Set.range f := by rw [hrange]; trivial
    simpa only [Set.mem_range] using hy
  have hreflect : ∀ {x y : Fin n}, H.Adj (f x) (f y) →
      (SimpleGraph.cycleGraph n).Adj x y := by
    intro x y hxy
    have hsource_degree : (SimpleGraph.cycleGraph n).degree x = 2 := by
      have hsource_min : 2 ≤ (SimpleGraph.cycleGraph n).degree x := by
        obtain ⟨a, -, b, -, hab, hxa, hxb⟩ :=
          cycleGraph_isTwoCore n hn x (Set.mem_univ x)
        have hcard : 1 < ((SimpleGraph.cycleGraph n).neighborFinset x).card :=
          Finset.one_lt_card_iff.mpr
            ⟨a, b, by simpa using hxa, by simpa using hxb, hab⟩
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
        omega
      have hsource_max : (SimpleGraph.cycleGraph n).degree x ≤ 2 := by
        calc
          (SimpleGraph.cycleGraph n).degree x ≤ H.degree (f x) := f.degree_le x
          _ = 2 := hdeg (f x)
      omega
    have hneighbor_card :
        Fintype.card ((SimpleGraph.cycleGraph n).neighborSet x) =
          Fintype.card (H.neighborSet (f x)) := by
      rw [SimpleGraph.card_neighborSet_eq_degree,
        SimpleGraph.card_neighborSet_eq_degree, hsource_degree, hdeg]
    have hneighbor_surj : Function.Surjective (f.mapNeighborSet x) :=
      ((Fintype.bijective_iff_injective_and_card (f.mapNeighborSet x)).mpr
        ⟨(f.mapNeighborSet x).injective, hneighbor_card⟩).surjective
    obtain ⟨z, hz⟩ := hneighbor_surj ⟨f y, hxy⟩
    have hfzy : f z.1 = f y := congrArg Subtype.val hz
    have hzy : z.1 = y := f.injective hfzy
    simpa [hzy] using z.2
  let e : SimpleGraph.cycleGraph n ↪g H :=
    { f.toEmbedding with
      map_rel_iff' := fun {x y} ↦
        ⟨hreflect, f.toHom.map_adj⟩ }
  let eIso : SimpleGraph.cycleGraph n ≃g H :=
    RelIso.ofSurjective e hsurj
  have hnq : n = q := by
    simpa only [Fintype.card_fin] using Fintype.card_congr eIso.toEquiv
  let T : ℕ → Type := fun m ↦ SimpleGraph.cycleGraph m ≃g H
  have htype : T n = T q := congrArg T hnq
  exact ⟨_root_.cast htype eIso⟩

/-- The surplus-zero admissibility predicate therefore determines a cycle
graph up to graph isomorphism. -/
theorem nonempty_cycleGraph_iso_of_isAdmissibleAttachmentCore_zero
    {q : ℕ} (H : SimpleGraph (Fin q))
    (hH : IsAdmissibleAttachmentCore q 0 H) :
    Nonempty (SimpleGraph.cycleGraph q ≃g H) := by
  exact nonempty_cycleGraph_iso_of_connected_forall_degree_eq_two H
    ((isAdmissibleAttachmentCore_zero_iff_connected_forall_degree_eq_two H).mp hH).1
    ((isAdmissibleAttachmentCore_zero_iff_connected_forall_degree_eq_two H).mp hH).2

end GraphCore
end PerronWright
