import PerronWright.Enumeration.RootedForestTransfer
import PerronWright.Enumeration.CoreInvariant

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical in
/-- The surviving `Fin n` labels are equivalent to the literal
complement of the deleted label. -/
def survivorEquiv {n : ℕ} (v : Fin (n + 1)) :
    Fin n ≃ ({v}ᶜ : Set (Fin (n + 1))) :=
  Equiv.ofBijective
    (fun j : Fin n => (⟨v.succAbove j, by simp⟩ : ({v}ᶜ : Set (Fin (n + 1)))))
    ⟨by
      intro i j h
      exact Fin.succAbove_right_injective (congrArg Subtype.val h),
     by
      intro x
      have hx : x.val ≠ v := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hx
      exact ⟨j, Subtype.ext hj⟩⟩

open scoped Classical in
theorem connected_comap_succAbove_of_leaf
    {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) (hconn : H.Connected)
    (hv : H.degree v = 1) :
    (H.comap v.succAbove).Connected := by
  have hconn' : (H.induce ({v}ᶜ : Set (Fin (n + 1)))).Connected :=
    hconn.induce_compl_singleton_of_degree_eq_one hv
  have hiso := SimpleGraph.Iso.comap (survivorEquiv v)
    (H.induce ({v}ᶜ : Set (Fin (n + 1))))
  have hsource := hiso.connected_iff.mpr hconn'
  exact hsource

/-- A two-neighbor certificate is invariant under relabelling by an
equivalence. -/
theorem isTwoCore_image_equiv
    {A B : Type*} (e : A ≃ B) (G : SimpleGraph B)
    {s : Set A} (hs : IsTwoCore (G.comap e) s) :
    IsTwoCore G (e '' s) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨w, hw, z, hz, hwz, hxw, hxz⟩ := hs x hx
  exact ⟨e w, ⟨w, hw, rfl⟩, e z, ⟨z, hz, rfl⟩,
    (fun h => hwz (e.injective h)), hxw, hxz⟩

theorem isTwoCore_preimage_equiv
    {A B : Type*} (e : A ≃ B) (G : SimpleGraph B)
    {s : Set B} (hs : IsTwoCore G s) :
    IsTwoCore (G.comap e) (e ⁻¹' s) := by
  intro x hx
  obtain ⟨w, hw, z, hz, hwz, hxw, hxz⟩ := hs (e x) hx
  refine ⟨e.symm w, ?_, e.symm z, ?_, ?_, ?_, ?_⟩
  · simpa using hw
  · simpa using hz
  · exact fun h => hwz (e.symm.injective h)
  · simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using hxw
  · simpa only [SimpleGraph.comap_adj, e.apply_symm_apply] using hxz

open scoped Classical in
theorem greatestTwoCore_image_equiv
    {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (G : SimpleGraph B) [DecidableRel G.Adj] :
    e '' greatestTwoCore (G.comap e) = greatestTwoCore G := by
  apply Set.Subset.antisymm
  · exact isTwoCore_subset_greatest G
      (isTwoCore_image_equiv e G (isTwoCore_greatest _))
  · intro y hy
    have hpre : IsTwoCore (G.comap e) (e ⁻¹' greatestTwoCore G) :=
      isTwoCore_preimage_equiv e G (isTwoCore_greatest G)
    have hx : e.symm y ∈ greatestTwoCore (G.comap e) :=
      isTwoCore_subset_greatest _ hpre (by simpa using hy)
    exact ⟨e.symm y, hx, e.apply_symm_apply y⟩

open scoped Classical in
/-- The greatest 2-core is unchanged by one labelled leaf deletion,
with the surviving `Fin n` labels embedded back into `Fin (n+1)`. -/
theorem greatestTwoCore_comap_succAbove_leaf
    {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) (hv : H.degree v = 1) :
    v.succAbove '' greatestTwoCore (H.comap v.succAbove) =
      greatestTwoCore H := by
  let e := survivorEquiv v
  have he :
      e '' greatestTwoCore (H.comap v.succAbove) =
        greatestTwoCore (H.induce ({v}ᶜ : Set (Fin (n + 1)))) := by
    exact greatestTwoCore_image_equiv e (H.induce ({v}ᶜ : Set (Fin (n + 1))))
  calc
    v.succAbove '' greatestTwoCore (H.comap v.succAbove) =
        Subtype.val '' (e '' greatestTwoCore (H.comap v.succAbove)) := by
      rw [Set.image_image]
      rfl
    _ = Subtype.val '' greatestTwoCore
          (H.induce ({v}ᶜ : Set (Fin (n + 1)))) := by rw [he]
    _ = greatestTwoCore H := greatestTwoCore_prune_leaf H hv

open scoped Classical in
/-- Core invariance along an arbitrary finite sequence of valid leaf
deletions, with the precise composite map back to original labels. -/
theorem LeafPruning.greatestTwoCore_terminal_image
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) :
    p.terminalLabels '' greatestTwoCore p.terminalGraph =
      greatestTwoCore G := by
  induction p with
  | done G hstop =>
      simp only [terminalLabels, terminalGraph]
      exact Set.image_id _
  | step H v j hv hvw tail ih =>
      change (tail.terminalLabels.trans v.succAboveEmb) ''
          greatestTwoCore tail.terminalGraph = greatestTwoCore H
      calc
        (tail.terminalLabels.trans v.succAboveEmb) ''
            greatestTwoCore tail.terminalGraph =
            v.succAbove ''
              (tail.terminalLabels '' greatestTwoCore tail.terminalGraph) := by
                rw [Set.image_image]
                rfl
        _ = v.succAbove '' greatestTwoCore (H.comap v.succAbove) := by
          rw [ih]
        _ = greatestTwoCore H := greatestTwoCore_comap_succAbove_leaf H v hv

open scoped Classical in
theorem LeafPruning.terminal_connected
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) (hconn : G.Connected) :
    p.terminalGraph.Connected := by
  induction p with
  | done G hstop => exact hconn
  | step H v j hv hvw tail ih =>
      exact ih (connected_comap_succAbove_of_leaf H v hconn hv)

open scoped Classical in
theorem LeafPruning.terminal_core_nonempty
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G)
    (hcore : (greatestTwoCore G).Nonempty) :
    (greatestTwoCore p.terminalGraph).Nonempty := by
  obtain ⟨x, hx⟩ := hcore
  rw [← p.greatestTwoCore_terminal_image] at hx
  obtain ⟨y, hy, _⟩ := hx
  exact ⟨y, hy⟩

open scoped Classical in
/-- In a connected graph containing a nonempty 2-core, the absence of
degree-one vertices forces every vertex into that core. -/
theorem greatestTwoCore_eq_univ_of_connected_noLeaf
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hcore : (greatestTwoCore G).Nonempty)
    (hno : ¬∃ v : V, G.degree v = 1) :
    greatestTwoCore G = Set.univ := by
  obtain ⟨x, hx⟩ := hcore
  obtain ⟨w, _, z, _, hwz, hxw, hxz⟩ := isTwoCore_greatest G x hx
  have hdeg : ∀ v : V, 2 ≤ G.degree v := by
    intro v
    have hpos : 0 < G.degree v := by
      by_cases hvx : v = x
      · subst v
        exact hxw.degree_pos_left
      · exact (hconn v x).degree_pos_left hvx
    have hne : G.degree v ≠ 1 := fun hd => hno ⟨v, hd⟩
    omega
  have htwo : IsTwoCore G Set.univ := by
    intro v _
    have hcard : 1 < (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact lt_of_lt_of_le (by norm_num : 1 < 2) (hdeg v)
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcard
    exact ⟨a, Set.mem_univ a, b, Set.mem_univ b, hab,
      (G.mem_neighborFinset v a).mp ha, (G.mem_neighborFinset v b).mp hb⟩
  exact Set.eq_univ_of_forall
    (fun v => isTwoCore_subset_greatest G htwo (Set.mem_univ v))

open scoped Classical in
/-- For a connected graph of positive paper surplus, the original
labels that survive any maximal degree-one pruning sequence are exactly
the vertices of its canonical greatest 2-core. -/
theorem LeafPruning.terminalLabels_range_eq_greatestTwoCore
    {k : ℕ} {G : SimpleGraph (Fin k)}
    (p : LeafPruning k G) (hconn : G.Connected)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    Set.range p.terminalLabels = greatestTwoCore G := by
  have hbase : (greatestTwoCore G).Nonempty :=
    greatestTwoCore_nonempty_of_positive_surplus G hconn hell hs
  have hterm : (greatestTwoCore p.terminalGraph).Nonempty :=
    p.terminal_core_nonempty hbase
  have hfull : greatestTwoCore p.terminalGraph = Set.univ :=
    greatestTwoCore_eq_univ_of_connected_noLeaf p.terminalGraph
      (p.terminal_connected hconn) hterm p.terminal_noLeaf
  calc
    Set.range p.terminalLabels =
        p.terminalLabels '' Set.univ := (Set.image_univ).symm
    _ = p.terminalLabels '' greatestTwoCore p.terminalGraph := by
      rw [hfull]
    _ = greatestTwoCore G := p.greatestTwoCore_terminal_image

open scoped Classical in
/-- In particular, the automatically constructed finite algorithm
returns precisely the induced greatest 2-core on its surviving labels. -/
theorem pruneAll_terminalLabels_range_eq_greatestTwoCore
    {k : ℕ} (G : SimpleGraph (Fin k)) (hconn : G.Connected)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    Set.range (LeafPruning.pruneAll k G).terminalLabels =
      greatestTwoCore G :=
  (LeafPruning.pruneAll k G).terminalLabels_range_eq_greatestTwoCore
    hconn hell hs

open scoped Classical in
/-- The terminal labelled graph is exactly a relabelling of the
canonical greatest 2-core: its original-label image is the core, and
its edges are the original edges induced on those labels. -/
theorem pruneAll_terminal_is_greatestTwoCore
    {k : ℕ} (G : SimpleGraph (Fin k)) (hconn : G.Connected)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    Set.range (LeafPruning.pruneAll k G).terminalLabels =
        greatestTwoCore G ∧
      (LeafPruning.pruneAll k G).terminalGraph =
        G.comap (LeafPruning.pruneAll k G).terminalLabels := by
  exact ⟨pruneAll_terminalLabels_range_eq_greatestTwoCore G hconn hell hs,
    (LeafPruning.pruneAll k G).terminalGraph_eq_comap⟩

#print axioms PerronWright.GraphCore.greatestTwoCore_comap_succAbove_leaf
#print axioms PerronWright.GraphCore.LeafPruning.greatestTwoCore_terminal_image
#print axioms PerronWright.GraphCore.LeafPruning.terminalLabels_range_eq_greatestTwoCore
#print axioms PerronWright.GraphCore.pruneAll_terminalLabels_range_eq_greatestTwoCore
#print axioms PerronWright.GraphCore.pruneAll_terminal_is_greatestTwoCore

end PerronWright.GraphCore

