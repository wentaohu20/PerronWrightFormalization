import PerronWright.Enumeration.CoreTerminal
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- Vertices that remain after degree-two paths are suppressed. -/
def branchingVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => 3 ≤ G.degree v)

/-- In a finite 2-core, the total degree above two is exactly twice
the graph surplus.  This is the arithmetic source of the finite cubic
kernel bound. -/
theorem degree_excess_eq_two_surplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {ell : ℕ}
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    (∑ v : V, (G.degree v - 2)) = 2 * ell := by
  have hsum : (∑ v : V, G.degree v) =
      (∑ v : V, (G.degree v - 2)) + 2 * Fintype.card V := by
    calc
      (∑ v : V, G.degree v) = ∑ v : V, ((G.degree v - 2) + 2) := by
        apply Finset.sum_congr rfl
        intro v _
        have hv := hmin v
        omega
      _ = (∑ v : V, (G.degree v - 2)) + 2 * Fintype.card V := by
        simp [Finset.sum_add_distrib, Finset.sum_const, mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges, hs] at hsum
  omega

/-- Every branch vertex consumes at least one unit of the `2 ell`
degree budget; hence fixed positive surplus has finitely many branch
vertices independent of the number of subdividing degree-two vertices. -/
theorem branchingVertices_card_le_two_surplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {ell : ℕ}
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    (branchingVertices G).card ≤ 2 * ell := by
  have hbound : (branchingVertices G).card ≤
      ∑ v : V, (G.degree v - 2) := by
    unfold branchingVertices
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro v _
    split_ifs with h
    · omega
    · omega
  exact hbound.trans (le_of_eq (degree_excess_eq_two_surplus G hmin hs))

/-- Degree-two subdivision vertices consume none of the exact degree
surplus; all `2 ell` units live on the branch set. -/
theorem branchingVertices_degree_excess_eq_two_surplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {ell : ℕ}
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    (∑ v ∈ branchingVertices G, (G.degree v - 2)) = 2 * ell := by
  rw [← degree_excess_eq_two_surplus G hmin hs]
  unfold branchingVertices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with h
  · rfl
  · have hv := hmin v
    omega

/-- Saturation of the branch-vertex budget means every branch vertex
has degree exactly three, matching the cubic-kernel extremal case. -/
theorem branchingVertices_card_eq_two_surplus_iff_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) {ell : ℕ}
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    (branchingVertices G).card = 2 * ell ↔
      ∀ v ∈ branchingVertices G, G.degree v = 3 := by
  let B := branchingVertices G
  have hsum : (∑ v ∈ B, (G.degree v - 2)) = 2 * ell :=
    branchingVertices_degree_excess_eq_two_surplus G hmin hs
  have hle : ∀ v ∈ B, 1 ≤ G.degree v - 2 := by
    intro v hv
    have hv' : 3 ≤ G.degree v := by
      simpa only [B, branchingVertices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hv
    omega
  constructor
  · intro hcard v hv
    change B.card = 2 * ell at hcard
    have hsum_eq : (∑ v ∈ B, (1 : ℕ)) =
        ∑ v ∈ B, (G.degree v - 2) := by
      calc
        (∑ v ∈ B, (1 : ℕ)) = B.card := by simp
        _ = ∑ v ∈ B, (G.degree v - 2) := hcard.trans hsum.symm
    have heq := (Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq
    have hv'' := heq v hv
    have hvmin := hmin v
    omega
  · intro hcubic
    change B.card = 2 * ell
    have hsum' : (∑ v ∈ B, (G.degree v - 2)) = B.card := by
      calc
        (∑ v ∈ B, (G.degree v - 2)) = ∑ _v ∈ B, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hcubic v hv]
        _ = B.card := by simp
    exact hsum'.symm.trans hsum

open scoped Classical in
/-- The labelled deletion used by `LeafPruning` removes exactly one
edge when its removed vertex is a leaf. -/
theorem leaf_comap_succAbove_edge_count
    {n : ℕ} (H : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) (hv : H.degree v = 1) :
    (H.comap v.succAbove).edgeFinset.card + 1 = H.edgeFinset.card := by
  let e := survivorEquiv v
  have hcard : (H.comap v.succAbove).edgeFinset.card =
      (H.induce ({v}ᶜ : Set (Fin (n + 1)))).edgeFinset.card := by
    exact (SimpleGraph.Iso.comap e
      (H.induce ({v}ᶜ : Set (Fin (n + 1))))).card_edgeFinset_eq
  rw [hcard]
  exact leaf_prune_edge_count H hv

open scoped Classical in
/-- Surplus is unchanged throughout an arbitrary finite sequence of
valid leaf deletions, now stated on the terminal graph's actual `Fin`
labels. -/
theorem LeafPruning.terminal_surplus
    {k : ℕ} {G : SimpleGraph (Fin k)} (p : LeafPruning k G)
    {ell : ℕ}
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + ell) :
    p.terminalGraph.edgeFinset.card + 1 =
      Fintype.card (Fin p.terminalCount) + ell := by
  induction p with
  | done G hstop => exact hs
  | step H v j hv hvw tail ih =>
      have he := leaf_comap_succAbove_edge_count H v hv
      simp only [Fintype.card_fin] at hs
      rw [← he] at hs
      apply ih
      simp only [Fintype.card_fin]
      clear ih
      apply Nat.add_right_cancel (m := 1)
      exact hs.trans (by omega)

open scoped Classical in
/-- A full induced 2-core has minimum degree two. -/
theorem min_degree_two_of_greatestTwoCore_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfull : greatestTwoCore G = Set.univ) :
    ∀ v, 2 ≤ G.degree v := by
  intro v
  have hv : v ∈ greatestTwoCore G := by rw [hfull]; trivial
  obtain ⟨w, _, z, _, hwz, hvw, hvz⟩ := isTwoCore_greatest G v hv
  have hcard : 1 < (G.neighborFinset v).card :=
    Finset.one_lt_card_iff.mpr
      ⟨w, z, (G.mem_neighborFinset v w).mpr hvw,
        (G.mem_neighborFinset v z).mpr hvz, hwz⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  omega

open scoped Classical in
/-- The actual graph produced by maximal leaf pruning is a 2-core
whose branch-vertex count is bounded solely by positive surplus. -/
theorem pruneAll_branchingVertices_card_le_two_surplus
    {k : ℕ} (G : SimpleGraph (Fin k)) (hconn : G.Connected)
    {ell : ℕ}
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1)) :
    (branchingVertices (LeafPruning.pruneAll k G).terminalGraph).card ≤
      2 * ell := by
  let p := LeafPruning.pruneAll k G
  have hcore : (greatestTwoCore G).Nonempty :=
    greatestTwoCore_nonempty_of_positive_surplus G hconn (by omega) hs
  have hterm : (greatestTwoCore p.terminalGraph).Nonempty :=
    p.terminal_core_nonempty hcore
  have hfull : greatestTwoCore p.terminalGraph = Set.univ :=
    greatestTwoCore_eq_univ_of_connected_noLeaf p.terminalGraph
      (p.terminal_connected hconn) hterm p.terminal_noLeaf
  have hmin := min_degree_two_of_greatestTwoCore_eq_univ p.terminalGraph hfull
  have hs' := p.terminal_surplus hs
  have hs'' : p.terminalGraph.edgeFinset.card =
      Fintype.card (Fin p.terminalCount) + ell := by omega
  exact branchingVertices_card_le_two_surplus p.terminalGraph hmin hs''

open scoped Classical in
theorem LeafPruning.terminalCount_le
    {k : ℕ} {G : SimpleGraph (Fin k)} (p : LeafPruning k G) :
    p.terminalCount ≤ k := by
  induction p with
  | done G hstop => exact le_refl _
  | step H v j hv hvw tail ih => exact ih.trans (Nat.le_succ _)

/-- A finite index for all possible labelled terminal 2-core shapes at
one original graph size. -/
def CoreIndex (k : ℕ) :=
  Σ m : Fin (k + 1), SimpleGraph (Fin m.val)

instance (k : ℕ) : Fintype (CoreIndex k) := by
  unfold CoreIndex
  infer_instance

open scoped Classical in
/-- The exact finite 2-core shape selected by the deterministic leaf
pruning algorithm. -/
def coreIndex {k : ℕ} (G : SimpleGraph (Fin k)) : CoreIndex k :=
  let p := LeafPruning.pruneAll k G
  ⟨⟨p.terminalCount, Nat.lt_succ_of_le p.terminalCount_le⟩, p.terminalGraph⟩

open scoped Classical in
/-- Every fixed-surplus graph contributes to an index with connected
minimum-degree-two core, exact surplus, and at most `2 ell` branch
vertices. -/
theorem coreIndex_admissible
    {k : ℕ} (G : SimpleGraph (Fin k)) (hconn : G.Connected)
    {ell : ℕ}
    (hs : G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1)) :
    (coreIndex G).2.Connected ∧
    (∀ v, 2 ≤ (coreIndex G).2.degree v) ∧
    (coreIndex G).2.edgeFinset.card = (coreIndex G).1.val + ell ∧
    (branchingVertices (coreIndex G).2).card ≤ 2 * ell := by
  let p := LeafPruning.pruneAll k G
  have hcore : (greatestTwoCore G).Nonempty :=
    greatestTwoCore_nonempty_of_positive_surplus G hconn (by omega) hs
  have hterm : (greatestTwoCore p.terminalGraph).Nonempty :=
    p.terminal_core_nonempty hcore
  have hfull : greatestTwoCore p.terminalGraph = Set.univ :=
    greatestTwoCore_eq_univ_of_connected_noLeaf p.terminalGraph
      (p.terminal_connected hconn) hterm p.terminal_noLeaf
  have hmin := min_degree_two_of_greatestTwoCore_eq_univ p.terminalGraph hfull
  have hs' := p.terminal_surplus hs
  have hs'' : p.terminalGraph.edgeFinset.card = p.terminalCount + ell := by
    apply Nat.add_right_cancel (m := 1)
    simpa only [Fintype.card_fin, Nat.add_assoc] using hs'
  change p.terminalGraph.Connected ∧
    (∀ v, 2 ≤ p.terminalGraph.degree v) ∧
    p.terminalGraph.edgeFinset.card = p.terminalCount + ell ∧
    (branchingVertices p.terminalGraph).card ≤ 2 * ell
  exact ⟨p.terminal_connected hconn, hmin, hs'',
    branchingVertices_card_le_two_surplus p.terminalGraph hmin (by
      simpa only [Fintype.card_fin] using hs'')⟩

open scoped Classical in
def fixedSurplusGraphs (k ell : ℕ) : Finset (SimpleGraph (Fin k)) :=
  Finset.univ.filter (fun G => G.Connected ∧
    G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1))

open scoped Classical in
/-- The literal fixed-surplus `connectedWeight` is the sum over the
finite set of connected labelled graphs with that exact edge count. -/
theorem connectedWeight_eq_sum_fixedSurplusGraphs
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) :
    M.connectedWeight t k (ell + 1) =
      ∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight t G := by
  classical
  unfold CompactBJRModel.connectedWeight fixedSurplusGraphs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro G _
  have heq : G.edgeFinset.card = k + (ell + 1) - 1 ↔
      G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1) := by
    simp only [Fintype.card_fin]
    omega
  simp only [heq]

open scoped Classical in
/-- The finite collection of possible 2-core indices at fixed size and
surplus, restricted to the exact graph-theoretic constraints proved
above. -/
def admissibleCoreIndices (k ell : ℕ) : Finset (CoreIndex k) :=
  Finset.univ.filter (fun I => I.2.Connected ∧
    (∀ v, 2 ≤ I.2.degree v) ∧
    I.2.edgeFinset.card = I.1.val + ell ∧
    (branchingVertices I.2).card ≤ 2 * ell)

open scoped Classical in
/-- The original annealed fixed-surplus connected-graph sum decomposes
exactly by its labelled 2-core shape.  All attached tree vertices are
integrated into continuous marks on that core; only indices with at most
`2 ell` branch vertices appear.  This is a finite equality, prior to
subdivision of degree-two paths and cubic-kernel asymptotics. -/
theorem connectedWeight_eq_admissible_core_fibers
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (k ell : ℕ) :
    M.connectedWeight t k (ell + 1) =
      ∑ I ∈ admissibleCoreIndices k ell,
        ∑ G ∈ (fixedSurplusGraphs k ell).filter (fun G => coreIndex G = I),
          markedGraphWeight M t (LeafPruning.pruneAll k G).terminalGraph
            ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1)) := by
  classical
  rw [connectedWeight_eq_sum_fixedSurplusGraphs M t k ell]
  have hsupport : ∀ G ∈ fixedSurplusGraphs k ell,
      coreIndex G ∈ admissibleCoreIndices k ell := by
    intro G hG
    have hG' : G.Connected ∧
        G.edgeFinset.card + 1 = Fintype.card (Fin k) + (ell + 1) := by
      simpa only [fixedSurplusGraphs, Finset.mem_filter, Finset.mem_univ, true_and] using hG
    simpa only [admissibleCoreIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] using coreIndex_admissible G hG'.1 hG'.2
  calc
    (∑ G ∈ fixedSurplusGraphs k ell, M.graphWeight t G) =
        ∑ G ∈ fixedSurplusGraphs k ell,
          markedGraphWeight M t (LeafPruning.pruneAll k G).terminalGraph
            ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1)) := by
      apply Finset.sum_congr rfl
      intro G _
      exact graphWeight_pruneAll M t G
    _ = ∑ I ∈ admissibleCoreIndices k ell,
          ∑ G ∈ (fixedSurplusGraphs k ell).filter (fun G => coreIndex G = I),
            markedGraphWeight M t (LeafPruning.pruneAll k G).terminalGraph
              ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1)) := by
      symm
      have heq : (fixedSurplusGraphs k ell).filter
          (fun G => coreIndex G ∈ admissibleCoreIndices k ell) =
          fixedSurplusGraphs k ell := Finset.filter_eq_self.mpr hsupport
      have hpartition := Finset.sum_fiberwise_eq_sum_filter
        (fixedSurplusGraphs k ell) (admissibleCoreIndices k ell) coreIndex
        (fun G => markedGraphWeight M t
          (LeafPruning.pruneAll k G).terminalGraph
          ((LeafPruning.pruneAll k G).terminalMarks M t (fun _ => 1)))
      simpa only [heq] using hpartition

#print axioms PerronWright.GraphCore.degree_excess_eq_two_surplus
#print axioms PerronWright.GraphCore.branchingVertices_card_le_two_surplus
#print axioms PerronWright.GraphCore.branchingVertices_card_eq_two_surplus_iff_cubic
#print axioms PerronWright.GraphCore.leaf_comap_succAbove_edge_count
#print axioms PerronWright.GraphCore.LeafPruning.terminal_surplus
#print axioms PerronWright.GraphCore.pruneAll_branchingVertices_card_le_two_surplus
#print axioms PerronWright.GraphCore.coreIndex_admissible
#print axioms PerronWright.GraphCore.connectedWeight_eq_admissible_core_fibers

end PerronWright.GraphCore

