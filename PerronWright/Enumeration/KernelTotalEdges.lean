import PerronWright.Enumeration.KernelEdgeCount

noncomputable section

namespace PerronWright.GraphCore

open scoped Classical

/-- The cardinality of the *actual* edge-labelled suppressed kernel
is the number of degree-two path components plus the original direct
branch-to-branch edges. -/
theorem kernelEdgeLabel_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : (G.induce {v | G.degree v = 2}).IsAcyclic) :
    Nat.card (KernelEdgeLabel G) =
      (Fintype.card {v : V | G.degree v = 2} -
        (G.induce {v | G.degree v = 2}).edgeFinset.card) +
      (directBranchEdges G).card := by
  rw [KernelEdgeLabel, Nat.card_sum,
    degreeTwo_components_eq_eulerDeficit G hacyc]
  exact congrArg _
    (Nat.subtype_card (directBranchEdges G) (fun e => Iff.rfl))

set_option linter.style.haveILetI false in
/-- Direct kernel edges are exactly the edges of the branch-induced
simple graph.  Their original labels are retained individually. -/
theorem directBranchEdges_card_eq_induced
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (directBranchEdges G).card =
      (G.induce (branchingVertices G : Set V)).edgeFinset.card := by
  have hset : directBranchEdges G =
      G.edgeFinset ∩ (branchingVertices G).sym2 := by
    ext e
    simp only [directBranchEdges, Finset.mem_filter, Finset.mem_inter,
      Finset.mem_sym2_iff]
  rw [hset]
  letI : Fintype (branchingVertices G : Set V) :=
    FinsetCoe.fintype (branchingVertices G)
  have hmap := G.map_edgeFinset_induce
    (s := (branchingVertices G : Set V))
  have hcard := congrArg Finset.card hmap
  convert hcard.symm using 1 <;>
    simp only [Finset.toFinset_coe, Finset.card_map]
  congr 1
  ext e
  simp only [SimpleGraph.mem_edgeFinset]

/-- Double-counting the actual crossing incidences of two finite
vertex sets, with no graph quotient or weighting assumptions. -/
theorem crossing_incidence_double_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : Finset V) :
    (∑ x ∈ s, ((G.neighborFinset x).filter (· ∈ t)).card) =
      ∑ y ∈ t, ((G.neighborFinset y).filter (· ∈ s)).card := by
  have hcount (A B : Finset V) (x : V) :
      ((G.neighborFinset x).filter (· ∈ B)).card =
        ∑ y ∈ B, if G.Adj x y then (1 : ℕ) else 0 := by
    have hfilter : (G.neighborFinset x).filter (· ∈ B) =
        B.filter (G.Adj x) := by
      ext y
      simp [G.mem_neighborFinset, and_comm]
    rw [hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ x ∈ s, ∑ y ∈ t,
          if G.Adj x y then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact hcount s t x
    _ = ∑ y ∈ t, ∑ x ∈ s,
          if G.Adj y x then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxy : G.Adj x y
      · simp [hxy, hxy.symm]
      · have hyx : ¬G.Adj y x := fun h => hxy h.symm
        simp [hxy, hyx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      exact (hcount t s y).symm

/-- On a minimum-degree-two graph, the branch set is precisely the
complement of the degree-two vertices. -/
theorem mem_branchingVertices_iff_degree_ne_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) (v : V) :
    v ∈ branchingVertices G ↔ G.degree v ≠ 2 := by
  simp only [branchingVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  have hv := hmin v
  omega

set_option linter.style.haveILetI false in
/-- The stubs counted from the degree-two side equal the same actual
crossing incidences counted from the branch side. -/
theorem degreeTwoBoundaryIncidences_eq_branch_crossing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) :
    degreeTwoBoundaryIncidences G =
      ∑ b ∈ branchingVertices G,
        ((G.neighborFinset b).filter (fun v => G.degree v = 2)).card := by
  let D : Finset V := Finset.univ.filter (fun v => G.degree v = 2)
  let B := branchingVertices G
  have hD (v : V) : v ∈ D ↔ G.degree v = 2 := by simp [D]
  have hB (v : V) : v ∈ B ↔ G.degree v ≠ 2 :=
    mem_branchingVertices_iff_degree_ne_two G hmin v
  letI : Fintype {v : V | G.degree v = 2} := Fintype.ofFinite _
  calc
    degreeTwoBoundaryIncidences G =
        ∑ d ∈ D,
          ((G.neighborFinset d).filter (fun y => G.degree y ≠ 2)).card := by
      have hsub := (Finset.sum_subtype
        (F := Fintype.ofFinite {v : V | G.degree v = 2}) D hD
        (fun d => ((G.neighborFinset d).filter
          (fun y => G.degree y ≠ 2)).card)).symm
      unfold degreeTwoBoundaryIncidences
      convert hsub using 1
      congr 1
      ext x
      simp
    _ = ∑ d ∈ D,
          ((G.neighborFinset d).filter (· ∈ B)).card := by
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      ext y
      simp only [Finset.mem_filter, hB]
    _ = ∑ b ∈ B,
          ((G.neighborFinset b).filter (· ∈ D)).card :=
      crossing_incidence_double_count G D B
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ext v
      simp only [Finset.mem_filter, hD]

set_option linter.style.haveILetI false in
/-- Internal branch incidences count each direct branch edge twice. -/
theorem branch_internal_incidence_eq_twice_direct
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ b ∈ branchingVertices G,
      ((G.neighborFinset b).filter (· ∈ branchingVertices G)).card) =
      2 * (directBranchEdges G).card := by
  let B := branchingVertices G
  let H := G.induce (B : Set V)
  have hin (b : (B : Set V)) : H.degree b =
      ((G.neighborFinset b.val).filter (· ∈ B)).card := by
    calc
      H.degree b = (H.neighborFinset b).card :=
        (H.card_neighborFinset_eq_degree b).symm
      _ = ((H.neighborFinset b).map (.subtype (· ∈ (B : Set V)))).card :=
        (Finset.card_map _).symm
      _ = (G.neighborFinset b.val ∩ (B : Set V).toFinset).card := by
        congr 1
        ext v
        simp [H, SimpleGraph.mem_neighborFinset]
      _ = ((G.neighborFinset b.val).filter (· ∈ B)).card := by
        congr 1
        ext v
        simp [B]
  have hsub := Finset.sum_subtype (F := FinsetCoe.fintype B) B
    (fun v => Iff.rfl)
    (fun b => ((G.neighborFinset b).filter (· ∈ B)).card)
  calc
    (∑ b ∈ branchingVertices G,
        ((G.neighborFinset b).filter (· ∈ branchingVertices G)).card) =
        ∑ b : (B : Set V),
          ((G.neighborFinset b.val).filter (· ∈ B)).card := by
      convert hsub using 1
    _ = ∑ b : (B : Set V), H.degree b := by
      apply Finset.sum_congr rfl
      intro b _
      exact (hin b).symm
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = 2 * (directBranchEdges G).card := by
      rw [directBranchEdges_card_eq_induced]

/-- The total branch degree is the direct-edge incidence count plus
the degree-two boundary incidence count. -/
theorem branch_degree_eq_direct_and_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 2 ≤ G.degree v) :
    (∑ b ∈ branchingVertices G, G.degree b) =
      2 * (directBranchEdges G).card +
        degreeTwoBoundaryIncidences G := by
  let B := branchingVertices G
  have hB (v : V) : v ∈ B ↔ G.degree v ≠ 2 :=
    mem_branchingVertices_iff_degree_ne_two G hmin v
  have hsplit (b : V) : G.degree b =
      ((G.neighborFinset b).filter (· ∈ B)).card +
        ((G.neighborFinset b).filter (fun v => G.degree v = 2)).card := by
    have hnot : (G.neighborFinset b).filter (· ∉ B) =
        (G.neighborFinset b).filter (fun v => G.degree v = 2) := by
      ext v
      simp only [Finset.mem_filter, hB]
      tauto
    calc
      G.degree b = (G.neighborFinset b).card :=
        (G.card_neighborFinset_eq_degree b).symm
      _ = ((G.neighborFinset b).filter (· ∈ B)).card +
          ((G.neighborFinset b).filter (· ∉ B)).card := by
            exact ((G.neighborFinset b).card_filter_add_card_filter_not (· ∈ B)).symm
      _ = _ := by rw [hnot]
  calc
    (∑ b ∈ branchingVertices G, G.degree b) =
        ∑ b ∈ B,
          (((G.neighborFinset b).filter (· ∈ B)).card +
            ((G.neighborFinset b).filter (fun v => G.degree v = 2)).card) := by
      apply Finset.sum_congr rfl
      intro b _
      exact hsplit b
    _ = (∑ b ∈ B, ((G.neighborFinset b).filter (· ∈ B)).card) +
          (∑ b ∈ B, ((G.neighborFinset b).filter
            (fun v => G.degree v = 2)).card) := by
      rw [Finset.sum_add_distrib]
    _ = 2 * (directBranchEdges G).card +
          degreeTwoBoundaryIncidences G := by
      rw [branch_internal_incidence_eq_twice_direct,
        degreeTwoBoundaryIncidences_eq_branch_crossing G hmin]

set_option maxHeartbeats 800000 in
/-- A connected positive-surplus core has exactly `|B| + ell`
labelled kernel edges after every degree-two path is suppressed. -/
theorem kernelEdgeLabel_card_eq_branching_add_surplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    Nat.card (KernelEdgeLabel G) =
      (branchingVertices G).card + ell := by
  let B := branchingVertices G
  let D := {v : V | G.degree v = 2}
  let H := G.induce D
  have hacyc : H.IsAcyclic := degreeTwo_induced_isAcyclic G hconn hmin hell hs
  have hdegree : (∑ b ∈ B, G.degree b) =
      2 * B.card + 2 * ell := by
    have hexcess : (∑ b ∈ B, (G.degree b - 2)) = 2 * ell := by
      simpa only [B] using
        (branchingVertices_degree_excess_eq_two_surplus G hmin hs)
    have hsplit : (∑ b ∈ B, (G.degree b - 2)) + 2 * B.card =
        ∑ b ∈ B, G.degree b := by
      calc
        _ = (∑ b ∈ B, (G.degree b - 2)) +
            (∑ _b ∈ B, (2 : ℕ)) := by
          simp [Finset.sum_const, mul_comm]
        _ = ∑ b ∈ B, ((G.degree b - 2) + 2) := by
          rw [Finset.sum_add_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro b _
          have hb := hmin b
          omega
    omega
  have hinc : (∑ b ∈ B, G.degree b) =
      2 * (directBranchEdges G).card +
        degreeTwoBoundaryIncidences G :=
    branch_degree_eq_direct_and_boundary G hmin
  have hboundary : degreeTwoBoundaryIncidences G =
      2 * (Fintype.card D - H.edgeFinset.card) :=
    degreeTwoBoundaryIncidences_eq_twice_eulerDeficit G
  have hcount : (directBranchEdges G).card +
      (Fintype.card D - H.edgeFinset.card) = B.card + ell := by
    omega
  rw [kernelEdgeLabel_card G hacyc]
  change (Fintype.card D - H.edgeFinset.card) +
    (directBranchEdges G).card = B.card + ell
  omega

/-- At surplus `ell`, an actual labelled suppressed kernel has at most
`3 ell` edge labels, independently of the number of degree-two vertices. -/
theorem kernelEdgeLabel_card_le_three_surplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    Nat.card (KernelEdgeLabel G) ≤ 3 * ell := by
  rw [kernelEdgeLabel_card_eq_branching_add_surplus G hconn hmin hell hs]
  have hb := branchingVertices_card_le_two_surplus G hmin hs
  omega

/-- The maximal labelled edge count is attained precisely when the
suppressed kernel is cubic on all branch vertices. -/
theorem kernelEdgeLabel_card_eq_three_surplus_iff_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    {ell : ℕ} (hell : 0 < ell)
    (hs : G.edgeFinset.card = Fintype.card V + ell) :
    Nat.card (KernelEdgeLabel G) = 3 * ell ↔
      ∀ v ∈ branchingVertices G, G.degree v = 3 := by
  rw [kernelEdgeLabel_card_eq_branching_add_surplus G hconn hmin hell hs]
  have hcubic := branchingVertices_card_eq_two_surplus_iff_cubic G hmin hs
  constructor
  · intro h
    apply hcubic.mp
    omega
  · intro h
    have hc := hcubic.mpr h
    omega

#print axioms PerronWright.GraphCore.kernelEdgeLabel_card
#print axioms PerronWright.GraphCore.directBranchEdges_card_eq_induced
#print axioms PerronWright.GraphCore.crossing_incidence_double_count
#print axioms PerronWright.GraphCore.degreeTwoBoundaryIncidences_eq_branch_crossing
#print axioms PerronWright.GraphCore.branch_internal_incidence_eq_twice_direct
#print axioms PerronWright.GraphCore.branch_degree_eq_direct_and_boundary
#print axioms PerronWright.GraphCore.kernelEdgeLabel_card_eq_branching_add_surplus
#print axioms PerronWright.GraphCore.kernelEdgeLabel_card_le_three_surplus
#print axioms PerronWright.GraphCore.kernelEdgeLabel_card_eq_three_surplus_iff_cubic

end PerronWright.GraphCore
