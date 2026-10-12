import PerronWright.Enumeration.CubicConnectedComponentLiteralConstant

/-!
# Relabelling actual connected cubic endpoint tables

Both the degree fibres and the support graph are transported by explicit
equivalences.  Hence the root-component summands depend only on the two
cardinalities of their original label sets.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

variable {V V' E E' : Type*}

def halfEdgeRelabel (ev : V ≃ V') (ee : E ≃ E') (x : E × Bool → V) :
    E' × Bool → V' := fun i ↦ ev (x (ee.symm i.1,i.2))

@[simp] theorem halfEdgeRelabel_apply (ev : V ≃ V') (ee : E ≃ E')
    (x : E × Bool → V) (e : E) (b : Bool) :
    halfEdgeRelabel ev ee x (ee e,b) = ev (x (e,b)) := by
  simp [halfEdgeRelabel]

@[simp] theorem halfEdgeRelabel_symm (ev : V ≃ V') (ee : E ≃ E')
    (x : E × Bool → V) :
    halfEdgeRelabel ev.symm ee.symm (halfEdgeRelabel ev ee x) = x := by
  funext i
  simp [halfEdgeRelabel]

def halfEdgeRelabelFiberEquiv (ev : V ≃ V') (ee : E ≃ E')
    (x : E × Bool → V) (v : V) :
    {i : E × Bool // x i = v} ≃
      {i : E' × Bool // halfEdgeRelabel ev ee x i = ev v} where
  toFun i := ⟨(ee i.val.1,i.val.2),by
    simpa only [halfEdgeRelabel_apply] using congrArg ev i.property⟩
  invFun i := ⟨(ee.symm i.val.1,i.val.2),ev.injective i.property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by apply Subtype.ext; simp

theorem halfEdgeRelabel_degree (ev : V ≃ V') (ee : E ≃ E')
    (x : E × Bool → V) (v : V) :
    Nat.card {i : E' × Bool // halfEdgeRelabel ev ee x i = ev v} =
      Nat.card {i : E × Bool // x i = v} :=
  (Nat.card_congr (halfEdgeRelabelFiberEquiv ev ee x v)).symm

/-- The support graph is the original graph with precisely the vertex
labels transported; the edge relabelling does not change adjacency. -/
def halfEdgeSupportRelabelIso (ev : V ≃ V') (ee : E ≃ E')
    (x : E × Bool → V) :
    labelledHalfEdgeSupport x ≃g labelledHalfEdgeSupport (halfEdgeRelabel ev ee x) where
  toEquiv := ev
  map_rel_iff' := by
    intro u v
    change ((∃ e : E',
        s(halfEdgeRelabel ev ee x (e,false),halfEdgeRelabel ev ee x (e,true)) =
          s(ev u,ev v)) ∧ ev u ≠ ev v) ↔
      ((∃ e : E, s(x (e,false),x (e,true)) = s(u,v)) ∧ u ≠ v)
    constructor
    · rintro ⟨⟨e,he⟩,hne⟩
      refine ⟨⟨ee.symm e,?_⟩,fun h ↦ hne (congrArg ev h)⟩
      simpa only [halfEdgeRelabel,Sym2.map_mk,Equiv.symm_apply_apply] using
        congrArg (Sym2.map ev.symm) he
    · rintro ⟨⟨e,he⟩,hne⟩
      refine ⟨⟨ee e,?_⟩,fun h ↦ hne (ev.injective h)⟩
      simpa only [halfEdgeRelabel_apply,Sym2.map_mk] using
        congrArg (Sym2.map ev) he

def uniformHalfEdgeRelabel [Fintype E] [Fintype E']
    (ev : V ≃ V') (ee : E ≃ E') (d : ℕ)
    (x : UniformHalfEdgeAssignment (E × Bool) V d) :
    UniformHalfEdgeAssignment (E' × Bool) V' d := by
  refine ⟨halfEdgeRelabel ev ee x.val,fun v' ↦ ?_⟩
  obtain ⟨v,rfl⟩ := ev.surjective v'
  rw [halfEdgeRelabel_degree]
  exact x.property v

def uniformHalfEdgeRelabelEquiv [Fintype E] [Fintype E']
    (ev : V ≃ V') (ee : E ≃ E') (d : ℕ) :
    UniformHalfEdgeAssignment (E × Bool) V d ≃
      UniformHalfEdgeAssignment (E' × Bool) V' d where
  toFun := uniformHalfEdgeRelabel ev ee d
  invFun := uniformHalfEdgeRelabel ev.symm ee.symm d
  left_inv x := Subtype.ext (halfEdgeRelabel_symm ev ee x.val)
  right_inv x := Subtype.ext (halfEdgeRelabel_symm ev.symm ee.symm x.val)

def connectedCubicHalfEdgeRelabelEquiv [Fintype E] [Fintype E']
    (ev : V ≃ V') (ee : E ≃ E') :
    ConnectedCubicHalfEdgeTable V E ≃ ConnectedCubicHalfEdgeTable V' E' where
  toFun x := ⟨uniformHalfEdgeRelabel ev ee 3 x.val,
    (halfEdgeSupportRelabelIso ev ee x.val.val).connected_iff.mp x.property⟩
  invFun x := ⟨uniformHalfEdgeRelabel ev.symm ee.symm 3 x.val,
    (halfEdgeSupportRelabelIso ev.symm ee.symm x.val.val).connected_iff.mp x.property⟩
  left_inv x := Subtype.ext (Subtype.ext (halfEdgeRelabel_symm ev ee x.val.val))
  right_inv x := Subtype.ext (Subtype.ext (halfEdgeRelabel_symm ev.symm ee.symm x.val.val))

theorem card_connectedCubicHalfEdgeTable_of_card_eq [Fintype V] [Fintype E]
    {v e : ℕ} (hv : Nat.card V = v) (he : Nat.card E = e) :
    Nat.card (ConnectedCubicHalfEdgeTable V E) =
      Nat.card (ConnectedCubicHalfEdgeTable (Fin v) (Fin e)) :=
  Nat.card_congr (connectedCubicHalfEdgeRelabelEquiv
    (Finite.equivFinOfCardEq hv) (Finite.equivFinOfCardEq he))

theorem card_uniformHalfEdgeAssignment_of_card_eq [Fintype V] [Fintype E]
    {v e d : ℕ} (hv : Nat.card V = v) (he : Nat.card E = e) :
    Nat.card (UniformHalfEdgeAssignment (E × Bool) V d) =
      Nat.card (UniformHalfEdgeAssignment (Fin e × Bool) (Fin v) d) :=
  Nat.card_congr (uniformHalfEdgeRelabelEquiv
    (Finite.equivFinOfCardEq hv) (Finite.equivFinOfCardEq he) d)

end PerronWright.GraphCore
