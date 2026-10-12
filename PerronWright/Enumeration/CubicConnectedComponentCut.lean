import PerronWright.Enumeration.CubicCompensationCoefficient
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Exact labelled half-edge cut decomposition

Both sides retain their original vertex and edge labels.  A cut-supported
endpoint table is equivalent to two independent tables on the two sides;
actual degree fibres are preserved, including the empty complement.
-/

noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

namespace PerronWright.GraphCore

variable {V E : Type*}

/-- The simple support of a genuine labelled half-edge table. -/
def labelledHalfEdgeSupport (x : E × Bool → V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (Set.range (fun e : E ↦ s(x (e,false), x (e,true))))

/-- No labelled edge crosses the specified vertex and edge cut. -/
abbrev CutHalfEdgeTable (A : Set V) (B : Set E) :=
  {x : E × Bool → V // ∀ e b, x (e,b) ∈ A ↔ e ∈ B}

/-- Two tables retaining the original labels in the cut and its complement. -/
abbrev CutHalfEdgePair (A : Set V) (B : Set E) :=
  (B × Bool → A) × ((Bᶜ : Set E) × Bool → (Aᶜ : Set V))

def cutTableInside {A : Set V} {B : Set E} (x : CutHalfEdgeTable A B) :
    B × Bool → A :=
  fun i ↦ ⟨x.val (i.1.val,i.2), (x.property _ _).2 i.1.property⟩

def cutTableOutside {A : Set V} {B : Set E} (x : CutHalfEdgeTable A B) :
    (Bᶜ : Set E) × Bool → (Aᶜ : Set V) :=
  fun i ↦ ⟨x.val (i.1.val,i.2), fun h ↦ i.1.property ((x.property _ _).1 h)⟩

def assembleCutHalfEdges {A : Set V} {B : Set E} (p : CutHalfEdgePair A B) :
    E × Bool → V :=
  fun i ↦ if h : i.1 ∈ B then (p.1 (⟨i.1,h⟩,i.2)).val
    else (p.2 (⟨i.1,h⟩,i.2)).val

theorem assembleCutHalfEdges_supported {A : Set V} {B : Set E}
    (p : CutHalfEdgePair A B) :
    ∀ e b, assembleCutHalfEdges p (e,b) ∈ A ↔ e ∈ B := by
  intro e b
  by_cases h : e ∈ B
  · simp only [assembleCutHalfEdges, h, iff_true]
    exact (p.1 (⟨e,h⟩,b)).property
  · simp only [assembleCutHalfEdges, h, iff_false]
    exact (p.2 (⟨e,h⟩,b)).property

def assembledCutTable {A : Set V} {B : Set E} (p : CutHalfEdgePair A B) :
    CutHalfEdgeTable A B :=
  ⟨assembleCutHalfEdges p, assembleCutHalfEdges_supported p⟩

/-- Literal split/reassembly equivalence, with no cardinality or
connectivity conclusion supplied as an input. -/
def cutHalfEdgeTableEquivPair (A : Set V) (B : Set E) :
    CutHalfEdgeTable A B ≃ CutHalfEdgePair A B where
  toFun x := (cutTableInside x, cutTableOutside x)
  invFun := assembledCutTable
  left_inv x := by
    apply Subtype.ext
    funext i
    change assembleCutHalfEdges (cutTableInside x,cutTableOutside x) i = x.val i
    unfold assembleCutHalfEdges
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      simp only [cutTableInside, assembledCutTable, assembleCutHalfEdges,
        dif_pos i.1.property]
    · funext i
      apply Subtype.ext
      simp only [cutTableOutside, assembledCutTable, assembleCutHalfEdges,
        dif_neg i.1.property]

/-- An incidence at an inside vertex necessarily has an inside edge label. -/
def cutInsideDegreeFiberEquiv {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (v : A) :
    {i : B × Bool // cutTableInside x i = v} ≃
      {i : E × Bool // x.val i = v.val} where
  toFun i := ⟨(i.val.1.val,i.val.2), congrArg Subtype.val i.property⟩
  invFun i :=
    ⟨(⟨i.val.1, (x.property i.val.1 i.val.2).1 (by rw [i.property]; exact v.property)⟩,i.val.2),
      Subtype.ext i.property⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

def cutOutsideDegreeFiberEquiv {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (v : (Aᶜ : Set V)) :
    {i : (Bᶜ : Set E) × Bool // cutTableOutside x i = v} ≃
      {i : E × Bool // x.val i = v.val} where
  toFun i := ⟨(i.val.1.val,i.val.2), congrArg Subtype.val i.property⟩
  invFun i :=
    ⟨(⟨i.val.1, fun h ↦ v.property (by rw [← i.property]; exact (x.property _ _).2 h)⟩,i.val.2),
      Subtype.ext i.property⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

theorem cutTableInside_degree {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (v : A) :
    Nat.card {i : B × Bool // cutTableInside x i = v} =
      Nat.card {i : E × Bool // x.val i = v.val} :=
  Nat.card_congr (cutInsideDegreeFiberEquiv x v)

theorem cutTableOutside_degree {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (v : (Aᶜ : Set V)) :
    Nat.card {i : (Bᶜ : Set E) × Bool // cutTableOutside x i = v} =
      Nat.card {i : E × Bool // x.val i = v.val} :=
  Nat.card_congr (cutOutsideDegreeFiberEquiv x v)

theorem cutTable_uniform_degree_iff {A : Set V} {B : Set E}
    (x : CutHalfEdgeTable A B) (d : ℕ) :
    (∀ v : V, Nat.card {i : E × Bool // x.val i = v} = d) ↔
      (∀ v : A, Nat.card {i : B × Bool // cutTableInside x i = v} = d) ∧
      (∀ v : (Aᶜ : Set V), Nat.card {i : (Bᶜ : Set E) × Bool // cutTableOutside x i = v} = d) := by
  simp only [cutTableInside_degree, cutTableOutside_degree]
  constructor
  · intro h
    exact ⟨fun v ↦ h v.val, fun v ↦ h v.val⟩
  · intro h v
    by_cases hv : v ∈ A
    · exact h.1 ⟨v,hv⟩
    · exact h.2 ⟨v,hv⟩

end PerronWright.GraphCore
