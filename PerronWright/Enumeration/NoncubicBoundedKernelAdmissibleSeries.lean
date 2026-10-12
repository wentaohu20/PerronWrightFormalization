import PerronWright.Enumeration.VariableKernelSubdivisionData
import PerronWright.Enumeration.BoundedKernelPathGeneratingSeries
import PerronWright.Enumeration.CubicForbiddenCorrectionBridge

/-!
# Literal all-length series for one bounded noncubic kernel

This file stays deliberately at the kernel/length-profile layer.  For one
fixed bounded edge-labelled kernel it proves that

* the existing subdivision profiles are exactly the finite antidiagonals
  satisfying the genuine loop and zero-parallel-edge restrictions;
* the literal all-length admissible series is the unrestricted marked-path
  resolvent product minus a finite inclusion--exclusion correction; and
* if the kernel has strictly fewer than `3 * ell` suppressed edges, cubic
  normalization leaves one explicit fold coordinate times a jointly
  analytic remainder.

No claim is made here about the fibre from actual labelled cores to bounded
kernel presentations.  That separate finite combinatorial classification is
needed before the result below can be promoted to the total noncubic graph
series.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

namespace NBKAS_MPR

export PerronWright.MarkedPathResolvent (profile pathResolventKernel)

end NBKAS_MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## Literal admissible length profiles -/

/-- The two genuine simplicity restrictions on an unrestricted internal
length assignment for a variable-valence bounded kernel. -/
def BoundedKernelLengthAssignment.IsAdmissible
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (l : Fin K.shape.2.1.val →₀ ℕ) : Prop :=
  (∀ e, (K.shape.2.2 e).IsDiag → 2 ≤ l e) ∧
    Function.Injective
      (fun e : {e : Fin K.shape.2.1.val // l e = 0} ↦ K.shape.2.2 e.1)

/-- The finite antidiagonal of total internal length `d`, restricted by the
actual loop lower bound and direct-edge injectivity condition. -/
abbrev BoundedKernelAdmissibleLengthAntidiagonal
    (d : ℕ) {ell : ℕ} (K : LabelledBoundedKernel ell) :=
  {l : (Finset.univ.finsuppAntidiag d :
      Finset (Fin K.shape.2.1.val →₀ ℕ)) //
    BoundedKernelLengthAssignment.IsAdmissible K l.1}

/-- Forget the finite codomain bound in an actual bounded-kernel length
profile. -/
def BoundedKernelLengthProfile.toFinsupp
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K) :
    Fin K.shape.2.1.val →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun e ↦ (L.length e).val)

@[simp] theorem BoundedKernelLengthProfile.toFinsupp_apply
    {k ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile k K) (e : Fin K.shape.2.1.val) :
    L.toFinsupp e = (L.length e).val :=
  rfl

private theorem BoundedKernelLengthProfile.toFinsupp_mem_antidiagonal
    {d ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile (K.shape.1.val + d) K) :
    L.toFinsupp ∈ (Finset.univ.finsuppAntidiag d :
      Finset (Fin K.shape.2.1.val →₀ ℕ)) := by
  rw [Finset.mem_finsuppAntidiag]
  constructor
  · have hsum : ∑ e, (L.length e).val = d := by
      have htotal := L.totalLength
      omega
    calc
      Finset.univ.sum ⇑L.toFinsupp =
          ∑ e : Fin K.shape.2.1.val, (L.length e).val := by
        apply Finset.sum_congr rfl
        intro e _
        exact BoundedKernelLengthProfile.toFinsupp_apply L e
      _ = d := hsum
  · exact Finset.subset_univ _

theorem BoundedKernelLengthProfile.toFinsupp_admissible
    {d ell : ℕ} {K : LabelledBoundedKernel ell}
    (L : BoundedKernelLengthProfile (K.shape.1.val + d) K) :
    BoundedKernelLengthAssignment.IsAdmissible K L.toFinsupp := by
  constructor
  · intro e he
    simpa only [BoundedKernelLengthProfile.toFinsupp_apply] using
      L.loopLength e he
  · intro e f hef
    let e' : {a : Fin K.shape.2.1.val // (L.length a).val = 0} :=
      ⟨e.1, by simpa only [BoundedKernelLengthProfile.toFinsupp_apply] using e.2⟩
    let f' : {a : Fin K.shape.2.1.val // (L.length a).val = 0} :=
      ⟨f.1, by simpa only [BoundedKernelLengthProfile.toFinsupp_apply] using f.2⟩
    have hef' : K.shape.2.2 e'.1 = K.shape.2.2 f'.1 := by
      simpa only [e', f'] using hef
    have heq := L.directEndpointsInjective hef'
    exact Subtype.ext (congrArg Subtype.val heq)

/-- An actual profile on `nv + d` vertices is exactly an admissible length
assignment of total internal length `d`. -/
def boundedKernelLengthProfileEquivAdmissibleAntidiagonal
    (d : ℕ) {ell : ℕ} (K : LabelledBoundedKernel ell) :
    BoundedKernelLengthProfile (K.shape.1.val + d) K ≃
      BoundedKernelAdmissibleLengthAntidiagonal d K where
  toFun L :=
    ⟨⟨L.toFinsupp, L.toFinsupp_mem_antidiagonal⟩,
      L.toFinsupp_admissible⟩
  invFun A := by
    let l : Fin K.shape.2.1.val →₀ ℕ := A.1.1
    have hsum : ∑ e, l e = d :=
      (Finset.mem_finsuppAntidiag.mp A.1.2).1
    have hle (e : Fin K.shape.2.1.val) : l e ≤ d := by
      rw [← hsum]
      exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (l i))
        (Finset.mem_univ e)
    exact
      { length := fun e ↦
          ⟨l e, by
            have := hle e
            omega⟩
        totalLength := by
          simpa only using congrArg (fun n ↦ K.shape.1.val + n) hsum
        loopLength := by
          intro e he
          exact A.2.1 e he
        directEndpointsInjective := A.2.2 }
  left_inv L := by
    cases L with
    | mk length totalLength loopLength directEndpointsInjective =>
        congr 1
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro e
    rfl

/-- Literal fixed-total-length admissible coefficient, written using the
existing subdivision-profile type (and hence its actual lower bounds). -/
def boundedKernelAdmissiblePathCoefficient
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) (d : ℕ) : ℂ :=
  letI := boundedKernelLengthProfileFintype
    (K.shape.1.val + d) K
  ∑ L : BoundedKernelLengthProfile (K.shape.1.val + d) K,
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M tau
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2)
        (L.length e).val

theorem boundedKernelAdmissiblePathCoefficient_eq_antidiagonal
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) (d : ℕ) :
    boundedKernelAdmissiblePathCoefficient M tau K x d =
      ∑ A : BoundedKernelAdmissibleLengthAntidiagonal d K,
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M tau
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (A.1.1 e) := by
  classical
  let _ := boundedKernelLengthProfileFintype
    (K.shape.1.val + d) K
  unfold boundedKernelAdmissiblePathCoefficient
  exact Fintype.sum_equiv
    (boundedKernelLengthProfileEquivAdmissibleAntidiagonal d K)
    (fun L : BoundedKernelLengthProfile (K.shape.1.val + d) K ↦
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M tau
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2)
          (L.length e).val)
    (fun A : BoundedKernelAdmissibleLengthAntidiagonal d K ↦
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M tau
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (A.1.1 e))
    (fun _ ↦ rfl)

/-! ## Finite witnesses to inadmissibility -/

/-- A loop edge together with one of its two forbidden lengths. -/
structure BoundedKernelShortLoopWitness
    {ell : ℕ} (K : LabelledBoundedKernel ell) where
  edge : Fin K.shape.2.1.val
  isLoop : (K.shape.2.2 edge).IsDiag
  length : Fin 2

/-- Two distinct edge labels with the same endpoint pair. -/
structure BoundedKernelRepeatedZeroWitness
    {ell : ℕ} (K : LabelledBoundedKernel ell) where
  first : Fin K.shape.2.1.val
  second : Fin K.shape.2.1.val
  ne : first ≠ second
  endpoints_eq : K.shape.2.2 first = K.shape.2.2 second

abbrev BoundedKernelForbiddenLengthWitness
    {ell : ℕ} (K : LabelledBoundedKernel ell) :=
  BoundedKernelShortLoopWitness K ⊕ BoundedKernelRepeatedZeroWitness K

def BoundedKernelForbiddenLengthWitness.Occurs
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (w : BoundedKernelForbiddenLengthWitness K)
    (l : Fin K.shape.2.1.val →₀ ℕ) : Prop :=
  match w with
  | Sum.inl w => l w.edge = w.length.val
  | Sum.inr w => l w.first = 0 ∧ l w.second = 0

@[instance_reducible] noncomputable def boundedKernelShortLoopWitnessFintype
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype (BoundedKernelShortLoopWitness K) := by
  apply Fintype.ofInjective (fun w ↦ (w.edge, w.length))
  intro a b h
  cases a
  cases b
  cases h
  rfl

@[instance_reducible] noncomputable def boundedKernelRepeatedZeroWitnessFintype
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype (BoundedKernelRepeatedZeroWitness K) := by
  apply Fintype.ofInjective (fun w ↦ (w.first, w.second))
  intro a b h
  cases a
  cases b
  cases h
  rfl

@[instance_reducible] noncomputable def boundedKernelForbiddenLengthWitnessFintype
    {ell : ℕ} (K : LabelledBoundedKernel ell) :
    Fintype (BoundedKernelForbiddenLengthWitness K) := by
  letI := boundedKernelShortLoopWitnessFintype K
  letI := boundedKernelRepeatedZeroWitnessFintype K
  infer_instance

theorem not_boundedKernelLengthAssignment_admissible_iff
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (l : Fin K.shape.2.1.val →₀ ℕ) :
    ¬ BoundedKernelLengthAssignment.IsAdmissible K l ↔
      ∃ w : BoundedKernelForbiddenLengthWitness K, w.Occurs l := by
  classical
  constructor
  · intro h
    rw [BoundedKernelLengthAssignment.IsAdmissible, not_and_or] at h
    rcases h with hloop | hparallel
    · push Not at hloop
      obtain ⟨e, heLoop, heShort⟩ := hloop
      let n : Fin 2 := ⟨l e, heShort⟩
      exact ⟨Sum.inl ⟨e, heLoop, n⟩, rfl⟩
    · obtain ⟨e, f, hef, hne⟩ :=
        Function.not_injective_iff.mp hparallel
      let w : BoundedKernelRepeatedZeroWitness K :=
        { first := e.1
          second := f.1
          ne := by
            intro hval
            apply hne
            exact Subtype.ext hval
          endpoints_eq := hef }
      exact ⟨Sum.inr w, ⟨e.2, f.2⟩⟩
  · rintro ⟨w, hw⟩ hadm
    rcases w with w | w
    · have hge := hadm.1 w.edge w.isLoop
      rw [hw] at hge
      omega
    · let e : {a : Fin K.shape.2.1.val // l a = 0} :=
        ⟨w.first, hw.1⟩
      let f : {a : Fin K.shape.2.1.val // l a = 0} :=
        ⟨w.second, hw.2⟩
      have heq : e = f := hadm.2 (by simpa only [e, f] using w.endpoints_eq)
      exact w.ne (congrArg Subtype.val heq)

/-- The finite set of values forced on one edge by one witness. -/
def boundedKernelForbiddenWitnessForcedValues
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (w : BoundedKernelForbiddenLengthWitness K)
    (e : Fin K.shape.2.1.val) : Finset ℕ :=
  match w with
  | Sum.inl w => if e = w.edge then {w.length.val} else ∅
  | Sum.inr w => if e = w.first ∨ e = w.second then {0} else ∅

noncomputable def boundedKernelForbiddenPatternForcedValues
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) : Finset ℕ := by
  classical
  exact J.biUnion (fun w ↦ boundedKernelForbiddenWitnessForcedValues w e)

def BoundedKernelForbiddenPatternCompatible
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (J : Finset (BoundedKernelForbiddenLengthWitness K)) : Prop :=
  ∀ e, (boundedKernelForbiddenPatternForcedValues J e).card ≤ 1

def BoundedKernelForbiddenPatternForcesEdge
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) : Prop :=
  (boundedKernelForbiddenPatternForcedValues J e).Nonempty

noncomputable def boundedKernelForbiddenPatternLength
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) : ℕ :=
  if h : (boundedKernelForbiddenPatternForcedValues J e).Nonempty then
    (boundedKernelForbiddenPatternForcedValues J e).min' h
  else 0

private def boundedKernelForbiddenWitnessAnchorEdge
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (w : BoundedKernelForbiddenLengthWitness K) : Fin K.shape.2.1.val :=
  match w with
  | Sum.inl w => w.edge
  | Sum.inr w => w.first

private def boundedKernelForbiddenWitnessAnchorLength
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (w : BoundedKernelForbiddenLengthWitness K) : ℕ :=
  match w with
  | Sum.inl w => w.length.val
  | Sum.inr _ => 0

private theorem boundedKernelForbiddenWitnessAnchorLength_mem
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (w : BoundedKernelForbiddenLengthWitness K) :
    boundedKernelForbiddenWitnessAnchorLength w ∈
      boundedKernelForbiddenWitnessForcedValues w
        (boundedKernelForbiddenWitnessAnchorEdge w) := by
  rcases w with w | w
  · simp [boundedKernelForbiddenWitnessAnchorLength,
      boundedKernelForbiddenWitnessAnchorEdge,
      boundedKernelForbiddenWitnessForcedValues]
  · simp [boundedKernelForbiddenWitnessAnchorLength,
      boundedKernelForbiddenWitnessAnchorEdge,
      boundedKernelForbiddenWitnessForcedValues]

theorem boundedKernelForbiddenPattern_exists_forcedEdge
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    {J : Finset (BoundedKernelForbiddenLengthWitness K)}
    (hJ : J.Nonempty) :
    ∃ e : Fin K.shape.2.1.val,
      BoundedKernelForbiddenPatternForcesEdge J e := by
  classical
  obtain ⟨w, hw⟩ := hJ
  refine ⟨boundedKernelForbiddenWitnessAnchorEdge w, ?_⟩
  unfold BoundedKernelForbiddenPatternForcesEdge
    boundedKernelForbiddenPatternForcedValues
  refine ⟨boundedKernelForbiddenWitnessAnchorLength w, ?_⟩
  exact Finset.mem_biUnion.mpr
    ⟨w, hw, boundedKernelForbiddenWitnessAnchorLength_mem w⟩

theorem boundedKernelForbiddenWitness_occurs_iff_forcedValues
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (w : BoundedKernelForbiddenLengthWitness K)
    (l : Fin K.shape.2.1.val → ℕ) :
    w.Occurs (Finsupp.equivFunOnFinite.symm l) ↔
      ∀ e n, n ∈ boundedKernelForbiddenWitnessForcedValues w e →
        l e = n := by
  rcases w with w | w
  · change l w.edge = w.length.val ↔
      ∀ e n, n ∈ (if e = w.edge then ({w.length.val} : Finset ℕ)
        else (∅ : Finset ℕ)) → l e = n
    constructor
    · intro h e n hn
      by_cases he : e = w.edge
      · subst e
        have hnval : n = w.length.val := by
          simpa only [if_true, Finset.mem_singleton] using hn
        exact h.trans hnval.symm
      · simp [he] at hn
    · intro hall
      exact hall w.edge w.length.val (by simp)
  · change (l w.first = 0 ∧ l w.second = 0) ↔
      ∀ e n, n ∈ (if e = w.first ∨ e = w.second then ({0} : Finset ℕ)
        else (∅ : Finset ℕ)) → l e = n
    constructor
    · rintro ⟨hfirst, hsecond⟩ e n hn
      by_cases he : e = w.first ∨ e = w.second
      · have hn0 : n = 0 := by
          simpa only [if_pos he, Finset.mem_singleton] using hn
        rcases he with rfl | rfl
        · simpa only [hn0] using hfirst
        · simpa only [hn0] using hsecond
      · simp [he] at hn
    · intro hall
      exact ⟨hall w.first 0 (by simp), hall w.second 0 (by simp)⟩

theorem boundedKernelForbiddenPatternLength_mem
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val)
    (he : BoundedKernelForbiddenPatternForcesEdge J e) :
    boundedKernelForbiddenPatternLength J e ∈
      boundedKernelForbiddenPatternForcedValues J e := by
  change (boundedKernelForbiddenPatternForcedValues J e).Nonempty at he
  simp only [boundedKernelForbiddenPatternLength, dif_pos he]
  exact Finset.min'_mem _ he

theorem boundedKernelForbiddenPattern_eq_length_of_mem
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    {J : Finset (BoundedKernelForbiddenLengthWitness K)}
    (hJ : BoundedKernelForbiddenPatternCompatible J)
    {e : Fin K.shape.2.1.val} {n : ℕ}
    (hn : n ∈ boundedKernelForbiddenPatternForcedValues J e) :
    n = boundedKernelForbiddenPatternLength J e := by
  exact (Finset.card_le_one_iff.mp (hJ e)) hn
    (boundedKernelForbiddenPatternLength_mem J e ⟨n, hn⟩)

theorem boundedKernelForbiddenPattern_all_occurs_iff
    {ell : ℕ} {K : LabelledBoundedKernel ell}
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (l : Fin K.shape.2.1.val → ℕ) :
    (∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)) ↔
      BoundedKernelForbiddenPatternCompatible J ∧
        ∀ e, BoundedKernelForbiddenPatternForcesEdge J e →
          l e = boundedKernelForbiddenPatternLength J e := by
  constructor
  · intro hall
    have hcompat : BoundedKernelForbiddenPatternCompatible J := by
      intro e
      rw [Finset.card_le_one_iff]
      intro m n hm hn
      change m ∈ J.biUnion
        (fun w ↦ boundedKernelForbiddenWitnessForcedValues w e) at hm
      change n ∈ J.biUnion
        (fun w ↦ boundedKernelForbiddenWitnessForcedValues w e) at hn
      rw [Finset.mem_biUnion] at hm hn
      obtain ⟨wm, hwmJ, hwm⟩ := hm
      obtain ⟨wn, hwnJ, hwn⟩ := hn
      have hm' :=
        (boundedKernelForbiddenWitness_occurs_iff_forcedValues wm l).mp
          (hall wm hwmJ) e m hwm
      have hn' :=
        (boundedKernelForbiddenWitness_occurs_iff_forcedValues wn l).mp
          (hall wn hwnJ) e n hwn
      exact hm'.symm.trans hn'
    refine ⟨hcompat, ?_⟩
    intro e he
    have hlen := boundedKernelForbiddenPatternLength_mem J e he
    change boundedKernelForbiddenPatternLength J e ∈
      J.biUnion (fun w ↦ boundedKernelForbiddenWitnessForcedValues w e) at hlen
    rw [Finset.mem_biUnion] at hlen
    obtain ⟨w, hwJ, hwlen⟩ := hlen
    exact (boundedKernelForbiddenWitness_occurs_iff_forcedValues w l).mp
      (hall w hwJ) e _ hwlen
  · rintro ⟨hcompat, hlength⟩ w hwJ
    rw [boundedKernelForbiddenWitness_occurs_iff_forcedValues]
    intro e n hn
    have hnPattern : n ∈ boundedKernelForbiddenPatternForcedValues J e := by
      change n ∈ J.biUnion
        (fun u ↦ boundedKernelForbiddenWitnessForcedValues u e)
      rw [Finset.mem_biUnion]
      exact ⟨w, hwJ, hn⟩
    have he : BoundedKernelForbiddenPatternForcesEdge J e :=
      ⟨n, hnPattern⟩
    exact (hlength e he).trans
      (boundedKernelForbiddenPattern_eq_length_of_mem hcompat hnPattern).symm

/-! ## Raw and normalized finite witness cylinders -/

/-- One fixed-length path coefficient, evaluated at the endpoints of a
bounded kernel edge along the joint fold chart. -/
def boundedKernelFixedLengthEdgeFactor
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  cubicFixedLengthPathKernel M hM n q
    (x (boundedKernelOrderedEndpoints K.shape e).1,
      x (boundedKernelOrderedEndpoints K.shape e).2)

@[simp] theorem boundedKernelFixedLengthEdgeFactor_eq_profileCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    boundedKernelFixedLengthEdgeFactor M hM K e n q x =
      profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n := by
  rfl

theorem boundedKernelFixedLengthEdgeFactor_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (e : Fin K.shape.2.1.val) (n : ℕ)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelFixedLengthEdgeFactor M hM K e n q x) (0, 0) := by
  let p : S × S :=
    (x (boundedKernelOrderedEndpoints K.shape e).1,
      x (boundedKernelOrderedEndpoints K.shape e).2)
  have heval : AnalyticAt ℂ
      (fun k : C(S × S, ℂ) ↦ k p)
      (cubicFixedLengthPathKernel M hM n (0, 0)) :=
    (ContinuousMap.evalCLM ℂ p : C(S × S, ℂ) →L[ℂ] ℂ).analyticAt _
  exact heval.comp_of_eq (cubicFixedLengthPathKernel_analytic M hM n) rfl

/-- Raw fixed-length/resolvent factor associated with one witness pattern. -/
def boundedKernelForbiddenRawPatternEdgeFactor
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    boundedKernelFixedLengthEdgeFactor M hM K e
      (boundedKernelForbiddenPatternLength J e) q x
  else
    NBKAS_MPR.pathResolventKernel M hM q
      (x (boundedKernelOrderedEndpoints K.shape e).1,
        x (boundedKernelOrderedEndpoints K.shape e).2)

/-- Pole-removed edge factor for one witness pattern. -/
def boundedKernelForbiddenNormalizedPatternEdgeFactor
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    q.2 * boundedKernelFixedLengthEdgeFactor M hM K e
      (boundedKernelForbiddenPatternLength J e) q x
  else
    boundedKernelNormalizedEdgeFactor M hM K.shape x e q

theorem boundedKernelForbiddenNormalizedPatternEdgeFactor_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ
      (fun q ↦ boundedKernelForbiddenNormalizedPatternEdgeFactor
        M hM K J e q x) (0, 0) := by
  classical
  unfold boundedKernelForbiddenNormalizedPatternEdgeFactor
  split_ifs
  · exact analyticAt_snd.mul
      (boundedKernelFixedLengthEdgeFactor_analytic M hM K e
        (boundedKernelForbiddenPatternLength J e) x)
  · exact boundedKernelNormalizedEdgeFactor_analytic M hM K.shape x e

theorem boundedKernelForbiddenNormalizedPatternEdgeFactor_eq_X_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelForbiddenNormalizedPatternEdgeFactor M hM K J e q x =
        q.2 * boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  filter_upwards
    [boundedNormalizedPathKernel_eq_smul_pathResolventKernel M hM] with q hq
  intro hX
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · simp [boundedKernelForbiddenNormalizedPatternEdgeFactor,
      boundedKernelForbiddenRawPatternEdgeFactor, he]
  · unfold boundedKernelForbiddenNormalizedPatternEdgeFactor
      boundedKernelForbiddenRawPatternEdgeFactor
    rw [if_neg he, if_neg he]
    have hfun := congrArg
      (fun f : C(S × S, ℂ) ↦
        f (x (boundedKernelOrderedEndpoints K.shape e).1,
          x (boundedKernelOrderedEndpoints K.shape e).2)) (hq hX)
    simpa only [boundedKernelNormalizedEdgeFactor,
      ContinuousMap.smul_apply, smul_eq_mul] using hfun

/-- Raw simultaneous witness intersection. -/
def boundedKernelForbiddenRawIntersection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    boundedKernelBranchProfileProduct M hM K.shape x q *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x
  else 0

/-- Pole-removed simultaneous witness intersection. -/
def boundedKernelForbiddenNormalizedIntersection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    boundedKernelBranchProfileProduct M hM K.shape x q *
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenNormalizedPatternEdgeFactor M hM K J e q x
  else 0

theorem boundedKernelForbiddenNormalizedIntersection_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelForbiddenNormalizedIntersection M hM K J q x)
      (0, 0) := by
  classical
  unfold boundedKernelForbiddenNormalizedIntersection
  split_ifs
  · exact (boundedKernelBranchProfileProduct_analytic M hM K.shape x).mul
      ((Finset.univ : Finset (Fin K.shape.2.1.val)).analyticAt_fun_prod
        (fun e _ ↦
          boundedKernelForbiddenNormalizedPatternEdgeFactor_analytic
            M hM K J e x))
  · exact analyticAt_const

theorem boundedKernelForbiddenNormalizedIntersection_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (hJ : J.Nonempty) (g : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelForbiddenNormalizedIntersection M hM K J (g, 0) x = 0 := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · obtain ⟨e, he⟩ := boundedKernelForbiddenPattern_exists_forcedEdge hJ
    have hedge :
        boundedKernelForbiddenNormalizedPatternEdgeFactor
          M hM K J e (g, 0) x = 0 := by
      simp [boundedKernelForbiddenNormalizedPatternEdgeFactor, he]
    unfold boundedKernelForbiddenNormalizedIntersection
    rw [if_pos hcompat, Finset.prod_eq_zero (Finset.mem_univ e) hedge]
    simp
  · simp [boundedKernelForbiddenNormalizedIntersection, hcompat]

theorem boundedKernelForbiddenNormalizedIntersection_eq_pow_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelForbiddenNormalizedIntersection M hM K J q x =
        q.2 ^ K.shape.2.1.val *
          boundedKernelForbiddenRawIntersection M hM K J q x := by
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ e : Fin K.shape.2.1.val, q.2 ≠ 0 →
          boundedKernelForbiddenNormalizedPatternEdgeFactor
              M hM K J e q x =
            q.2 * boundedKernelForbiddenRawPatternEdgeFactor
              M hM K J e q x := by
    rw [Filter.eventually_all]
    intro e
    exact boundedKernelForbiddenNormalizedPatternEdgeFactor_eq_X_mul_raw
      M hM K J e x
  filter_upwards [hall] with q hq
  intro hX
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · unfold boundedKernelForbiddenNormalizedIntersection
      boundedKernelForbiddenRawIntersection
    rw [if_pos hcompat, if_pos hcompat]
    simp_rw [hq _ hX]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  · simp [boundedKernelForbiddenNormalizedIntersection,
      boundedKernelForbiddenRawIntersection, hcompat]

/-- Finite inclusion--exclusion correction on the raw resolvent scale. -/
def boundedKernelRawForbiddenCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ := by
  letI := boundedKernelForbiddenLengthWitnessFintype K
  exact ∑ J ∈ (Finset.univ :
      Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
        Finset.Nonempty,
    (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenRawIntersection M hM K J q x

/-- The same finite correction after removing one pole from every kernel
edge. -/
def boundedKernelNormalizedForbiddenCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ := by
  letI := boundedKernelForbiddenLengthWitnessFintype K
  exact ∑ J ∈ (Finset.univ :
      Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
        Finset.Nonempty,
    (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenNormalizedIntersection M hM K J q x

theorem boundedKernelNormalizedForbiddenCorrection_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelNormalizedForbiddenCorrection M hM K q x) (0, 0) := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrection
  let s := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let F : Finset (BoundedKernelForbiddenLengthWitness K) →
      (C(S, ℂ) × ℂ → ℂ) := fun J q ↦
    (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenNormalizedIntersection M hM K J q x
  change AnalyticAt ℂ
    (fun q : C(S, ℂ) × ℂ ↦ Finset.sum s (fun J ↦ F J q)) (0, 0)
  have hsum : AnalyticAt ℂ (Finset.sum s F) (0, 0) := by
    apply Finset.analyticAt_sum
    intro J hJ
    exact analyticAt_const.mul
      (boundedKernelForbiddenNormalizedIntersection_analytic M hM K J x)
  have hfun : Finset.sum s F =
      (fun q : C(S, ℂ) × ℂ ↦ Finset.sum s (fun J ↦ F J q)) := by
    funext q
    exact Finset.sum_apply q s F
  rw [← hfun]
  exact hsum

theorem boundedKernelNormalizedForbiddenCorrection_axis
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (g : C(S, ℂ)) (x : Fin K.shape.1.val → S) :
    boundedKernelNormalizedForbiddenCorrection M hM K (g, 0) x = 0 := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  unfold boundedKernelNormalizedForbiddenCorrection
  apply Finset.sum_eq_zero
  intro J hJ
  have hne : J.Nonempty := (Finset.mem_filter.mp hJ).2
  rw [boundedKernelForbiddenNormalizedIntersection_axis M hM K J hne g x,
    mul_zero]

theorem boundedKernelNormalizedForbiddenCorrection_eq_pow_mul_raw
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0), q.2 ≠ 0 →
      boundedKernelNormalizedForbiddenCorrection M hM K q x =
        q.2 ^ K.shape.2.1.val *
          boundedKernelRawForbiddenCorrection M hM K q x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  have hall :
      ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
        ∀ J : Finset (BoundedKernelForbiddenLengthWitness K),
          q.2 ≠ 0 →
          boundedKernelForbiddenNormalizedIntersection M hM K J q x =
            q.2 ^ K.shape.2.1.val *
              boundedKernelForbiddenRawIntersection M hM K J q x := by
    rw [Filter.eventually_all]
    intro J
    exact boundedKernelForbiddenNormalizedIntersection_eq_pow_mul_raw
      M hM K J x
  filter_upwards [hall] with q hq
  intro hX
  unfold boundedKernelNormalizedForbiddenCorrection
    boundedKernelRawForbiddenCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [hq J hX]
  ring

/-! ## Literal all-length assignment sums -/

/-- Literal unrestricted all-length path/profile integrand. -/
def boundedKernelLiteralUnrestrictedAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelBranchProfileProduct M hM K.shape x q *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)

/-- Literal admissible all-length path/profile integrand.  The predicate is
exactly the one encoded by `BoundedKernelLengthProfile`. -/
def boundedKernelLiteralAdmissibleAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelBranchProfileProduct M hM K.shape x q *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      if BoundedKernelLengthAssignment.IsAdmissible K
          (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0

/-- Literal forbidden all-length path/profile integrand. -/
def boundedKernelLiteralForbiddenAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelBranchProfileProduct M hM K.shape x q *
    ∑' l : Fin K.shape.2.1.val → ℕ,
      if ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0

private theorem boundedKernelAssignmentProduct_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    Summable (fun l : Fin K.shape.2.1.val → ℕ ↦
      ∏ e : Fin K.shape.2.1.val,
        profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)) := by
  exact (summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (NBKAS_MPR.profile M hM q) r hr hr1 hprofile _ _)).1

theorem boundedKernelCoreResolventIntegrand_eq_literalUnrestricted
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelCoreResolventIntegrand M hM K.shape x q =
      boundedKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  unfold boundedKernelCoreResolventIntegrand
    boundedKernelLiteralUnrestrictedAssignmentIntegrand
  apply congrArg (fun z : ℂ ↦
    boundedKernelBranchProfileProduct M hM K.shape x q * z)
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (NBKAS_MPR.profile M hM q) r hr hr1 hprofile _ _)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    M hM q r hr hr1 hprofile _ _ |>.symm

theorem boundedKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelLiteralAdmissibleAssignmentIntegrand M hM K q x +
        boundedKernelLiteralForbiddenAssignmentIntegrand M hM K q x =
      boundedKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  classical
  let B : (Fin K.shape.2.1.val → ℕ) → ℂ := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
  let A : Set (Fin K.shape.2.1.val → ℕ) := {l |
    BoundedKernelLengthAssignment.IsAdmissible K
      (Finsupp.equivFunOnFinite.symm l)}
  let F : Set (Fin K.shape.2.1.val → ℕ) := {l |
    ∃ w : BoundedKernelForbiddenLengthWitness K,
      w.Occurs (Finsupp.equivFunOnFinite.symm l)}
  have hB : Summable B :=
    boundedKernelAssignmentProduct_summable M hM K q x r hr hr1 hprofile
  have hA : Summable (A.indicator B) := hB.indicator A
  have hF : Summable (F.indicator B) := hB.indicator F
  have hterm (l : Fin K.shape.2.1.val → ℕ) :
      A.indicator B l + F.indicator B l = B l := by
    have hiff := not_boundedKernelLengthAssignment_admissible_iff K
      (Finsupp.equivFunOnFinite.symm l)
    by_cases ha : BoundedKernelLengthAssignment.IsAdmissible K
        (Finsupp.equivFunOnFinite.symm l)
    · have hf : ¬ ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) :=
        fun hw ↦ (hiff.mpr hw) ha
      have hAl : l ∈ A := by simpa [A] using ha
      have hFl : l ∉ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
    · have hf : ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) := hiff.mp ha
      have hAl : l ∉ A := by simpa [A] using ha
      have hFl : l ∈ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
  unfold boundedKernelLiteralAdmissibleAssignmentIntegrand
    boundedKernelLiteralForbiddenAssignmentIntegrand
    boundedKernelLiteralUnrestrictedAssignmentIntegrand
  rw [← mul_add]
  apply congrArg (fun z : ℂ ↦
    boundedKernelBranchProfileProduct M hM K.shape x q * z)
  change (∑' l, A.indicator B l) + (∑' l, F.indicator B l) = ∑' l, B l
  rw [← hA.tsum_add hF]
  exact tsum_congr hterm

/-! ## The finite correction is the literal forbidden subseries -/

/-- The one-edge coefficient sequence with a pattern-forced length frozen. -/
def boundedKernelForbiddenPatternEdgeCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S) (n : ℕ) : ℂ :=
  if BoundedKernelForbiddenPatternForcesEdge J e then
    if n = boundedKernelForbiddenPatternLength J e then
      profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    else 0
  else
    profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2) n

theorem boundedKernelForbiddenPatternEdgeCoefficient_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    Summable (boundedKernelForbiddenPatternEdgeCoefficient
      M hM K J e q x) := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    have hs := (hasSum_ite_eq (boundedKernelForbiddenPatternLength J e)
      (c (boundedKernelForbiddenPatternLength J e))).summable
    exact hs.congr (fun n ↦ by
      by_cases hn : n = boundedKernelForbiddenPatternLength J e
      · subst n
        simp [boundedKernelForbiddenPatternEdgeCoefficient, he, c]
      · simp [boundedKernelForbiddenPatternEdgeCoefficient, he, hn, c])
  · exact (summable_profilePathEdgeCoefficient M hM
      (NBKAS_MPR.profile M hM q) r hr hr1 hprofile
      (x (boundedKernelOrderedEndpoints K.shape e).1)
      (x (boundedKernelOrderedEndpoints K.shape e).2)).congr
        (fun n ↦ by
          simp [boundedKernelForbiddenPatternEdgeCoefficient, he])

theorem tsum_boundedKernelForbiddenPatternEdgeCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (e : Fin K.shape.2.1.val) (q : C(S, ℂ) × ℂ)
    (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    (∑' n : ℕ,
        boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x n) =
      boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  classical
  by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) n
    calc
      (∑' n : ℕ,
          boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x n) =
          c (boundedKernelForbiddenPatternLength J e) := by
        calc
          _ = ∑' n : ℕ,
              if n = boundedKernelForbiddenPatternLength J e then
                c (boundedKernelForbiddenPatternLength J e) else 0 := by
            apply tsum_congr
            intro n
            by_cases hn : n = boundedKernelForbiddenPatternLength J e
            · subst n
              simp [boundedKernelForbiddenPatternEdgeCoefficient, he, c]
            · simp [boundedKernelForbiddenPatternEdgeCoefficient, he, hn, c]
          _ = c (boundedKernelForbiddenPatternLength J e) :=
            (hasSum_ite_eq (boundedKernelForbiddenPatternLength J e)
              (c (boundedKernelForbiddenPatternLength J e))).tsum_eq
      _ = boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
        simp [boundedKernelForbiddenRawPatternEdgeFactor, he, c]
  · rw [show (∑' n : ℕ,
        boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x n) =
        ∑' n : ℕ, profilePathEdgeCoefficient M
          (NBKAS_MPR.profile M hM q)
          (x (boundedKernelOrderedEndpoints K.shape e).1)
          (x (boundedKernelOrderedEndpoints K.shape e).2) n by
      apply tsum_congr
      intro n
      simp [boundedKernelForbiddenPatternEdgeCoefficient, he]]
    rw [tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
      M hM q r hr hr1 hprofile]
    simp [boundedKernelForbiddenRawPatternEdgeFactor, he]

/-- Pattern-restricted table weight; incompatible intersections are empty. -/
def boundedKernelForbiddenPatternAssignmentWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (l : Fin K.shape.2.1.val → ℕ) : ℂ :=
  if BoundedKernelForbiddenPatternCompatible J then
    ∏ e : Fin K.shape.2.1.val,
      boundedKernelForbiddenPatternEdgeCoefficient M hM K J e q x (l e)
  else 0

theorem boundedKernelForbiddenPatternAssignmentWeight_eq_occurrenceIndicator
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (l : Fin K.shape.2.1.val → ℕ) :
    boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l =
      if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin K.shape.2.1.val,
          profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
            (x (boundedKernelOrderedEndpoints K.shape e).1)
            (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
      else 0 := by
  classical
  by_cases hall :
      ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
  · obtain ⟨hcompat, hlength⟩ :=
      (boundedKernelForbiddenPattern_all_occurs_iff J l).mp hall
    rw [if_pos hall]
    unfold boundedKernelForbiddenPatternAssignmentWeight
    rw [if_pos hcompat]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : BoundedKernelForbiddenPatternForcesEdge J e
    · simp [boundedKernelForbiddenPatternEdgeCoefficient, he,
        hlength e he]
    · simp [boundedKernelForbiddenPatternEdgeCoefficient, he]
  · rw [if_neg hall]
    unfold boundedKernelForbiddenPatternAssignmentWeight
    by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
    · rw [if_pos hcompat]
      have hnot : ¬ ∀ e, BoundedKernelForbiddenPatternForcesEdge J e →
          l e = boundedKernelForbiddenPatternLength J e := by
        intro hlength
        exact hall ((boundedKernelForbiddenPattern_all_occurs_iff J l).mpr
          ⟨hcompat, hlength⟩)
      push Not at hnot
      obtain ⟨e, he, hne⟩ := hnot
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [boundedKernelForbiddenPatternEdgeCoefficient, he, hne]
    · simp [hcompat]

theorem boundedKernelForbiddenPatternAssignmentWeight_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    Summable (boundedKernelForbiddenPatternAssignmentWeight
      M hM K J q x) := by
  classical
  by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
  · exact (summable_finFunction_prod_and_tsum
        (fun e n ↦ boundedKernelForbiddenPatternEdgeCoefficient
          M hM K J e q x n)
        (fun e ↦ boundedKernelForbiddenPatternEdgeCoefficient_summable
          M hM K J e q x r hr hr1 hprofile)).1.congr
      (fun l ↦ by
        simp [boundedKernelForbiddenPatternAssignmentWeight, hcompat])
  · exact summable_zero.congr
      (fun l ↦ by
        simp [boundedKernelForbiddenPatternAssignmentWeight, hcompat])

theorem tsum_boundedKernelForbiddenPatternAssignmentWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (J : Finset (BoundedKernelForbiddenLengthWitness K))
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r)
    (hcompat : BoundedKernelForbiddenPatternCompatible J) :
    (∑' l : Fin K.shape.2.1.val → ℕ,
        boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l) =
      ∏ e : Fin K.shape.2.1.val,
        boundedKernelForbiddenRawPatternEdgeFactor M hM K J e q x := by
  classical
  simp only [boundedKernelForbiddenPatternAssignmentWeight, hcompat, if_true]
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ boundedKernelForbiddenPatternEdgeCoefficient
      M hM K J e q x n)
    (fun e ↦ boundedKernelForbiddenPatternEdgeCoefficient_summable
      M hM K J e q x r hr hr1 hprofile)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_boundedKernelForbiddenPatternEdgeCoefficient
    M hM K J e q x r hr hr1 hprofile

private theorem boundedKernel_sum_nonempty_powerset
    {W : Type*} [DecidableEq W] (s : Finset W) (hs : s.Nonempty) :
    (∑ J ∈ s.powerset.filter Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1)) = 1 := by
  have hzInt := Finset.sum_powerset_neg_one_pow_card_of_nonempty hs
  have hz : (∑ J ∈ s.powerset, (-1 : ℂ) ^ J.card) = 0 := by
    exact_mod_cast hzInt
  have hempty : (∅ : Finset W) ∈ s.powerset := Finset.empty_mem_powerset s
  have herase : s.powerset.filter Finset.Nonempty = s.powerset.erase ∅ := by
    apply Finset.ext
    intro J
    simp [Finset.nonempty_iff_ne_empty, and_comm]
  rw [herase]
  have hbase :
      (∑ J ∈ s.powerset.erase ∅, (-1 : ℂ) ^ J.card) = -1 := by
    have hsplit := Finset.sum_erase_add
      (s := s.powerset) (f := fun J : Finset W ↦ (-1 : ℂ) ^ J.card)
      hempty
    calc
      (∑ J ∈ s.powerset.erase ∅, (-1 : ℂ) ^ J.card) =
          (∑ J ∈ s.powerset, (-1 : ℂ) ^ J.card) - 1 := by
        rw [eq_sub_iff_add_eq]
        simpa only [Finset.card_empty, pow_zero] using hsplit
      _ = -1 := by rw [hz]; ring
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, hbase]
  norm_num

theorem boundedKernelForbidden_inclusionExclusion_assignment
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (l : Fin K.shape.2.1.val → ℕ) (z : ℂ) :
    letI := boundedKernelForbiddenLengthWitnessFintype K
    (∑ J ∈ (Finset.univ :
        Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
          Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1) *
        (if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
          then z else 0)) =
      if ∃ w : BoundedKernelForbiddenLengthWitness K,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then z else 0 := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  classical
  let W : Finset (BoundedKernelForbiddenLengthWitness K) :=
    Finset.univ.filter fun w ↦
      w.Occurs (Finsupp.equivFunOnFinite.symm l)
  by_cases hW : W.Nonempty
  · have hex : ∃ w : BoundedKernelForbiddenLengthWitness K,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) := by
      obtain ⟨w, hw⟩ := hW
      exact ⟨w, (Finset.mem_filter.mp hw).2⟩
    rw [if_pos hex]
    have hfilter :
        ((Finset.univ :
            Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
              Finset.Nonempty).filter (fun J ↦ ∀ w ∈ J,
                w.Occurs (Finsupp.equivFunOnFinite.symm l)) =
          W.powerset.filter Finset.Nonempty := by
      apply Finset.ext
      intro J
      constructor
      · intro hJ
        have hOuter := Finset.mem_filter.mp hJ
        have hInner := Finset.mem_filter.mp hOuter.1
        refine Finset.mem_filter.mpr ⟨?_, hInner.2⟩
        refine Finset.mem_powerset.mpr ?_
        intro w hw
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ w, hOuter.2 w hw⟩
      · intro hJ
        have hRight := Finset.mem_filter.mp hJ
        have hSubset := Finset.mem_powerset.mp hRight.1
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.subset_univ J), hRight.2⟩
        · intro w hw
          exact (Finset.mem_filter.mp (hSubset hw)).2
    calc
      (∑ J ∈ (Finset.univ :
          Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
            Finset.Nonempty,
        (-1 : ℂ) ^ (J.card + 1) *
          (if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
            then z else 0)) =
          ∑ J ∈ (Finset.univ :
              Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
                Finset.Nonempty,
            if (∀ w ∈ J,
                w.Occurs (Finsupp.equivFunOnFinite.symm l)) then
              (-1 : ℂ) ^ (J.card + 1) * z else 0 := by
        apply Finset.sum_congr rfl
        intro J _
        by_cases hocc : ∀ w ∈ J,
            w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all
      _ = ∑ J ∈ ((Finset.univ :
              Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
                Finset.Nonempty).filter (fun J ↦ ∀ w ∈ J,
                  w.Occurs (Finsupp.equivFunOnFinite.symm l)),
             (-1 : ℂ) ^ (J.card + 1) * z := by
        simp only [Finset.sum_filter]
      _ = ∑ J ∈ W.powerset.filter Finset.Nonempty,
            (-1 : ℂ) ^ (J.card + 1) * z := by rw [hfilter]
      _ = (∑ J ∈ W.powerset.filter Finset.Nonempty,
            (-1 : ℂ) ^ (J.card + 1)) * z := by
        rw [Finset.sum_mul]
      _ = z := by
        rw [boundedKernel_sum_nonempty_powerset W hW, one_mul]
  · have hnex : ¬ ∃ w : BoundedKernelForbiddenLengthWitness K,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) := by
      rintro ⟨w, hw⟩
      exact hW ⟨w, by simp [W, hw]⟩
    rw [if_neg hnex]
    apply Finset.sum_eq_zero
    intro J hJ
    have hne : J.Nonempty := (Finset.mem_filter.mp hJ).2
    obtain ⟨w, hw⟩ := hne
    have hnot : ¬ ∀ u ∈ J,
        u.Occurs (Finsupp.equivFunOnFinite.symm l) := by
      intro hall
      exact hnex ⟨w, hall w hw⟩
    rw [if_neg hnot, mul_zero]

theorem boundedKernelRawForbiddenCorrection_eq_literalForbidden
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelRawForbiddenCorrection M hM K q x =
      boundedKernelLiteralForbiddenAssignmentIntegrand M hM K q x := by
  let _ := boundedKernelForbiddenLengthWitnessFintype K
  classical
  let P := (Finset.univ :
    Finset (BoundedKernelForbiddenLengthWitness K)).powerset.filter
      Finset.Nonempty
  let B : (Fin K.shape.2.1.val → ℕ) → ℂ := fun l ↦
    ∏ e : Fin K.shape.2.1.val,
      profilePathEdgeCoefficient M (NBKAS_MPR.profile M hM q)
        (x (boundedKernelOrderedEndpoints K.shape e).1)
        (x (boundedKernelOrderedEndpoints K.shape e).2) (l e)
  have hJsum (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      boundedKernelForbiddenRawIntersection M hM K J q x =
        boundedKernelBranchProfileProduct M hM K.shape x q *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight
              M hM K J q x l := by
    unfold boundedKernelForbiddenRawIntersection
    by_cases hcompat : BoundedKernelForbiddenPatternCompatible J
    · rw [if_pos hcompat,
          tsum_boundedKernelForbiddenPatternAssignmentWeight
            M hM K J q x r hr hr1 hprofile hcompat]
    · rw [if_neg hcompat]
      have hzero :
          (∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight
              M hM K J q x l) = 0 := by
        simp [boundedKernelForbiddenPatternAssignmentWeight, hcompat]
      rw [hzero, mul_zero]
  have hsumJ (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      Summable (fun l : Fin K.shape.2.1.val → ℕ ↦
        (-1 : ℂ) ^ (J.card + 1) *
          boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l) :=
    (boundedKernelForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).mul_left _
  unfold boundedKernelRawForbiddenCorrection
    boundedKernelLiteralForbiddenAssignmentIntegrand
  simp_rw [hJsum]
  rw [show (∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
        (boundedKernelBranchProfileProduct M hM K.shape x q *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l)) =
      boundedKernelBranchProfileProduct M hM K.shape x q *
        ∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring]
  apply congrArg (fun z : ℂ ↦
    boundedKernelBranchProfileProduct M hM K.shape x q * z)
  have hscale (J : Finset (BoundedKernelForbiddenLengthWitness K)) :
      (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin K.shape.2.1.val → ℕ,
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l =
        ∑' l : Fin K.shape.2.1.val → ℕ,
          (-1 : ℂ) ^ (J.card + 1) *
            boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l :=
    ((boundedKernelForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).tsum_mul_left _).symm
  have hswap := Summable.tsum_finsetSum
    (s := P)
    (f := fun J l ↦ (-1 : ℂ) ^ (J.card + 1) *
      boundedKernelForbiddenPatternAssignmentWeight M hM K J q x l)
    (fun J _ ↦ hsumJ J)
  simp_rw [hscale]
  rw [← hswap]
  apply tsum_congr
  intro l
  simp_rw [boundedKernelForbiddenPatternAssignmentWeight_eq_occurrenceIndicator]
  convert boundedKernelForbidden_inclusionExclusion_assignment K l (B l) using 1 <;>
    simp only [P, B]
  · apply Finset.sum_congr rfl
    intro J _hJ
    by_cases hocc : ∀ w ∈ J,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all
  · by_cases hex : ∃ w : BoundedKernelForbiddenLengthWitness K,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) <;> simp_all

/-- The literal admissible all-length series is exactly the marked-path
resolvent product minus the finite forbidden-pattern correction. -/
theorem boundedKernelLiteralAdmissible_eq_resolvent_sub_finiteCorrection
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) :
    boundedKernelLiteralAdmissibleAssignmentIntegrand M hM K q x =
      boundedKernelCoreResolventIntegrand M hM K.shape x q -
        boundedKernelRawForbiddenCorrection M hM K q x := by
  have hsplit := boundedKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    M hM K q x r hr hr1 hprofile
  rw [← boundedKernelCoreResolventIntegrand_eq_literalUnrestricted
      M hM K q x r hr hr1 hprofile,
    ← boundedKernelRawForbiddenCorrection_eq_literalForbidden
      M hM K q x r hr hr1 hprofile] at hsplit
  exact eq_sub_of_add_eq hsplit

/-! ## Cubic normalization and the extra fold coordinate -/

/-- Pole-removed admissible amplitude for one bounded kernel. -/
def boundedKernelAdmissibleNormalizedCoreIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  boundedKernelNormalizedCoreIntegrand M hM K.shape x q -
    boundedKernelNormalizedForbiddenCorrection M hM K q x

theorem boundedKernelAdmissibleNormalizedCoreIntegrand_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x)
      (0, 0) :=
  (boundedKernelNormalizedCoreIntegrand_analytic M hM K.shape x).sub
    (boundedKernelNormalizedForbiddenCorrection_analytic M hM K x)

/-- On the punctured strict-subcritical germ, the analytic amplitude is the
edge-pole normalization of the literal admissible assignment series. -/
theorem boundedKernelAdmissibleNormalized_eq_pow_mul_literal
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ∀ r : ℝ, 0 ≤ r → r < 1 →
        (∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) → q.2 ≠ 0 →
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x =
          q.2 ^ K.shape.2.1.val *
            boundedKernelLiteralAdmissibleAssignmentIntegrand
              M hM K q x := by
  filter_upwards
    [boundedKernelNormalizedCoreIntegrand_eq_pow_mul_resolvent
      M hM K.shape x,
     boundedKernelNormalizedForbiddenCorrection_eq_pow_mul_raw
      M hM K x] with q hcore hforbidden
  intro r hr hr1 hprofile hX
  unfold boundedKernelAdmissibleNormalizedCoreIntegrand
  rw [hcore hX, hforbidden hX,
    boundedKernelLiteralAdmissible_eq_resolvent_sub_finiteCorrection
      M hM K q x r hr hr1 hprofile]
  ring

/-- Canonical jointly analytic remainder after cubic normalization of one
strictly noncubic bounded kernel. -/
def boundedKernelAdmissibleCubicDefectRemainder
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) : ℂ :=
  q.2 ^ (3 * ell - K.shape.2.1.val - 1) *
    boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x

theorem boundedKernelAdmissibleCubicDefectRemainder_analytic
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (x : Fin K.shape.1.val → S) :
    AnalyticAt ℂ (fun q ↦
      boundedKernelAdmissibleCubicDefectRemainder M hM K q x)
      (0, 0) :=
  (analyticAt_snd.pow (3 * ell - K.shape.2.1.val - 1)).mul
    (boundedKernelAdmissibleNormalizedCoreIntegrand_analytic M hM K x)

/-- A strict edge deficit leaves one explicit fold coordinate after cubic
normalization, on the whole joint parameter space. -/
theorem boundedKernel_cubicNormalizedAdmissible_eq_X_mul_remainder
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledBoundedKernel ell)
    (hedges : K.shape.2.1.val < 3 * ell)
    (q : C(S, ℂ) × ℂ) (x : Fin K.shape.1.val → S) :
    q.2 ^ (3 * ell - K.shape.2.1.val) *
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM K q x =
      q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM K q x := by
  have hsucc :
      3 * ell - K.shape.2.1.val - 1 + 1 =
        3 * ell - K.shape.2.1.val := by
    omega
  unfold boundedKernelAdmissibleCubicDefectRemainder
  have hpow :
      q.2 ^ (3 * ell - K.shape.2.1.val) =
        q.2 ^ (3 * ell - K.shape.2.1.val - 1) * q.2 := by
    conv_lhs => rw [← hsucc, pow_succ]
  rw [hpow]
  ring

/-- Specialized no-interface statement for one fixed connected noncubic
bounded kernel.  It is intentionally a kernel/length-profile theorem, not a
claim about the total graph series. -/
theorem connectedNoncubicKernel_cubicNormalizedAdmissible_eq_X_mul
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (x : Fin K.1.toLabelledBoundedKernel.shape.1.val → S) :
    q.2 ^ (3 * ell -
        K.1.toLabelledBoundedKernel.shape.2.1.val) *
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM
          K.1.toLabelledBoundedKernel q x =
      q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM
        K.1.toLabelledBoundedKernel q x :=
  boundedKernel_cubicNormalizedAdmissible_eq_X_mul_remainder
    M hM K.1.toLabelledBoundedKernel K.2 q x

/-- On the punctured strict-subcritical germ, the preceding identity is the
literal cubic normalization `X^(3*ell)` of the admissible all-length
assignment series. -/
theorem connectedNoncubicKernel_literal_cubicNormalization
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedNoncubicKernel ell)
    (x : Fin K.1.toLabelledBoundedKernel.shape.1.val → S) :
    ∀ᶠ q : C(S, ℂ) × ℂ in 𝓝 (0, 0),
      ∀ r : ℝ, 0 ≤ r → r < 1 →
        (∀ y, ‖NBKAS_MPR.profile M hM q y‖ ≤ r) → q.2 ≠ 0 →
        q.2 ^ (3 * ell) *
            boundedKernelLiteralAdmissibleAssignmentIntegrand M hM
              K.1.toLabelledBoundedKernel q x =
          q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM
            K.1.toLabelledBoundedKernel q x := by
  filter_upwards
    [boundedKernelAdmissibleNormalized_eq_pow_mul_literal
      M hM K.1.toLabelledBoundedKernel x] with q hnormalized
  intro r hr hr1 hprofile hX
  let B := K.1.toLabelledBoundedKernel
  have hsum :
      3 * ell = (3 * ell - B.shape.2.1.val) + B.shape.2.1.val := by
    omega
  have hpow :
      q.2 ^ (3 * ell) =
        q.2 ^ (3 * ell - B.shape.2.1.val) * q.2 ^ B.shape.2.1.val := by
    calc
      q.2 ^ (3 * ell) =
          q.2 ^ ((3 * ell - B.shape.2.1.val) + B.shape.2.1.val) :=
        congrArg (fun n : ℕ ↦ q.2 ^ n) hsum
      _ = q.2 ^ (3 * ell - B.shape.2.1.val) *
          q.2 ^ B.shape.2.1.val := pow_add _ _ _
  calc
    q.2 ^ (3 * ell) *
        boundedKernelLiteralAdmissibleAssignmentIntegrand M hM B q x =
      q.2 ^ (3 * ell - B.shape.2.1.val) *
        (q.2 ^ B.shape.2.1.val *
          boundedKernelLiteralAdmissibleAssignmentIntegrand M hM B q x) := by
        rw [hpow]
        ring
    _ = q.2 ^ (3 * ell - B.shape.2.1.val) *
        boundedKernelAdmissibleNormalizedCoreIntegrand M hM B q x := by
      rw [← hnormalized r hr hr1 hprofile hX]
    _ = q.2 * boundedKernelAdmissibleCubicDefectRemainder M hM B q x :=
      boundedKernel_cubicNormalizedAdmissible_eq_X_mul_remainder
        M hM B K.2 q x

end PerronWright.GraphCore
