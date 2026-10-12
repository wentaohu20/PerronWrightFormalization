import PerronWright.Enumeration.CubicForbiddenAnalyticCorrection
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Nat.Choose.Sum

/-!
# Literal length-assignment meaning of the cubic forbidden correction

The analytic correction in `CubicForbiddenAnalyticCorrection` is a finite
inclusion--exclusion sum of resolvent cylinders.  This file proves that this
is not merely a convenient definition: on every strict-subcritical profile
ball it is exactly the sum over the literal forbidden length assignments.

There are three ingredients, all proved here from the preceding concrete
objects.

* A finite product of absolutely summable one-edge series is the `tsum` over
  the full finite length table.
* A compatible witness intersection is the product in which precisely its
  forced edge lengths are frozen; an incompatible intersection is empty.
* For a fixed length table, inclusion--exclusion over the finite set of
  witnesses which actually occur has value one exactly when that set is
  nonempty.

Thus the raw forbidden correction is identified with a genuine forbidden
assignment `tsum`, before integration and before the outer finite cubic
kernel sum.  No analytic or combinatorial interface is assumed.
-/

open MeasureTheory PerronWright
open scoped Classical Topology BigOperators

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-! ## A finite product of absolutely summable scalar series -/

/-- The absolutely convergent finite Fubini identity needed below.  It is
stated for `Fin n`, exactly the edge-label type of a labelled cubic kernel. -/
theorem summable_finFunction_prod_and_tsum
    {A : Type*} [NormedCommRing A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [CompleteSpace A]
    {n : ℕ} (f : (i : Fin n) → ℕ → A)
    (hf : ∀ i, Summable (f i)) :
    Summable (fun a : Fin n → ℕ ↦ ∏ i, f i (a i)) ∧
      (∑' a : Fin n → ℕ, ∏ i, f i (a i)) =
        ∏ i, ∑' m : ℕ, f i m := by
  induction n with
  | zero =>
      constructor
      · exact Summable.of_finite
      · simp
  | succ n ih =>
      let fInit : (i : Fin n) → ℕ → A := fun i ↦ f i.castSucc
      let fLast : ℕ → A := f (Fin.last n)
      let F : (Fin n → ℕ) → A := fun a ↦ ∏ i, fInit i (a i)
      let e : (Fin (n + 1) → ℕ) ≃ (Fin n → ℕ) × ℕ :=
        Fin.succFunEquiv ℕ n
      have hInit := ih fInit (fun i ↦ hf i.castSucc)
      have hLast : Summable fLast := hf (Fin.last n)
      have hPairNorm :
          Summable (fun p : (Fin n → ℕ) × ℕ ↦
            ‖F p.1 * fLast p.2‖) :=
        Summable.mul_norm hInit.1.norm hLast.norm
      have hPair :
          Summable (fun p : (Fin n → ℕ) × ℕ ↦
            F p.1 * fLast p.2) :=
        hPairNorm.of_norm
      have hrewrite (a : Fin (n + 1) → ℕ) :
          (∏ i, f i (a i)) = F (e a).1 * fLast (e a).2 := by
        change (∏ i : Fin (n + 1), f i (a i)) =
          (∏ i : Fin n, f (Fin.castAdd 1 i) (a (Fin.castAdd 1 i))) *
            f (Fin.natAdd n 0) (a (Fin.natAdd n 0))
        rw [Fin.prod_univ_castSucc]
        refine congrArg₂ (· * ·) ?_ ?_
        · apply Finset.prod_congr rfl
          intro i _
          congr 2
        · congr 2
      have hsum : Summable (fun a : Fin (n + 1) → ℕ ↦
          ∏ i, f i (a i)) := by
        exact (hPair.comp_injective e.injective).congr
          (fun a ↦ (hrewrite a).symm)
      refine ⟨hsum, ?_⟩
      calc
        (∑' a : Fin (n + 1) → ℕ, ∏ i, f i (a i)) =
            ∑' p : (Fin n → ℕ) × ℕ, F p.1 * fLast p.2 := by
          rw [← e.tsum_eq]
          exact tsum_congr hrewrite
        _ = (∑' a : Fin n → ℕ, F a) *
              ∑' m : ℕ, fLast m := by
          exact (tsum_mul_tsum_of_summable_norm
            hInit.1.norm hLast.norm).symm
        _ = (∏ i : Fin n, ∑' m : ℕ, f i.castSucc m) *
              ∑' m : ℕ, f (Fin.last n) m := by
          rw [hInit.2]
        _ = ∏ i : Fin (n + 1), ∑' m : ℕ, f i m := by
          rw [Fin.prod_univ_castSucc]

/-- The absolute-convergence form of
`summable_finFunction_prod_and_tsum`, valid in any complete normed
commutative ring. -/
theorem summable_norm_finFunction_prod_and_tsum
    {A : Type*} [NormedCommRing A] [CompleteSpace A]
    {n : ℕ} (f : (i : Fin n) → ℕ → A)
    (hf : ∀ i, Summable (fun m ↦ ‖f i m‖)) :
    Summable (fun a : Fin n → ℕ ↦ ‖∏ i, f i (a i)‖) ∧
      (∑' a : Fin n → ℕ, ∏ i, f i (a i)) =
        ∏ i, ∑' m : ℕ, f i m := by
  induction n with
  | zero =>
      constructor
      · exact Summable.of_finite
      · simp
  | succ n ih =>
      let fInit : (i : Fin n) → ℕ → A := fun i ↦ f i.castSucc
      let fLast : ℕ → A := f (Fin.last n)
      let F : (Fin n → ℕ) → A := fun a ↦ ∏ i, fInit i (a i)
      let e : (Fin (n + 1) → ℕ) ≃ (Fin n → ℕ) × ℕ :=
        Fin.succFunEquiv ℕ n
      have hInit := ih fInit (fun i ↦ hf i.castSucc)
      have hLast : Summable (fun m ↦ ‖fLast m‖) := hf (Fin.last n)
      have hPairNorm :
          Summable (fun p : (Fin n → ℕ) × ℕ ↦
            ‖F p.1 * fLast p.2‖) :=
        Summable.mul_norm hInit.1 hLast
      have hrewrite (a : Fin (n + 1) → ℕ) :
          (∏ i, f i (a i)) = F (e a).1 * fLast (e a).2 := by
        change (∏ i : Fin (n + 1), f i (a i)) =
          (∏ i : Fin n, f (Fin.castAdd 1 i) (a (Fin.castAdd 1 i))) *
            f (Fin.natAdd n 0) (a (Fin.natAdd n 0))
        rw [Fin.prod_univ_castSucc]
        refine congrArg₂ (· * ·) ?_ ?_
        · apply Finset.prod_congr rfl
          intro i _
          congr 2
        · congr 2
      have hsumNorm : Summable (fun a : Fin (n + 1) → ℕ ↦
          ‖∏ i, f i (a i)‖) := by
        exact (hPairNorm.comp_injective e.injective).congr
          (fun a ↦ congrArg norm (hrewrite a).symm)
      refine ⟨hsumNorm, ?_⟩
      calc
        (∑' a : Fin (n + 1) → ℕ, ∏ i, f i (a i)) =
            ∑' p : (Fin n → ℕ) × ℕ, F p.1 * fLast p.2 := by
          rw [← e.tsum_eq]
          exact tsum_congr hrewrite
        _ = (∑' a : Fin n → ℕ, F a) *
              ∑' m : ℕ, fLast m := by
          exact (tsum_mul_tsum_of_summable_norm
            hInit.1 hLast).symm
        _ = (∏ i : Fin n, ∑' m : ℕ, f i.castSucc m) *
              ∑' m : ℕ, f (Fin.last n) m := by
          rw [hInit.2]
        _ = ∏ i : Fin (n + 1), ∑' m : ℕ, f i m := by
          rw [Fin.prod_univ_castSucc]

/-! ## Witness patterns as literal constraints -/

/-- A concrete witness occurs exactly when the assignment takes every value
forced by that witness. -/
theorem cubicForbiddenWitness_occurs_iff_forcedValues
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (w : CubicKernelForbiddenLengthWitness H)
    (l : Fin (3 * ell) → ℕ) :
    w.Occurs (Finsupp.equivFunOnFinite.symm l) ↔
      ∀ e n, n ∈ cubicForbiddenWitnessForcedValues w e → l e = n := by
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
      · have hn0 : n = 0 := by simpa only [if_pos he, Finset.mem_singleton] using hn
        rcases he with rfl | rfl
        · simpa only [hn0] using hfirst
        · simpa only [hn0] using hsecond
      · simp [he] at hn
    · intro hall
      constructor
      · exact hall w.first 0 (by simp)
      · exact hall w.second 0 (by simp)

theorem cubicForbiddenPatternLength_mem
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (J : Finset (CubicKernelForbiddenLengthWitness H))
    (e : Fin (3 * ell)) (he : CubicForbiddenPatternForcesEdge J e) :
    cubicForbiddenPatternLength J e ∈
      cubicForbiddenPatternForcedValues J e := by
  change (cubicForbiddenPatternForcedValues J e).Nonempty at he
  simp only [cubicForbiddenPatternLength, dif_pos he]
  exact Finset.min'_mem _ he

theorem cubicForbiddenPattern_eq_length_of_mem
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    {J : Finset (CubicKernelForbiddenLengthWitness H)}
    (hJ : CubicForbiddenPatternCompatible J)
    {e : Fin (3 * ell)} {n : ℕ}
    (hn : n ∈ cubicForbiddenPatternForcedValues J e) :
    n = cubicForbiddenPatternLength J e := by
  exact (Finset.card_le_one_iff.mp (hJ e)) hn
    (cubicForbiddenPatternLength_mem J e ⟨n, hn⟩)

/-- Simultaneous occurrence of all witnesses in a pattern is equivalent to
compatibility plus the resulting finite list of forced edge equalities. -/
theorem cubicForbiddenPattern_all_occurs_iff
    {ell : ℕ} {H : PerronWright.FiniteMultiGraph (2 * ell) (3 * ell)}
    (J : Finset (CubicKernelForbiddenLengthWitness H))
    (l : Fin (3 * ell) → ℕ) :
    (∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)) ↔
      CubicForbiddenPatternCompatible J ∧
        ∀ e, CubicForbiddenPatternForcesEdge J e →
          l e = cubicForbiddenPatternLength J e := by
  constructor
  · intro hall
    have hcompat : CubicForbiddenPatternCompatible J := by
      intro e
      rw [Finset.card_le_one_iff]
      intro m n hm hn
      change m ∈ J.biUnion (fun w ↦ cubicForbiddenWitnessForcedValues w e) at hm
      change n ∈ J.biUnion (fun w ↦ cubicForbiddenWitnessForcedValues w e) at hn
      rw [Finset.mem_biUnion] at hm hn
      obtain ⟨wm, hwmJ, hwm⟩ := hm
      obtain ⟨wn, hwnJ, hwn⟩ := hn
      have hm' :=
        (cubicForbiddenWitness_occurs_iff_forcedValues wm l).mp
          (hall wm hwmJ) e m hwm
      have hn' :=
        (cubicForbiddenWitness_occurs_iff_forcedValues wn l).mp
          (hall wn hwnJ) e n hwn
      exact hm'.symm.trans hn'
    refine ⟨hcompat, ?_⟩
    intro e he
    have hlen := cubicForbiddenPatternLength_mem J e he
    change cubicForbiddenPatternLength J e ∈
      J.biUnion (fun w ↦ cubicForbiddenWitnessForcedValues w e) at hlen
    rw [Finset.mem_biUnion] at hlen
    obtain ⟨w, hwJ, hwlen⟩ := hlen
    exact (cubicForbiddenWitness_occurs_iff_forcedValues w l).mp
      (hall w hwJ) e _ hwlen
  · rintro ⟨hcompat, hlength⟩ w hwJ
    rw [cubicForbiddenWitness_occurs_iff_forcedValues]
    intro e n hn
    have hnPattern : n ∈ cubicForbiddenPatternForcedValues J e := by
      change n ∈ J.biUnion (fun u ↦ cubicForbiddenWitnessForcedValues u e)
      rw [Finset.mem_biUnion]
      exact ⟨w, hwJ, hn⟩
    have he : CubicForbiddenPatternForcesEdge J e := ⟨n, hnPattern⟩
    exact (hlength e he).trans
      (cubicForbiddenPattern_eq_length_of_mem hcompat hnPattern).symm

/-! ## Factorization of one literal witness intersection -/

/-- The one-edge coefficient sequence with the length frozen when the
pattern forces that edge. -/
def cubicForbiddenPatternEdgeCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S) (n : ℕ) : ℂ :=
  if CubicForbiddenPatternForcesEdge J e then
    if n = cubicForbiddenPatternLength J e then
      profilePathEdgeCoefficient M (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    else 0
  else
    profilePathEdgeCoefficient M (MPR.profile M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n

theorem cubicForbiddenPatternEdgeCoefficient_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (cubicForbiddenPatternEdgeCoefficient M hM K J e q x) := by
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    have hs := (hasSum_ite_eq (cubicForbiddenPatternLength J e)
      (c (cubicForbiddenPatternLength J e))).summable
    exact hs.congr (fun n ↦ by
      by_cases hn : n = cubicForbiddenPatternLength J e
      · subst n
        simp [cubicForbiddenPatternEdgeCoefficient, he, c]
      · simp [cubicForbiddenPatternEdgeCoefficient, he, hn, c])
  · exact (summable_profilePathEdgeCoefficient M hM
      (MPR.profile M hM q) r hr hr1 hprofile
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2)).congr
        (fun n ↦ by simp [cubicForbiddenPatternEdgeCoefficient, he])

theorem tsum_cubicForbiddenPatternEdgeCoefficient
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (e : Fin (3 * ell)) (q : C(S, ℂ) × ℂ)
    (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    (∑' n : ℕ,
        cubicForbiddenPatternEdgeCoefficient M hM K J e q x n) =
      cubicForbiddenRawPatternEdgeFunction M hM K J e q x := by
  classical
  by_cases he : CubicForbiddenPatternForcesEdge J e
  · let c : ℕ → ℂ := fun n ↦
      profilePathEdgeCoefficient M (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) n
    calc
      (∑' n : ℕ,
          cubicForbiddenPatternEdgeCoefficient M hM K J e q x n) =
          c (cubicForbiddenPatternLength J e) := by
        calc
          _ = ∑' n : ℕ, if n = cubicForbiddenPatternLength J e then
              c (cubicForbiddenPatternLength J e) else 0 := by
            apply tsum_congr
            intro n
            by_cases hn : n = cubicForbiddenPatternLength J e
            · subst n
              simp [cubicForbiddenPatternEdgeCoefficient, he, c]
            · simp [cubicForbiddenPatternEdgeCoefficient, he, hn, c]
          _ = c (cubicForbiddenPatternLength J e) :=
            (hasSum_ite_eq (cubicForbiddenPatternLength J e)
              (c (cubicForbiddenPatternLength J e))).tsum_eq
      _ = cubicForbiddenRawPatternEdgeFunction M hM K J e q x := by
        simp [cubicForbiddenRawPatternEdgeFunction, he, c]
  · have hsum := tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
      M hM q r hr hr1 hprofile
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2)
    rw [show (∑' n : ℕ,
        cubicForbiddenPatternEdgeCoefficient M hM K J e q x n) =
        ∑' n : ℕ, profilePathEdgeCoefficient M (MPR.profile M hM q)
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) n by
      apply tsum_congr
      intro n
      simp [cubicForbiddenPatternEdgeCoefficient, he]]
    rw [tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
      M hM q r hr hr1 hprofile]
    unfold cubicForbiddenRawPatternEdgeFunction
    rw [if_neg he]
    change (MPR.pathResolventKernel M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2) =
      (MPR.pathResolventKernel M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1,
        x (cubicKernelOrderedEndpoints K.graph e).2)
    rfl

/-- A pattern-restricted table weight.  The outer compatibility test makes
an inconsistent witness intersection literally empty. -/
def cubicForbiddenPatternAssignmentWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (l : Fin (3 * ell) → ℕ) : ℂ :=
  if CubicForbiddenPatternCompatible J then
    ∏ e : Fin (3 * ell),
      cubicForbiddenPatternEdgeCoefficient M hM K J e q x (l e)
  else 0

/-- The frozen-edge description agrees pointwise with the literal
simultaneous-occurrence indicator. -/
theorem cubicForbiddenPatternAssignmentWeight_eq_occurrenceIndicator
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (l : Fin (3 * ell) → ℕ) :
    cubicForbiddenPatternAssignmentWeight M hM K J q x l =
      if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M (MPR.profile M hM q)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0 := by
  classical
  by_cases hall :
      ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
  · obtain ⟨hcompat, hlength⟩ :=
      (cubicForbiddenPattern_all_occurs_iff J l).mp hall
    rw [if_pos hall]
    unfold cubicForbiddenPatternAssignmentWeight
    rw [if_pos hcompat]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : CubicForbiddenPatternForcesEdge J e
    · simp [cubicForbiddenPatternEdgeCoefficient, he, hlength e he]
    · simp [cubicForbiddenPatternEdgeCoefficient, he]
  · rw [if_neg hall]
    unfold cubicForbiddenPatternAssignmentWeight
    by_cases hcompat : CubicForbiddenPatternCompatible J
    · rw [if_pos hcompat]
      have hnot : ¬ ∀ e, CubicForbiddenPatternForcesEdge J e →
          l e = cubicForbiddenPatternLength J e := by
        intro hlength
        exact hall ((cubicForbiddenPattern_all_occurs_iff J l).mpr
          ⟨hcompat, hlength⟩)
      push Not at hnot
      obtain ⟨e, he, hne⟩ := hnot
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [cubicForbiddenPatternEdgeCoefficient, he, hne]
    · simp [hcompat]

theorem cubicForbiddenPatternAssignmentWeight_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (cubicForbiddenPatternAssignmentWeight M hM K J q x) := by
  classical
  by_cases hcompat : CubicForbiddenPatternCompatible J
  · exact (summable_finFunction_prod_and_tsum
        (fun e n ↦ cubicForbiddenPatternEdgeCoefficient
          M hM K J e q x n)
        (fun e ↦ cubicForbiddenPatternEdgeCoefficient_summable
          M hM K J e q x r hr hr1 hprofile)).1.congr
      (fun l ↦ by simp [cubicForbiddenPatternAssignmentWeight, hcompat])
  · exact summable_zero.congr
      (fun l ↦ by simp [cubicForbiddenPatternAssignmentWeight, hcompat])

theorem tsum_cubicForbiddenPatternAssignmentWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (J : Finset (CubicKernelForbiddenLengthWitness K.graph))
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r)
    (hcompat : CubicForbiddenPatternCompatible J) :
    (∑' l : Fin (3 * ell) → ℕ,
        cubicForbiddenPatternAssignmentWeight M hM K J q x l) =
      ∏ e : Fin (3 * ell),
        cubicForbiddenRawPatternEdgeFunction M hM K J e q x := by
  classical
  simp only [cubicForbiddenPatternAssignmentWeight, hcompat, if_true]
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ cubicForbiddenPatternEdgeCoefficient
      M hM K J e q x n)
    (fun e ↦ cubicForbiddenPatternEdgeCoefficient_summable
      M hM K J e q x r hr hr1 hprofile)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_cubicForbiddenPatternEdgeCoefficient
    M hM K J e q x r hr hr1 hprofile

/-! ## Pointwise finite inclusion--exclusion -/

private theorem sum_nonempty_powerset_neg_one_pow_card_add_one
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

/-- For one length table, the finite inclusion--exclusion coefficient is
the indicator that at least one concrete forbidden witness occurs. -/
theorem cubicForbidden_inclusionExclusion_assignment
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (l : Fin (3 * ell) → ℕ) (z : ℂ) :
    letI := cubicKernelForbiddenLengthWitnessFintype K.graph
    (∑ J ∈ (Finset.univ :
        Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
          Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1) *
        (if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
          then z else 0)) =
      if ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then z else 0 := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  classical
  let W : Finset (CubicKernelForbiddenLengthWitness K.graph) :=
    Finset.univ.filter fun w ↦
      w.Occurs (Finsupp.equivFunOnFinite.symm l)
  by_cases hW : W.Nonempty
  · have hex : ∃ w : CubicKernelForbiddenLengthWitness K.graph,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) := by
      obtain ⟨w, hw⟩ := hW
      exact ⟨w, (Finset.mem_filter.mp hw).2⟩
    rw [if_pos hex]
    have hfilter :
        ((Finset.univ :
            Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
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
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hOuter.2 w hw⟩
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
          Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
            Finset.Nonempty,
        (-1 : ℂ) ^ (J.card + 1) *
          (if ∀ w ∈ J, w.Occurs (Finsupp.equivFunOnFinite.symm l)
            then z else 0)) =
          ∑ J ∈ (Finset.univ :
              Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
                Finset.Nonempty,
            if (∀ w ∈ J,
                w.Occurs (Finsupp.equivFunOnFinite.symm l)) then
              (-1 : ℂ) ^ (J.card + 1) * z else 0 := by
        apply Finset.sum_congr rfl
        intro J hJ
        by_cases hocc : ∀ w ∈ J,
            w.Occurs (Finsupp.equivFunOnFinite.symm l)
        · simp
        · simp
      _ = ∑ J ∈ ((Finset.univ :
              Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
                Finset.Nonempty).filter (fun J ↦ ∀ w ∈ J,
                  w.Occurs (Finsupp.equivFunOnFinite.symm l)),
            (-1 : ℂ) ^ (J.card + 1) * z := by
        have hsf :
            (∑ J ∈ ((Finset.univ :
                Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
                  Finset.Nonempty).filter (fun J ↦ ∀ w ∈ J,
                    w.Occurs (Finsupp.equivFunOnFinite.symm l)),
              (-1 : ℂ) ^ (J.card + 1) * z) =
            ∑ J ∈ (Finset.univ :
                Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
                  Finset.Nonempty,
              if (∀ w ∈ J,
                  w.Occurs (Finsupp.equivFunOnFinite.symm l)) then
                (-1 : ℂ) ^ (J.card + 1) * z else 0 := by
          rw [Finset.sum_filter]
        exact hsf.symm
      _ = ∑ J ∈ W.powerset.filter Finset.Nonempty,
            (-1 : ℂ) ^ (J.card + 1) * z := by rw [hfilter]
      _ = (∑ J ∈ W.powerset.filter Finset.Nonempty,
            (-1 : ℂ) ^ (J.card + 1)) * z := by
        rw [Finset.sum_mul]
      _ = z := by
        rw [sum_nonempty_powerset_neg_one_pow_card_add_one W hW, one_mul]
  · have hnex : ¬ ∃ w : CubicKernelForbiddenLengthWitness K.graph,
        w.Occurs (Finsupp.equivFunOnFinite.symm l) := by
      rintro ⟨w, hw⟩
      exact hW ⟨w, by simp [W, hw]⟩
    rw [if_neg hnex]
    apply Finset.sum_eq_zero
    intro J hJ
    have hne : J.Nonempty := by
      exact (Finset.mem_filter.mp hJ).2
    obtain ⟨w, hw⟩ := hne
    have hnot : ¬ ∀ u ∈ J,
        u.Occurs (Finsupp.equivFunOnFinite.symm l) := by
      intro hall
      exact hnex ⟨w, hall w hw⟩
    rw [if_neg hnot, mul_zero]

/-! ## The raw correction is the literal forbidden assignment sum -/

/-- Literal pointwise forbidden length-assignment sum for one labelled
cubic kernel. -/
def cubicKernelLiteralForbiddenAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) : ℂ :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q x *
    ∑' l : Fin (3 * ell) → ℕ,
      if ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M (MPR.profile M hM q)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0

/-- Pointwise, the finite raw inclusion--exclusion sum is the literal
forbidden-assignment sum. -/
theorem cubicKernelRawForbiddenCorrection_eq_literalAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    letI := cubicKernelForbiddenLengthWitnessFintype K.graph
    (∑ J ∈ (Finset.univ :
        Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
          Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1) *
        cubicForbiddenRawIntersectionFunction M hM K J q x) =
      cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q x := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  classical
  let P := (Finset.univ :
    Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
      Finset.Nonempty
  let B : (Fin (3 * ell) → ℕ) → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
  have hJsum (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      cubicForbiddenRawIntersectionFunction M hM K J q x =
        cubicKernelBranchProfileFunction M hM (ell := ell) q x *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l := by
    unfold cubicForbiddenRawIntersectionFunction
    by_cases hcompat : CubicForbiddenPatternCompatible J
    · rw [if_pos hcompat,
          tsum_cubicForbiddenPatternAssignmentWeight
            M hM K J q x r hr hr1 hprofile hcompat]
      rw [ContinuousMap.mul_apply, ContinuousMap.prod_apply]
    · rw [if_neg hcompat]
      have hzero :
          (∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l) = 0 := by
        simp [cubicForbiddenPatternAssignmentWeight, hcompat]
      rw [hzero, mul_zero]
      rfl
  have hsumJ (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      Summable (fun l : Fin (3 * ell) → ℕ ↦
        (-1 : ℂ) ^ (J.card + 1) *
          cubicForbiddenPatternAssignmentWeight M hM K J q x l) :=
    (cubicForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).mul_left _
  unfold cubicKernelLiteralForbiddenAssignmentIntegrand
  simp_rw [hJsum]
  rw [show (∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
        ((cubicKernelBranchProfileFunction M hM (ell := ell) q) x *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l)) =
      (cubicKernelBranchProfileFunction M hM (ell := ell) q) x *
        ∑ J ∈ P, (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J _
      ring]
  have hswap := Summable.tsum_finsetSum
    (s := P)
    (f := fun J l ↦ (-1 : ℂ) ^ (J.card + 1) *
      cubicForbiddenPatternAssignmentWeight M hM K J q x l)
    (fun J _ ↦ hsumJ J)
  have hscale (J : Finset (CubicKernelForbiddenLengthWitness K.graph)) :
      (-1 : ℂ) ^ (J.card + 1) *
          ∑' l : Fin (3 * ell) → ℕ,
            cubicForbiddenPatternAssignmentWeight M hM K J q x l =
        ∑' l : Fin (3 * ell) → ℕ,
          (-1 : ℂ) ^ (J.card + 1) *
            cubicForbiddenPatternAssignmentWeight M hM K J q x l :=
    ((cubicForbiddenPatternAssignmentWeight_summable
      M hM K J q x r hr hr1 hprofile).tsum_mul_left _).symm
  simp_rw [hscale]
  rw [← hswap]
  apply congrArg (fun z : ℂ ↦
    cubicKernelBranchProfileFunction M hM (ell := ell) q x * z)
  apply tsum_congr
  intro l
  simp_rw [cubicForbiddenPatternAssignmentWeight_eq_occurrenceIndicator]
  have hIE := cubicForbidden_inclusionExclusion_assignment K l (B l)
  convert hIE using 1 <;> simp only [P, B]
  · apply Finset.sum_congr rfl
    intro J _
    congr 1
    by_cases hocc : ∀ w ∈ J,
        w.Occurs (Finsupp.equivFunOnFinite.symm l)
    · simp
    · simp
  · by_cases hex : ∃ w : CubicKernelForbiddenLengthWitness K.graph,
        w.Occurs (Finsupp.equivFunOnFinite.symm l)
    · simp [hex]
    · simp [hex]

/-- After integration, the already defined raw analytic correction is
exactly the integral of the literal forbidden length-assignment `tsum`. -/
theorem cubicKernelIntegratedRawForbiddenCorrection_eq_literalAssignmentIntegral
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelIntegratedRawForbiddenCorrection M hM K q =
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell := by
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  classical
  unfold cubicKernelIntegratedRawForbiddenCorrection
    cubicKernelIntegratedRawForbiddenIntersection
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, cubicKernelIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  exact cubicKernelRawForbiddenCorrection_eq_literalAssignmentIntegrand
    M hM K q x r hr hr1 hprofile

/-! ## The complementary literal admissible sum -/

/-- Literal unrestricted table sum for one labelled cubic kernel. -/
def cubicKernelLiteralUnrestrictedAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) : ℂ :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q x *
    ∑' l : Fin (3 * ell) → ℕ,
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M (MPR.profile M hM q)
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)

/-- Literal admissible table sum, with the exact loop and zero-parallel-edge
conditions from `CubicKernelLengthAssignment.IsAdmissible`. -/
def cubicKernelLiteralAdmissibleAssignmentIntegrand
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S) : ℂ :=
  cubicKernelBranchProfileFunction M hM (ell := ell) q x *
    ∑' l : Fin (3 * ell) → ℕ,
      if CubicKernelLengthAssignment.IsAdmissible K.graph
          (Finsupp.equivFunOnFinite.symm l) then
        ∏ e : Fin (3 * ell),
          profilePathEdgeCoefficient M (MPR.profile M hM q)
            (x (cubicKernelOrderedEndpoints K.graph e).1)
            (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
      else 0

private theorem cubicKernelAssignmentProduct_summable
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    Summable (fun l : Fin (3 * ell) → ℕ ↦
      ∏ e : Fin (3 * ell),
        profilePathEdgeCoefficient M (MPR.profile M hM q)
          (x (cubicKernelOrderedEndpoints K.graph e).1)
          (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)) := by
  exact (summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M (MPR.profile M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (MPR.profile M hM q) r hr hr1 hprofile _ _)).1

/-- The unrestricted marked-path resolvent product is the literal `tsum`
over all finite edge-length tables. -/
theorem cubicKernelResolventIntegrandFunction_eq_literalUnrestricted
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelResolventIntegrandFunction M hM K q x =
      cubicKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  rw [cubicKernelResolventIntegrandFunction_apply]
  unfold cubicKernelResolventIntegrand
    cubicKernelLiteralUnrestrictedAssignmentIntegrand
  rw [cubicKernelBranchProfileFunction_apply]
  apply congrArg (fun z : ℂ ↦
    cubicKernelBranchProfileProduct M hM x q * z)
  rw [(summable_finFunction_prod_and_tsum
    (fun e n ↦ profilePathEdgeCoefficient M (MPR.profile M hM q)
      (x (cubicKernelOrderedEndpoints K.graph e).1)
      (x (cubicKernelOrderedEndpoints K.graph e).2) n)
    (fun e ↦ summable_profilePathEdgeCoefficient M hM
      (MPR.profile M hM q) r hr hr1 hprofile _ _)).2]
  apply Finset.prod_congr rfl
  intro e _
  exact tsum_profilePathEdgeCoefficient_eq_pathResolventKernel
    M hM q r hr hr1 hprofile _ _ |>.symm

/-- Literal admissible and forbidden tables partition the unrestricted
table sum.  Absolute summability justifies the two subseries. -/
theorem cubicKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ) (x : Fin (2 * ell) → S)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x +
        cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q x =
      cubicKernelLiteralUnrestrictedAssignmentIntegrand M hM K q x := by
  classical
  let B : (Fin (3 * ell) → ℕ) → ℂ := fun l ↦
    ∏ e : Fin (3 * ell),
      profilePathEdgeCoefficient M (MPR.profile M hM q)
        (x (cubicKernelOrderedEndpoints K.graph e).1)
        (x (cubicKernelOrderedEndpoints K.graph e).2) (l e)
  let A : Set (Fin (3 * ell) → ℕ) := {l |
    CubicKernelLengthAssignment.IsAdmissible K.graph
      (Finsupp.equivFunOnFinite.symm l)}
  let F : Set (Fin (3 * ell) → ℕ) := {l |
    ∃ w : CubicKernelForbiddenLengthWitness K.graph,
      w.Occurs (Finsupp.equivFunOnFinite.symm l)}
  have hB : Summable B :=
    cubicKernelAssignmentProduct_summable M hM K q x r hr hr1 hprofile
  have hA : Summable (A.indicator B) := hB.indicator A
  have hF : Summable (F.indicator B) := hB.indicator F
  have hterm (l : Fin (3 * ell) → ℕ) :
      A.indicator B l + F.indicator B l = B l := by
    have hiff := not_cubicKernelLengthAssignment_admissible_iff K.graph
      (Finsupp.equivFunOnFinite.symm l)
    by_cases ha : CubicKernelLengthAssignment.IsAdmissible K.graph
        (Finsupp.equivFunOnFinite.symm l)
    · have hf : ¬ ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) := by
        exact fun hw ↦ (hiff.mpr hw) ha
      have hAl : l ∈ A := by simpa [A] using ha
      have hFl : l ∉ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
    · have hf : ∃ w : CubicKernelForbiddenLengthWitness K.graph,
          w.Occurs (Finsupp.equivFunOnFinite.symm l) := hiff.mp ha
      have hAl : l ∉ A := by simpa [A] using ha
      have hFl : l ∈ F := by simpa [F] using hf
      simp [Set.indicator, hAl, hFl]
  unfold cubicKernelLiteralAdmissibleAssignmentIntegrand
    cubicKernelLiteralForbiddenAssignmentIntegrand
    cubicKernelLiteralUnrestrictedAssignmentIntegrand
  rw [← mul_add]
  apply congrArg (fun z : ℂ ↦
    cubicKernelBranchProfileFunction M hM (ell := ell) q x * z)
  change (∑' l, A.indicator B l) + (∑' l, F.indicator B l) = ∑' l, B l
  rw [← hA.tsum_add hF]
  exact tsum_congr hterm

/-- The fixed-kernel admissible resolvent contribution is an integral of the
literal admissible length-assignment `tsum`. -/
theorem cubicKernelIntegratedResolvent_sub_rawForbidden_eq_literalAdmissible
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (K : LabelledConnectedCubicKernel ell)
    (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    cubicKernelIntegratedResolventProduct M hM K q -
        cubicKernelIntegratedRawForbiddenCorrection M hM K q =
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell := by
  rw [cubicKernelIntegratedRawForbiddenCorrection_eq_literalAssignmentIntegral
    M hM K q r hr hr1 hprofile]
  unfold cubicKernelIntegratedResolventProduct
  rw [cubicKernelIntegralCLM_apply]
  have hf : Integrable
      (⇑(cubicKernelResolventIntegrandFunction M hM K q))
      (cubicKernelProductMeasure M ell) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (cubicKernelResolventIntegrandFunction M hM K q).continuous
    · exact isClosed_closure.isCompact
  let _ := cubicKernelForbiddenLengthWitnessFintype K.graph
  let G : C((Fin (2 * ell) → S), ℂ) :=
    ∑ J ∈ (Finset.univ :
        Finset (CubicKernelForbiddenLengthWitness K.graph)).powerset.filter
          Finset.Nonempty,
      (-1 : ℂ) ^ (J.card + 1) •
        cubicForbiddenRawIntersectionFunction M hM K J q
  have hG : Integrable (G : (Fin (2 * ell) → S) → ℂ)
      (cubicKernelProductMeasure M ell) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact G.continuous
    · exact isClosed_closure.isCompact
  have hg : Integrable
      (cubicKernelLiteralForbiddenAssignmentIntegrand M hM K q)
      (cubicKernelProductMeasure M ell) := by
    apply hG.congr
    filter_upwards [] with x
    have hx := cubicKernelRawForbiddenCorrection_eq_literalAssignmentIntegrand
      M hM K q x r hr hr1 hprofile
    simpa only [G, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul] using hx
  rw [← integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [cubicKernelResolventIntegrandFunction_eq_literalUnrestricted
    M hM K q x r hr hr1 hprofile]
  have hsplit := cubicKernelLiteralAdmissible_add_forbidden_eq_unrestricted
    M hM K q x r hr hr1 hprofile
  exact sub_eq_iff_eq_add.mpr hsplit.symm

/-- Exact finite inverse-multiplicity sum of the literal admissible
assignment integrals. -/
def positiveSurplusCubicLiteralAdmissibleResolventSum
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ) : ℂ :=
  letI := labelledConnectedCubicKernelFintype ell
  ∑ K : LabelledConnectedCubicKernel ell,
    labelledCubicKernelInverseMultiplicity K *
      ∫ x : Fin (2 * ell) → S,
        cubicKernelLiteralAdmissibleAssignmentIntegrand M hM K q x
          ∂cubicKernelProductMeasure M ell

/-- On a strict-subcritical profile ball, the raw admissible resolvent sum
defined by inclusion--exclusion is exactly the literal admissible
length-assignment sum. -/
theorem positiveSurplusCubicAdmissibleResolventSum_eq_literal
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (ell : ℕ) (q : C(S, ℂ) × ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hprofile : ∀ y, ‖MPR.profile M hM q y‖ ≤ r) :
    positiveSurplusCubicAdmissibleResolventSum M hM ell q =
      positiveSurplusCubicLiteralAdmissibleResolventSum M hM ell q := by
  let _ := labelledConnectedCubicKernelFintype ell
  unfold positiveSurplusCubicAdmissibleResolventSum
    positiveSurplusCubicIntegratedResolventSum
    positiveSurplusCubicRawForbiddenCorrection
    positiveSurplusCubicLiteralAdmissibleResolventSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro K _
  rw [← mul_sub]
  congr 1
  exact cubicKernelIntegratedResolvent_sub_rawForbidden_eq_literalAdmissible
    M hM K q r hr hr1 hprofile

end PerronWright.GraphCore
