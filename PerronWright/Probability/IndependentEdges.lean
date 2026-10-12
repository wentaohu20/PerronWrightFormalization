import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite independent edge variables

An edge with nonnegative hazard `z` is present with probability
`1 - exp (-z)`.  The results below construct the probability mass function
and compute every partial edge-assignment event directly from the finite
product.  They will be applied with hazard `t * κ(x_i,x_j) / n`.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.IndependentEdges

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The probability of one Boolean edge value at hazard `z`. -/
def edgeMass (z : ℝ) (b : Bool) : ℝ :=
  if b then 1 - Real.exp (-z) else Real.exp (-z)

@[simp] theorem edgeMass_false (z : ℝ) :
    edgeMass z false = Real.exp (-z) := rfl

@[simp] theorem edgeMass_true (z : ℝ) :
    edgeMass z true = 1 - Real.exp (-z) := rfl

theorem edgeMass_nonneg {z : ℝ} (hz : 0 ≤ z) (b : Bool) :
    0 ≤ edgeMass z b := by
  cases b
  · exact (Real.exp_pos _).le
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz))

@[simp] theorem sum_edgeMass (z : ℝ) :
    ∑ b : Bool, edgeMass z b = 1 := by
  simp [edgeMass]

/-- The conditional mass of a complete edge assignment. -/
def mass (z : J → ℝ) (a : J → Bool) : ℝ :=
  ∏ e, edgeMass (z e) (a e)

omit [DecidableEq J] in
theorem mass_nonneg {z : J → ℝ} (hz : ∀ e, 0 ≤ z e)
    (a : J → Bool) : 0 ≤ mass z a :=
  Finset.prod_nonneg (fun e _ ↦ edgeMass_nonneg (hz e) (a e))

@[simp] theorem sum_mass (z : J → ℝ) :
    ∑ a : J → Bool, mass z a = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp

/-- The probability mass function of the independent Boolean edges. -/
def pmf (z : J → ℝ) (hz : ∀ e, 0 ≤ z e) : PMF (J → Bool) :=
  PMF.ofFintype (fun a ↦ ENNReal.ofReal (mass z a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ mass_nonneg hz a)]
    simp)

@[simp] theorem pmf_apply (z : J → ℝ) (hz : ∀ e, 0 ≤ z e)
    (a : J → Bool) : pmf z hz a = ENNReal.ofReal (mass z a) := rfl

@[simp] theorem pmf_apply_toReal (z : J → ℝ) (hz : ∀ e, 0 ≤ z e)
    (a : J → Bool) : (pmf z hz a).toReal = mass z a := by
  rw [pmf_apply, ENNReal.toReal_ofReal (mass_nonneg hz a)]

/-- The values on the prescribed coordinates agree with `c`. -/
def AgreesOn (D : Finset J) (c a : J → Bool) : Prop :=
  ∀ e ∈ D, a e = c e

/-- Summing over unconstrained edges leaves just the prescribed factors. -/
theorem sum_mass_agreesOn (z : J → ℝ) (D : Finset J)
    (c : J → Bool) :
    (∑ a : J → Bool, if AgreesOn D c a then mass z a else 0) =
      ∏ e ∈ D, edgeMass (z e) (c e) := by
  classical
  have hmask (a : J → Bool) :
      (if AgreesOn D c a then mass z a else 0) =
        ∏ e, if e ∈ D → a e = c e then edgeMass (z e) (a e) else 0 := by
    by_cases h : AgreesOn D c a
    · rw [if_pos h]
      unfold mass
      apply Finset.prod_congr rfl
      intro e _
      rw [if_pos (h e)]
    · rw [if_neg h]
      obtain ⟨e, he, hc⟩ : ∃ e, e ∈ D ∧ a e ≠ c e := by
        simpa only [AgreesOn, not_forall, exists_prop] using h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      exact if_neg (fun h' ↦ hc (h' he))
  simp_rw [hmask]
  rw [← Fintype.prod_sum
    (fun e (b : Bool) ↦ if e ∈ D → b = c e then edgeMass (z e) b else 0)]
  have he (e : J) :
      (∑ b : Bool, if e ∈ D → b = c e then edgeMass (z e) b else 0) =
        if e ∈ D then edgeMass (z e) (c e) else 1 := by
    by_cases h : e ∈ D
    · cases c e <;> simp [h]
    · simp [h]
  simp_rw [he]
  exact Finset.prod_ite_mem_eq D (fun e ↦ edgeMass (z e) (c e))

/-- A genuine expectation under the constructed probability measure. -/
theorem integral_agreesOn (z : J → ℝ) (hz : ∀ e, 0 ≤ z e)
    (D : Finset J) (c : J → Bool) :
    (∫ a, if AgreesOn D c a then (1 : ℝ) else 0 ∂(pmf z hz).toMeasure) =
      ∏ e ∈ D, edgeMass (z e) (c e) := by
  classical
  rw [PMF.integral_eq_sum]
  simp only [pmf_apply_toReal, smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact sum_mass_agreesOn z D c

/-- An edge pattern on the prescribed set, padded by absent edges elsewhere. -/
def extend (D : Finset J) (c : D → Bool) : J → Bool :=
  fun e ↦ if h : e ∈ D then c ⟨e, h⟩ else false

/-- Restrict a complete edge assignment to a finite set of coordinates. -/
def restrict (D : Finset J) (a : J → Bool) : D → Bool := fun e ↦ a e.val

omit [Fintype J] in
@[simp] theorem extend_mem (D : Finset J) (c : D → Bool) (e : D) :
    extend D c e.val = c e := by simp [extend, e.property]

omit [Fintype J] in
@[simp] theorem restrict_extend (D : Finset J) (c : D → Bool) :
    restrict D (extend D c) = c := by
  funext e
  exact extend_mem D c e

omit [Fintype J] in
theorem agreesOn_extend_restrict (D : Finset J) (a : J → Bool) :
    AgreesOn D a (extend D (restrict D a)) := by
  intro e he
  simp [extend, restrict, he]

omit [Fintype J] in
theorem agreesOn_extend_iff (D : Finset J) (c : D → Bool) (a : J → Bool) :
    AgreesOn D (extend D c) a ↔ restrict D a = c := by
  constructor
  · intro h
    funext e
    simpa only [restrict, extend_mem] using h e.val e.property
  · intro h e he
    have := congrFun h ⟨e, he⟩
    simpa [restrict, extend, he] using this

/-- Exact elimination of unconstrained independent coordinates for every
observable that only depends on the prescribed coordinates. -/
theorem sum_mass_mul_local (z : J → ℝ) (D : Finset J)
    (F : (J → Bool) → ℝ)
    (hF : ∀ a, F a = F (extend D (restrict D a))) :
    (∑ a : J → Bool, mass z a * F a) =
      ∑ c : D → Bool,
        (∏ e ∈ D, edgeMass (z e) (extend D c e)) * F (extend D c) := by
  have hs (a : J → Bool) :
      mass z a * F a = ∑ c : D → Bool,
        if AgreesOn D (extend D c) a then mass z a * F (extend D c) else 0 := by
    rw [Fintype.sum_eq_single (restrict D a)]
    · rw [if_pos ((agreesOn_extend_iff D _ a).mpr rfl), ← hF a]
    · intro c hc
      rw [if_neg (fun h ↦ hc ((agreesOn_extend_iff D c a).mp h).symm)]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have hs' :
      (∑ a : J → Bool,
        if AgreesOn D (extend D c) a then mass z a * F (extend D c) else 0) =
      (∑ a : J → Bool, if AgreesOn D (extend D c) a then mass z a else 0) *
        F (extend D c) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hs', sum_mass_agreesOn]

/-- The absence factor can be extracted from a present edge. -/
theorem edgeMass_true_odds (z : ℝ) :
    edgeMass z true = Real.exp (-z) * (Real.exp z - 1) := by
  rw [edgeMass_true, mul_sub, ← Real.exp_add]
  simp

omit [Fintype J] [DecidableEq J] in
/-- The exact exponential-odds factorization of a prescribed configuration. -/
theorem prescribedMass_odds (z : J → ℝ) (D : Finset J)
    (c : J → Bool) :
    (∏ e ∈ D, edgeMass (z e) (c e)) =
      Real.exp (-(∑ e ∈ D, z e)) *
        ∏ e ∈ D, if c e then Real.exp (z e) - 1 else 1 := by
  classical
  have he (e : J) : edgeMass (z e) (c e) =
      Real.exp (-(z e)) * (if c e then Real.exp (z e) - 1 else 1) := by
    cases c e
    · simp
    · exact edgeMass_true_odds (z e)
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  simp only [Finset.sum_neg_distrib]

end PerronWright.IndependentEdges
