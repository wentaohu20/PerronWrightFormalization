import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.InfinitePi

/-!
# Exact finite superposition of genuine independent Poisson counts

Finite sums have the sum of their actual rates. The argument uses the
proved Poisson convolution law and independence of disjoint finite index
sets; no superposition law is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical NNReal

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FinitePoissonSuperposition

theorem poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  by_cases hn : n = 0 <;> simp [poissonMeasure_singleton,hn]

variable {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem hasLaw_finset_sum (X : I → Ω → ℕ) (r : I → ℝ≥0)
    (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P) (hi : iIndepFun X P)
    (s : Finset I) :
    HasLaw (fun ω ↦ ∑ i ∈ s, X i ω) (poissonMeasure (∑ i ∈ s, r i)) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty,poissonMeasure_zero_eq_dirac]
      exact hasLaw_dirac_of_ae_eq (Eventually.of_forall (fun _ ↦ rfl))
  | @insert i s his ih =>
      have hind := (hi.indepFun_finsetSum_of_notMem₀ (fun i ↦ (hX i).aemeasurable) his).symm
      have ih' : HasLaw (∑ j ∈ s, X j) (poissonMeasure (∑ j ∈ s, r j)) P := by
        convert ih using 1
        funext ω
        simp only [Finset.sum_apply]
      have hsum := hind.hasLaw_add_poissonMeasure (hX i) ih'
      simp only [Finset.sum_insert his]
      convert hsum using 1
      funext ω
      simp only [Pi.add_apply,Finset.sum_apply]

theorem infinitePi_hasLaw_finset_sum (r : I → ℝ≥0) (s : Finset I) :
    HasLaw (fun x : I → ℕ ↦ ∑ i ∈ s, x i) (poissonMeasure (∑ i ∈ s, r i))
      (Measure.infinitePi (fun i ↦ poissonMeasure (r i))) := by
  exact hasLaw_finset_sum (fun i (x : I → ℕ) ↦ x i) r
    (fun i ↦ (measurePreserving_eval_infinitePi (fun i ↦ poissonMeasure (r i)) i).hasLaw)
    (iIndepFun_infinitePi (X := fun _ (x : ℕ) ↦ x) (fun _ ↦ measurable_id)) s

end PerronWright.FinitePoissonSuperposition
