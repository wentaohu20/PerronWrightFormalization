import PerronWright.Probability.BrownianKilledFiniteDimensionalDensity

/-! # Actual Gaussian product density at finite strictly ordered times

The actual free endpoint tuple at any finite strictly increasing time
vector, with first time zero, has the literal Gaussian-difference product
density. Its deterministic initial coordinate is not included in the
Lebesgue density. The final free coordinate is the genuine final endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFiniteDimensionalOrderedDensity

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledFiniteDimensionalCoordinates
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFiniteDimensionalDensity

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem orderedGaps_positive (n : ℕ) (times : Fin (n+1) → ℝ≥0) (hstrict : StrictMono times) :
    ∀ j < n, 0 < orderedGaps n times j := by
  intro j hj
  let i : Fin n := ⟨j,hj⟩
  have hs : finiteTimeExtension n times (j+1) = times i.succ :=
    finiteTimeExtension_at n times i.succ
  have hc : finiteTimeExtension n times j = times i.castSucc :=
    finiteTimeExtension_at n times i.castSucc
  rw [orderedGaps,hs,hc]
  have hlt : i.castSucc < i.succ := Fin.castSucc_lt_succ
  exact tsub_pos_iff_lt.mpr (hstrict hlt)

theorem freeTupleLaw_ordered_source (a : ℝ) (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hmono : Monotone times) (hzero : times 0 = 0) :
    freeTupleLaw a (orderedGaps n times) n =
      (pathLaw.restrict (survival (-a) (times (Fin.last n)))).map
        (fun f : Path ↦ fun i : Fin n ↦ a+f (times i.succ)) := by
  have hm : Measurable (fun f : Path ↦ fun i : Fin (n+1) ↦ a+f (times i)) :=
    measurable_pi_lambda _ (fun i ↦ measurable_const.add (continuous_eval _).measurable)
  have h := congrArg (Measure.map (dropInitial n)) (finite_ordered_endpoint_law 0 a n times hmono hzero)
  rw [Measure.map_map (continuous_dropInitial n).measurable hm,← freeTupleLaw_eq_chain_map,zero_sub] at h
  exact h.symm

/-- Direct actual source density for every finite strictly ordered time
vector and every positive initial point. No density identity is an input. -/
theorem ordered_free_endpoints_density (a : ℝ) (ha : 0 < a) (n : ℕ)
    (times : Fin (n+1) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0) :
    (pathLaw.restrict (survival (-a) (times (Fin.last n)))).map
        (fun f : Path ↦ fun i : Fin n ↦ a+f (times i.succ)) =
      volume.withDensity (jointDensity n a (orderedGaps n times)) := by
  rw [← freeTupleLaw_ordered_source a n times hstrict.monotone hzero]
  exact freeTupleLaw_eq_withDensity n a ha _ (orderedGaps_positive n times hstrict)

theorem ordered_free_endpoints_density_all (a : ℝ) (n : ℕ) (hn : 0 < n)
    (times : Fin (n+1) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0) :
    (pathLaw.restrict (survival (-a) (times (Fin.last n)))).map
        (fun f : Path ↦ fun i : Fin n ↦ a+f (times i.succ)) =
      volume.withDensity (jointDensity n a (orderedGaps n times)) := by
  rw [← freeTupleLaw_ordered_source a n times hstrict.monotone hzero]
  exact freeTupleLaw_eq_withDensity_all n hn a _ (orderedGaps_positive n times hstrict)

theorem lintegral_ordered_free_density (a : ℝ) (ha : 0 < a) (n : ℕ)
    (times : Fin (n+1) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    {Φ : FreeVector n → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f in survival (-a) (times (Fin.last n)),
        Φ (fun i : Fin n ↦ a+f (times i.succ)) ∂pathLaw) =
      ∫⁻ v, jointDensity n a (orderedGaps n times) v*Φ v := by
  have hm : Measurable (fun f : Path ↦ fun i : Fin n ↦ a+f (times i.succ)) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_const.add (continuous_eval _).measurable)
  rw [← lintegral_map hΦ hm,ordered_free_endpoints_density a ha n times hstrict hzero,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_jointDensity n a _) hΦ]
  rfl

end PerronWright.BrownianKilledFiniteDimensionalOrderedDensity
