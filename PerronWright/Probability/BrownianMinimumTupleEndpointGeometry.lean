import PerronWright.Probability.BrownianMinimumFutureCoordinates
import PerronWright.Probability.BrownianMinimumEndpointCandidateContinuity
import PerronWright.Probability.BrownianEntranceProductGeometry

/-! # Literal endpoint-pinned entrance tuple geometry

The residual first duration depends on the proposed minimum time. Every
later duration is the original observation gap. Appending the terminal
height splits off the genuine final killed transition.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumTupleEndpointGeometry

open BrownianMinimumFutureCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFreeEntranceGeometry BrownianPositiveBridgeMultiPointEntrance
open BrownianEntranceProductGeometry BrownianKilledBoundaryEntrance
open BrownianPositiveKilledEndpoint

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def residualGaps (n : ℕ) (times : Fin (n+2) → ℝ≥0) (s : ℝ) : ℕ → ℝ≥0 :=
  orderedGaps (n+2) (residualSchedule (n+1) times (Real.toNNReal s))

def fixedGaps (n : ℕ) (times : Fin (n+2) → ℝ≥0) : ℕ → ℝ≥0 :=
  orderedGaps (n+2) (Fin.cons 0 times)

theorem measurable_residualGaps (n : ℕ) (times : Fin (n+2) → ℝ≥0) :
    Measurable (residualGaps n times) := by
  apply measurable_pi_lambda
  intro j
  unfold residualGaps orderedGaps finiteTimeExtension residualSchedule
  fun_prop

theorem residualGaps_zero (n : ℕ) (times : Fin (n+2) → ℝ≥0) (s : ℝ) :
    residualGaps n times s 0 = times 0-Real.toNNReal s := by
  unfold residualGaps orderedGaps
  have h1 := finiteTimeExtension_at (n+2) (residualSchedule (n+1) times (Real.toNNReal s))
    (0 : Fin (n+2)).succ
  have h0 := finiteTimeExtension_at (n+2) (residualSchedule (n+1) times (Real.toNNReal s))
    (0 : Fin (n+3))
  simp only [Fin.val_succ,Fin.val_zero] at h1 h0
  rw [h1,h0]
  simp only [residualSchedule_succ,residualSchedule_zero,tsub_zero]

theorem fixedGaps_internal (n : ℕ) (times : Fin (n+2) → ℝ≥0) (i : Fin (n+1)) :
    fixedGaps n times (i.val+1) = times i.succ-times i.castSucc := by
  unfold fixedGaps orderedGaps
  have h1 := finiteTimeExtension_at (n+2) (Fin.cons 0 times) i.succ.succ
  have h0 := finiteTimeExtension_at (n+2) (Fin.cons 0 times) i.castSucc.succ
  simp only [Fin.val_succ,Fin.val_castSucc] at h1 h0
  rw [h1,h0]
  simp only [Fin.cons_succ]

theorem residualGaps_internal (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (s : ℝ) (hs : Real.toNNReal s < times 0)
    (i : Fin (n+1)) :
    residualGaps n times s (i.val+1) = fixedGaps n times (i.val+1) := by
  rw [fixedGaps_internal]
  unfold residualGaps orderedGaps
  have h1 := finiteTimeExtension_at (n+2) (residualSchedule (n+1) times (Real.toNNReal s)) i.succ.succ
  have h0 := finiteTimeExtension_at (n+2) (residualSchedule (n+1) times (Real.toNNReal s)) i.castSucc.succ
  simp only [Fin.val_succ,Fin.val_castSucc] at h1 h0
  rw [h1,h0]
  simp only [residualSchedule_succ]
  have hi := hs.le.trans (hstrict.monotone (Fin.zero_le i.castSucc))
  have hj := hs.le.trans (hstrict.monotone (Fin.zero_le i.succ))
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (tsub_le_tsub_right (hstrict.monotone Fin.castSucc_lt_succ.le) _),
    NNReal.coe_sub hi,NNReal.coe_sub hj,
    NNReal.coe_sub (hstrict.monotone Fin.castSucc_lt_succ.le)]
  ring

theorem fixedGaps_positive (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0) :
    ∀ j < n+2, 0 < fixedGaps n times j :=
  orderedGaps_positive (n+2) (Fin.cons 0 times)
    (Fin.strictMono_cons.mpr ⟨fun i ↦ hfirst.trans_le (hstrict.monotone (Fin.zero_le i)),hstrict⟩)

theorem internalDensity_residual (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (s : ℝ) (hs : Real.toNNReal s < times 0)
    (v : FreeVector (n+1)) :
    internalDensity n (residualGaps n times s) v = internalDensity n (fixedGaps n times) v := by
  unfold internalDensity
  apply Finset.prod_congr rfl
  intro i _
  have h := residualGaps_internal n times hstrict s hs i.castSucc
  simp only [Fin.val_castSucc] at h
  rw [h]

theorem entranceJoint_append (n : ℕ) (gaps : ℕ → ℝ≥0) (v : FreeVector (n+1)) (y : ℝ) :
    entranceJoint (n+1) gaps (Fin.snoc v y) =
      entranceJoint n gaps v*density (v (Fin.last n)) (gaps (n+1)) y := by
  unfold entranceJoint
  rw [show (0 : Fin (n+2)) = (0 : Fin (n+1)).castSucc by rfl]
  simp only [internalDensity,Fin.prod_univ_castSucc,
    Fin.snoc_castSucc,Fin.snoc_last,Fin.val_castSucc,Fin.val_last,
    Fin.succ_castSucc,Fin.succ_last,
    mul_assoc]

theorem measurable_joint_entranceJoint (n : ℕ) :
    Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ entranceJoint n q.1 q.2) :=
  (measurable_joint_entranceNN.comp
    (by fun_prop : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ (q.1 0,q.2 0)))).mul
      (measurable_joint_internalDensity n)

def candidate (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo (0 : ℝ) (times (Fin.last (n+1)) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
    BrownianFirstPassageDensityGeometry.density a s*∫⁻ v : FreeVector (n+1),
      entranceJoint (n+1) (residualGaps n times s) (Fin.snoc v (a+z))*
        ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v (a+z)))

theorem measurable_joint_integrand (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦
      BrownianFirstPassageDensityGeometry.density q.2.1.2 q.2.1.1*
        (entranceJoint (n+1) (residualGaps n times q.2.1.1) (Fin.snoc q.2.2 (q.2.1.2+q.1))*
          ENNReal.ofReal (Φ (Real.toNNReal q.2.1.1,-q.2.1.2,Fin.snoc q.2.2 (q.2.1.2+q.1))))) := by
  have hv : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦
      (Fin.snoc q.2.2 (q.2.1.2+q.1) : FreeVector (n+2))) := by
    simpa only [Function.comp_def,freeAppend] using
      (continuous_freeAppend (n+1)).measurable.comp
        (by fun_prop : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦
          (q.2.2,q.2.1.2+q.1)))
  exact (BrownianHeatResolvent.measurable_joint_passageDensity.comp
    (by fun_prop : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦ (q.2.1.2,q.2.1.1)))).mul
    (((measurable_joint_entranceJoint (n+1)).comp
      (((measurable_residualGaps n times).comp
        (by fun_prop : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦ q.2.1.1))).prodMk hv)).mul
        ((Φ.continuous.measurable.comp
          ((by fun_prop : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦
            Real.toNNReal q.2.1.1)).prodMk
              ((by fun_prop : Measurable (fun q : ℝ × ((ℝ × ℝ) × FreeVector (n+1)) ↦
                -q.2.1.2)).prodMk hv))).ennreal_ofReal))

end PerronWright.BrownianMinimumTupleEndpointGeometry
