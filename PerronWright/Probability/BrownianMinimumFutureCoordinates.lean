import PerronWright.Probability.ContinuousPathMinimumFutureBandAverage
import PerronWright.Probability.BrownianKilledFreeEntranceNonnegativeTests

/-! # Literal original observation times after the minimum

Residual observation times are the original times minus the minimum
time. Their positive ordering and the actual future-path reconstruction
are deterministic identities. The coordinate pullback stays continuous
even outside the region in which the minimum precedes every observation.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumFutureCoordinates

open BrownianPathLaw ContinuousPathLeastMinimum ContinuousPathMinimumFutureBandAverage
open BrownianPathIndependentIncrements BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFreeEntranceTests BrownianKilledFreeEntranceNonnegativeTests
open BrownianKilledFiniteDimensionalOrderedTimes

def residualSchedule (n : ℕ) (times : Fin (n+1) → ℝ≥0) (s : ℝ≥0) : Fin (n+2) → ℝ≥0 :=
  Fin.cons 0 (fun i ↦ times i-s)

@[simp] theorem residualSchedule_zero (n : ℕ) (times : Fin (n+1) → ℝ≥0) (s : ℝ≥0) :
    residualSchedule n times s 0 = 0 := by simp [residualSchedule]

@[simp] theorem residualSchedule_succ (n : ℕ) (times : Fin (n+1) → ℝ≥0) (s : ℝ≥0)
    (i : Fin (n+1)) : residualSchedule n times s i.succ = times i-s := by
  simp [residualSchedule]

theorem residualSchedule_last (n : ℕ) (times : Fin (n+1) → ℝ≥0) (s : ℝ≥0) :
    residualSchedule n times s (Fin.last (n+1)) = times (Fin.last n)-s := by
  exact residualSchedule_succ n times s (Fin.last n)

theorem residualSchedule_strictMono (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (s : ℝ≥0) (hs : s < times 0) :
    StrictMono (residualSchedule n times s) := by
  apply Fin.strictMono_cons.mpr
  constructor
  · intro i
    exact tsub_pos_iff_lt.mpr (hs.trans_le (hstrict.monotone (Fin.zero_le i)))
  · intro i j hij
    have hsi := hs.le.trans (hstrict.monotone (Fin.zero_le i))
    have hsj := hs.le.trans (hstrict.monotone (Fin.zero_le j))
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_sub hsi,NNReal.coe_sub hsj]
    exact sub_lt_sub_right (show (times i : ℝ) < (times j : ℝ) from hstrict hij) _

def coordinateMap (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (p : ℝ≥0 × ℝ × Path) : ℝ≥0 × ℝ × FreeVector (n+1) :=
  (p.1,p.2.1,fun i ↦ p.2.2 (times i-p.1))

theorem continuous_coordinateMap (n : ℕ) (times : Fin (n+1) → ℝ≥0) :
    Continuous (coordinateMap n times) :=
  continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_pi (fun i ↦
    continuous_joint_eval.comp (continuous_snd.snd.prodMk
      (show Continuous (fun p : ℝ≥0 × ℝ × Path ↦ times i-p.1) from
        continuous_const.sub continuous_fst)))))

def coordinateTest (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) : (ℝ≥0 × ℝ × Path) →ᵇ ℝ :=
  Φ.compContinuous ⟨coordinateMap n times,continuous_coordinateMap n times⟩

theorem coordinateTest_minimumPoint (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (T : ℝ≥0) (f : Path)
    (hs : ∀ i, leastMinimizer T f ≤ times i) :
    coordinateTest n times Φ (minimumPoint T f) =
      Φ (leastMinimizer T f,minimumValue T f,fun i ↦ f (times i)-minimumValue T f) := by
  change Φ (leastMinimizer T f,minimumValue T f,
    fun i ↦ futurePath (leastMinimizer T f) f (times i-leastMinimizer T f)) = _
  apply congrArg Φ
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext i
  dsimp only
  rw [futurePath_eval,add_tsub_cancel_of_le (hs i),leastMinimizer_value]

theorem actual_residual_coordinates_entrance_tendsto (n : ℕ)
    (times : Fin (n+1) → ℝ≥0) (hstrict : StrictMono times)
    (s : ℝ≥0) (hs : s < times 0) (a : ℝ)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ f in ContinuousPathFirstPassage.survival (-δ) (times (Fin.last n)-s),
        ENNReal.ofReal (Φ (s,-a,fun i ↦ f (times i-s))) ∂pathLaw)/ENNReal.ofReal δ)
      (𝓝[>] 0) (𝓝 (∫⁻ v, ENNReal.ofReal (Φ (s,-a,v))
        ∂freeEntranceLaw n (orderedGaps (n+1) (residualSchedule n times s)))) := by
  let L : C(ℝ × FreeVector (n+1),ℝ≥0 × ℝ × FreeVector (n+1)) :=
    ⟨fun p ↦ (s,-a,p.2),continuous_const.prodMk (continuous_const.prodMk continuous_snd)⟩
  have h := actual_unshifted_ordered_nonnegative_test_tendsto n (residualSchedule n times s)
    (residualSchedule_strictMono n times hstrict s hs) (residualSchedule_zero n times s)
    (Φ.compContinuous L) (fun p ↦ hΦ _)
  simpa only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,L,
    residualSchedule_succ,residualSchedule_last] using h

end PerronWright.BrownianMinimumFutureCoordinates
