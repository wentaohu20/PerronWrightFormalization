import PerronWright.Probability.BrownianEntranceProjectiveFamily
import PerronWright.Probability.BrownianPathIndependentIncrements

/-! # Literal finite coordinates on both sides of the survival horizon

Repeated and unordered prefix coordinates are recovered from an ordered
schedule containing the endpoint. Coordinates after the horizon use the
literal fresh forward path. This is deterministic coordinate geometry;
no convergence or distributional identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianSurvivalCylinderCoordinates

open BrownianPathLaw BrownianPathIndependentIncrements BrownianEntranceProjectiveFamily

def interiorSamples {n : ℕ} (σ : Fin n → ℝ≥0) : Finset (InteriorTime 1) :=
  (Finset.univ.image σ).subtype (fun t ↦ 0 < t ∧ t < 1)

private theorem mem_interiorSamples {n : ℕ} (σ : Fin n → ℝ≥0) (i : Fin n)
    (hi : 0 < σ i ∧ σ i < 1) :
    (⟨σ i,hi⟩ : InteriorTime 1) ∈ interiorSamples σ := by
  exact Finset.mem_subtype.mpr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

def prefixFill {n : ℕ} (σ : Fin n → ℝ≥0)
    (v : Fin ((interiorSamples σ).card+1) → ℝ) : Fin n → ℝ := fun i ↦
  if hi : 0 < σ i ∧ σ i < 1 then
    v (((interiorSamples σ).orderIsoOfFin rfl).symm
      ⟨⟨σ i,hi⟩,mem_interiorSamples σ i hi⟩).castSucc
  else if σ i = 0 then 0 else v (Fin.last (interiorSamples σ).card)

theorem continuous_prefixFill {n : ℕ} (σ : Fin n → ℝ≥0) : Continuous (prefixFill σ) := by
  apply continuous_pi
  intro i
  by_cases hi : 0 < σ i ∧ σ i < 1
  · simp only [prefixFill,dif_pos hi]
    exact continuous_apply _
  · simp only [prefixFill,dif_neg hi]
    by_cases hz : σ i = 0
    · simp only [if_pos hz]
      exact continuous_const
    · simp only [if_neg hz]
      exact continuous_apply _

def prefixSample {n : ℕ} (σ : Fin n → ℝ≥0) (f : Path) :
    Fin ((interiorSamples σ).card+1) → ℝ :=
  fun i ↦ f (sortedTimes 1 (interiorSamples σ) i.succ)

theorem continuous_prefixSample {n : ℕ} (σ : Fin n → ℝ≥0) :
    Continuous (prefixSample σ) := continuous_pi (fun _ ↦ continuous_eval _)

theorem prefixFill_sample {n : ℕ} (σ : Fin n → ℝ≥0) (hσ : ∀ i, σ i ≤ 1)
    (f : Path) (hz : f 0 = 0) :
    prefixFill σ (prefixSample σ f) = fun i ↦ f (σ i) := by
  funext i
  by_cases hi : 0 < σ i ∧ σ i < 1
  · simp only [prefixFill,dif_pos hi,prefixSample,Fin.succ_castSucc,
      sortedTimes_internal,OrderIso.apply_symm_apply]
  · simp only [prefixFill,dif_neg hi]
    by_cases hzero : σ i = 0
    · simp only [hzero,if_true,hz]
    · have hpos : 0 < σ i := pos_iff_ne_zero.mpr hzero
      have hone : σ i = 1 := le_antisymm (hσ i)
        (le_of_not_gt (fun h ↦ hi ⟨hpos,h⟩))
      simp only [prefixSample,Fin.succ_last,sortedTimes_last,hone,one_ne_zero,if_false]

def clampedTimes {n : ℕ} (σ : Fin n → ℝ≥0) : Fin n → ℝ≥0 := fun i ↦ min (σ i) 1

def spliceFill {n : ℕ} (σ : Fin n → ℝ≥0)
    (q : (Fin ((interiorSamples (clampedTimes σ)).card+1) → ℝ) × Path) : Fin n → ℝ :=
  fun i ↦ prefixFill (clampedTimes σ) q.1 i+q.2 (σ i-1)

theorem continuous_spliceFill {n : ℕ} (σ : Fin n → ℝ≥0) : Continuous (spliceFill σ) :=
  continuous_pi (fun i ↦
    ((continuous_apply i).comp ((continuous_prefixFill (clampedTimes σ)).comp continuous_fst)).add
      ((continuous_eval (σ i-1)).comp continuous_snd))

theorem spliceFill_sample {n : ℕ} (σ : Fin n → ℝ≥0) (p h : Path) (hz : p 0 = 0) :
    spliceFill σ (prefixSample (clampedTimes σ) p,h) =
      fun i ↦ splicePath 1 (p,h) (σ i) := by
  have he := prefixFill_sample (clampedTimes σ) (fun i ↦ min_le_right (σ i) 1) p hz
  funext i
  change prefixFill (clampedTimes σ) (prefixSample (clampedTimes σ) p) i+h (σ i-1) = _
  rw [he]
  rfl

end PerronWright.BrownianSurvivalCylinderCoordinates
