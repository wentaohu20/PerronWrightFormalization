import PerronWright.Probability.WindowSizeRescaling
import PerronWright.Probability.FiniteIrreduciblePointProcessNormalization
import PerronWright.Probability.FiniteIrreducibleWindowPointLawLimit

/-! # Genuine deterministic starred window weak limits

The actual closed graph window, including both boundary atoms and all
multiplicities, is exactly the positive dilation of the unstarred window
[a/c,b/c]. Its full source spatial limit is already proved.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleStarredWindowLaw

open FinitePointMeasureCompact FinitePointMeasureMarking
open ComponentWindowPointMeasures WindowSizeRescaling
open FiniteIrreducibleComponentProcess (graphLaw)
open FiniteIrreduciblePointProcessNormalization
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S]

def windowLaw (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R : ℕ) (c : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  ⟨(graphLaw M lambda n x).map (windowPointMeasure a b R c),
    Measure.isProbabilityMeasure_map (measurable_windowPointMeasure a b R c n).aemeasurable⟩

theorem windowLaw_eq_map_unmarkedWindowLaw (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S) :
    windowLaw M lambda a b R c n x =
      (FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda (a/c) (b/c) R n x).map
        (continuous_mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc)).measurable.aemeasurable := by
  apply Subtype.ext
  change (graphLaw M lambda n x).map (windowPointMeasure a b R c) =
    ((graphLaw M lambda n x).map (windowPointMeasure (a/c) (b/c) R 1)).map
      (mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc).measurable)
  rw [Measure.map_map (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable
    (measurable_windowPointMeasure (a/c) (b/c) R 1 n)]
  congr 1
  exact funext (windowPointMeasure_eq_map a b R hc)

def starredWindowLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  windowLaw M lambda a b R (sizeScale M hM) n x

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem exists_unique_windowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    {c : ℝ} (hc : 0 < c) (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ windowLaw M lambda a b R c n (v n)) atTop (𝓝 ν) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a,le_rfl,hab⟩,⟨0,by omega⟩)⟩
  have hab' : a/c ≤ b/c := (div_le_div_iff_of_pos_right hc).mpr hab
  obtain ⟨ν,hν,_⟩ := FiniteIrreducibleWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
    M hM lambda (a/c) (b/c) (div_pos ha hc) hab' R v E hE hround
  have hcont := continuous_mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc)
  let ρ := ν.map hcont.measurable.aemeasurable
  have hρ : Tendsto (fun n ↦ windowLaw M lambda a b R c n (v n)) atTop (𝓝 ρ) := by
    simpa only [windowLaw_eq_map_unmarkedWindowLaw M lambda a b R hc,ρ] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda (a/c) (b/c) R n (v n))
        ν hν hcont
  exact ⟨ρ,hρ,fun θ hθ ↦ tendsto_nhds_unique hθ hρ⟩

theorem exists_unique_starredWindowLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ starredWindowLaw M hM lambda a b R n (v n)) atTop (𝓝 ν) :=
  exists_unique_windowLaw_limit M hM lambda a b ha hab R (sizeScale_pos M hM) v E hE hround

end PerronWright.FiniteIrreducibleStarredWindowLaw
