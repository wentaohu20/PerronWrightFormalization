import PerronWright.Probability.CountableFiniteTupleSampling
import PerronWright.Probability.BrownianExcursionCampbellWeights

/-!
# Every-order intrinsic factorial statistics of the full Brownian process

Each slot has its own positive size interval and surplus. The intervals
may overlap. The statistic is an intrinsic measurable count polynomial
on the genuine weak-Borel finite-window point-measure law. The exact
expectation is the complete-excursion Poisson area-weighted Brownian
source integral, with no finite-moment or density hypothesis.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionRectangleFactorials

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionSection
open BrownianExcursionWindowPointMeasure BrownianExcursionAtomicMeasure
open BrownianExcursionPointProcessLaw BrownianFullHorizonPoissonMarks
open BrownianFullHorizonExcursionAreas ComponentGlobalPointProcess
open FinitePointMeasureCompact FinitePointMeasureRectangleFactorials

variable {d : ℕ}

def cells (a b : Fin d → ℝ) (r : Fin d → ℕ) : Fin d → Set PositiveSizeSurplus :=
  fun i ↦ BrownianExcursionCampbellWeights.cell (a i) (b i) (r i)

theorem measurableSet_cells (a b : Fin d → ℝ) (r : Fin d → ℕ) (i : Fin d) :
    MeasurableSet (cells a b r i) :=
  BrownianExcursionCampbellWeights.measurableSet_cell _ _ _

def windowSet (a b : Fin d → ℝ) (r : Fin d → ℕ) : Set PositiveSizeSurplus :=
  ⋃ i, cells a b r i

theorem isCompact_windowSet (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i) :
    IsCompact (windowSet a b r) :=
  isCompact_iUnion (fun i ↦ BrownianExcursionCampbellWeights.isCompact_cell _ _ _ (ha i))

theorem cells_subset_windowSet (a b : Fin d → ℝ) (r : Fin d → ℕ) (i : Fin d) :
    cells a b r i ⊆ windowSet a b r := subset_iUnion _ i

def factorialStatistic (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (η : PointMeasure PositiveSizeSurplus) : ℝ≥0∞ :=
  rectangleFactorial η (cells a b r)

theorem measurable_factorialStatistic (a b : Fin d → ℝ) (r : Fin d → ℕ) :
    Measurable (factorialStatistic a b r) :=
  (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp
    (measurable_rectangleFactorial (cells a b r) (measurableSet_cells a b r))

theorem atom_mem_cell_iff (lambda a b : ℝ) (r : ℕ) (q : ℚ)
    (p : Path × (ℕ → ℕ)) (hp : 0 < lengthValue lambda q p.1) :
    atom lambda (pathInput p) q ∈ BrownianExcursionCampbellWeights.cell a b r ↔
      lengthValue lambda q p.1 ∈ Icc a b ∧ rationalCount p.2 q = r := by
  simp [atom,positiveSize,pathInput,hp,BrownianExcursionCampbellWeights.cell,
    positiveWindowSet,ambientEmbedding,ComponentWindowPointMeasures.windowSet]
  intro hm _ _
  exact hm.le

theorem selection_cell_iff (lambda : ℝ) (K : Set PositiveSizeSurplus)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) (p : Path × (ℕ → ℕ)) (hg : Good lambda p.1)
    (i : Fin d) (q : ℚ) :
    (q ∈ BrownianExcursionCompactWindows.selection lambda K (pathInput p) ∧
      atom lambda (pathInput p) q ∈ cells a b r i) ↔
    Representative (driftedReflectionPath lambda p.1) q ∧
      lengthValue lambda q p.1 ∈ Icc (a i) (b i) ∧ rationalCount p.2 q = r i := by
  constructor
  · rintro ⟨hs,hc⟩
    have hp : 0 < lengthValue lambda q p.1 := hs.1.2.2
    exact ⟨hs.1.2.1,(atom_mem_cell_iff lambda (a i) (b i) (r i) q p hp).mp hc⟩
  · rintro ⟨hr,hb,hm⟩
    have hp : 0 < lengthValue lambda q p.1 := (ha i).trans_le hb.1
    have hc : atom lambda (pathInput p) q ∈ cells a b r i :=
      (atom_mem_cell_iff lambda (a i) (b i) (r i) q p hp).mpr ⟨hb,hm⟩
    exact ⟨⟨⟨hg,hr,hp⟩,hK i hc⟩,hc⟩

/-- The genuine intrinsic factorial count equals the actual complete
ordered distinct representative tuple count, pointwise on the proved
good set. No chosen enumeration or atom-distinctness assumption enters. -/
theorem window_factorialStatistic_eq_tuple_statistic (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) (p : Path × (ℕ → ℕ)) (hg : Good lambda p.1) :
    factorialStatistic a b r (BrownianExcursionCompactWindows.window lambda K (pathInput p)) =
      BrownianExcursionTuplePoissonWeights.statistic lambda a b r p := by
  unfold factorialStatistic BrownianExcursionCompactWindows.window
  rw [CountableFiniteTupleSampling.rectangleFactorial_pointMeasure _ _ _
    (BrownianExcursionCompactWindows.finite_selection lambda K hKc (pathInput p))
    _ (measurableSet_cells a b r)]
  apply tsum_congr
  intro e
  have h : (Function.Injective e ∧ ∀ i,
      e i ∈ BrownianExcursionCompactWindows.selection lambda K (pathInput p) ∧
      atom lambda (pathInput p) (e i) ∈ cells a b r i) ↔
      BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e p.1 ∧
        ∀ i, rationalCount p.2 (e i) = r i := by
    constructor
    · rintro ⟨he,hs⟩
      have ht i := (selection_cell_iff lambda K a b r ha hK p hg i (e i)).mp (hs i)
      exact ⟨⟨he,fun i ↦ ⟨(ht i).1,(ht i).2.1⟩⟩,fun i ↦ (ht i).2.2⟩
    · rintro ⟨⟨he,hs⟩,hm⟩
      exact ⟨he,fun i ↦ (selection_cell_iff lambda K a b r ha hK p hg i (e i)).mpr
        ⟨(hs i).1,(hs i).2,hm i⟩⟩
  simp only [BrownianExcursionTuplePoissonWeights.contribution,h]

theorem ae_window_factorialStatistic_eq_tuple_statistic (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) :
    ∀ᵐ p ∂pathJointLaw lambda,
      factorialStatistic a b r (BrownianExcursionCompactWindows.window lambda K (pathInput p)) =
        BrownianExcursionTuplePoissonWeights.statistic lambda a b r p := by
  have hg : ∀ᵐ p ∂pathJointLaw lambda, Good lambda p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [pathJointLaw_source]
    exact ae_good lambda
  exact hg.mono (fun p hp ↦ window_factorialStatistic_eq_tuple_statistic lambda K hKc a b r ha hK p hp)

/-- Every-order actual weak-Borel window law, arbitrary overlapping
positive size intervals, and the complete conditional Poisson weights.
Both sides are extended integrals; finite moments are not assumed. -/
theorem windowLaw_rectangle_factorial_formula (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) :
    (∫⁻ η, factorialStatistic a b r η
      ∂(BrownianExcursionCompactWindows.law lambda K hKc : Measure _)) =
    ∫⁻ f, ∑' e : Fin d → ℚ, BrownianExcursionTuplePoissonWeights.weight lambda a b r e f
      ∂pathLaw := by
  change (∫⁻ η, factorialStatistic a b r η
    ∂((pathJointLaw lambda).map (BrownianExcursionCompactWindows.window lambda K ∘ pathInput))) = _
  rw [lintegral_map (measurable_factorialStatistic a b r)
    ((BrownianExcursionCompactWindows.measurable_window lambda K hKc.measurableSet).comp measurable_pathInput)]
  calc
    _ = ∫⁻ p, BrownianExcursionTuplePoissonWeights.statistic lambda a b r p ∂pathJointLaw lambda :=
      lintegral_congr_ae (ae_window_factorialStatistic_eq_tuple_statistic lambda K hKc a b r ha hK)
    _ = _ := BrownianExcursionTuplePoissonWeights.joint_expectation_eq_source_weights lambda a b r

theorem windowLaw_rectangle_factorial_complete_area_formula (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) :
    (∫⁻ η, factorialStatistic a b r η
      ∂(BrownianExcursionCompactWindows.law lambda K hKc : Measure _)) =
    ∫⁻ f, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f then
        ∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda f) (r i) else 0 ∂pathLaw := by
  rw [windowLaw_rectangle_factorial_formula lambda K hKc a b r ha hK]
  exact lintegral_congr (fun f ↦ tsum_congr (fun e ↦
    BrownianExcursionTuplePoissonWeights.weight_eq_full_area lambda a b r e f))

theorem windowLaw_rectangle_factorial_original_source (lambda : ℝ)
    (K : Set PositiveSizeSurplus) (hKc : IsCompact K)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i)
    (hK : ∀ i, cells a b r i ⊆ K) :
    (∫⁻ η, factorialStatistic a b r η
      ∂(BrownianExcursionCompactWindows.law lambda K hKc : Measure _)) =
    ∫⁻ x, ∑' e : Fin d → ℚ,
      BrownianExcursionTuplePoissonWeights.weight lambda a b r e (measurablePath x)
      ∂BrownianGaussianSkeleton.rationalLaw := by
  rw [windowLaw_rectangle_factorial_formula lambda K hKc a b r ha hK,pathLaw,
    lintegral_map (Measurable.tsum (fun e ↦
      BrownianExcursionTuplePoissonWeights.measurable_weight lambda a b r e)) measurable_measurablePath]

/-- The minimal actual compact union window requires only positive
lower size bounds, including different and overlapping slot windows. -/
theorem rectangle_factorial_formula (lambda : ℝ)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) (ha : ∀ i, 0 < a i) :
    (∫⁻ η, factorialStatistic a b r η
      ∂(BrownianExcursionCompactWindows.law lambda (windowSet a b r)
        (isCompact_windowSet a b r ha) : Measure _)) =
    ∫⁻ f, ∑' e : Fin d → ℚ,
      if BrownianExcursionTuplePoissonWeights.sourceEvent lambda a b e f then
        ∏ i, BrownianExcursionTuplePoissonWeights.poissonWeight
          (excursionArea (e i : ℝ) lambda f) (r i) else 0 ∂pathLaw :=
  windowLaw_rectangle_factorial_complete_area_formula lambda (windowSet a b r)
    (isCompact_windowSet a b r ha) a b r ha (cells_subset_windowSet a b r)

end PerronWright.BrownianExcursionRectangleFactorials
