import PerronWright.Probability.BrownianFullHorizonSpatialCounts

/-!
# Full spatial count laws, independence, and exact bounded-law agreement

The count observables are taken from the literal summed random measure.
Their Poisson marginals and independence are consequences of the proved
vector pushforward. On any fixed Borel time window their joint law agrees
exactly with the earlier bounded iid-atom spatial construction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonSpatialCountLaws

open BrownianPathLaw BrownianFullHorizonSpatialKernel BrownianFullHorizonSpatialIntensity
open BrownianFullHorizonSpatialSupport BrownianFullHorizonSpatialCounts FinitePointMeasureCompact

variable {D : Type*} [Fintype D]

theorem spatial_hasLaw_count_vector (lambda : ℝ) (f : Path) (N : ℕ)
    (A : D → Set (ℝ × ℝ)) (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (hAN : ∀ i, A i ⊆ timeCut N) :
    HasLaw (fun a : SpatialAtoms ↦ fun i ↦ spatialCount a (A i))
      (PoissonCountKernel.finiteCountLaw (fun i ↦ (intensity lambda f (A i)).toNNReal))
      (spatialLaw lambda f) :=
  ⟨(measurable_pi_lambda _ (fun i ↦ measurable_spatialCount (hA i))).aemeasurable,
    spatialLaw_map_count_vector lambda f N A hAd hA hAN⟩

theorem spatial_hasLaw_count (lambda : ℝ) (f : Path) (N : ℕ)
    (A : D → Set (ℝ × ℝ)) (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (hAN : ∀ i, A i ⊆ timeCut N) (i : D) :
    HasLaw (fun a : SpatialAtoms ↦ spatialCount a (A i))
      (poissonMeasure ((intensity lambda f (A i)).toNNReal)) (spatialLaw lambda f) :=
  (PoissonCountKernel.finiteCountLaw_hasLaw_eval _ i).fun_comp
    (spatial_hasLaw_count_vector lambda f N A hAd hA hAN)

theorem spatial_counts_independent (lambda : ℝ) (f : Path) (N : ℕ)
    (A : D → Set (ℝ × ℝ)) (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (hAN : ∀ i, A i ⊆ timeCut N) :
    iIndepFun (fun i (a : SpatialAtoms) ↦ spatialCount a (A i)) (spatialLaw lambda f) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (measurable_spatialCount (hA i)).aemeasurable)).mpr
  rw [spatialLaw_map_count_vector lambda f N A hAd hA hAN]
  unfold PoissonCountKernel.finiteCountLaw
  congr 1
  funext i
  exact (spatial_hasLaw_count lambda f N A hAd hA hAN i).map_eq.symm

theorem spatial_countLaw_eq_bounded_countLaw (lambda : ℝ) (f : Path) (a b : ℝ≥0)
    (A : D → Set (ℝ × ℝ)) (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i))
    (hwin : ∀ i, ∀ z ∈ A i, z.1 ∈ Icc (a : ℝ) (b : ℝ)) :
    (spatialLaw lambda f).map (fun η i ↦ spatialCount η (A i)) =
      (BrownianUnderGraphPoissonLaw.law lambda a b f).map (fun η i ↦ count η (A i)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (b : ℝ)
  have hAN : ∀ i, A i ⊆ timeCut N := fun i z hz ↦ (hwin i z hz).2.trans_lt hN
  rw [spatialLaw_map_count_vector lambda f N A hAd hA hAN,
    BrownianUnderGraphDisjointCounts.law_count_vector lambda a b f A hAd hA]
  congr 1
  funext i
  congr 1
  rw [intensity,Measure.restrict_apply (hA i)]
  congr 1
  ext z
  constructor
  · rintro ⟨hz,hr⟩
    exact ⟨hz,hwin i z hz,hr.2⟩
  · rintro ⟨hz,hr⟩
    exact ⟨hz,a.coe_nonneg.trans hr.1.1,hr.2⟩

end PerronWright.BrownianFullHorizonSpatialCountLaws
