import PerronWright.Probability.BrownianPathExtremaTails
import PerronWright.Probability.ContinuousPathLeastMinimum

/-! # The actual Brownian minimum is strictly below its starting point

The proved negative-level reflection tails extend to the open negative
half-line by countable rational exhaustion. Gaussian symmetry and its
atom-free endpoint law give total mass one. No negative-minimum or
minimum-uniqueness hypothesis is imposed on the Brownian path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianMinimumNegative

open BrownianPathLaw ContinuousPathLeastMinimum ContinuousPathReflection
open BrownianPathExtremaTails

theorem twice_gaussian_negative_mass (T : ℝ≥0) (hT : 0 < T) :
    2*gaussianReal 0 T (Iio 0) = 1 := by
  have hz : gaussianReal 0 T {0} = 0 :=
    (gaussianReal_absolutelyContinuous 0 hT.ne') (measure_singleton 0)
  have hsym : gaussianReal 0 T (Iio 0) = gaussianReal 0 T (Ioi 0) := by
    have he := gaussianReal_map_neg (μ := (0 : ℝ)) (v := T)
    simp only [neg_zero] at he
    calc
      _ = ((gaussianReal 0 T).map (fun x : ℝ ↦ -x)) (Iio 0) := by rw [he]
      _ = gaussianReal 0 T ((fun x : ℝ ↦ -x) ⁻¹' Iio 0) :=
        Measure.map_apply measurable_neg measurableSet_Iio
      _ = _ := by
        congr 1
        ext x
        simp only [mem_preimage,mem_Iio,mem_Ioi,neg_lt_zero]
  have hd : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    apply disjoint_left.mpr
    intro x h1 h2
    change x < 0 at h1
    change 0 < x at h2
    exact (not_le_of_gt h1) h2.le
  have he : gaussianReal 0 T (Iio 0)+gaussianReal 0 T (Ioi 0) = 1 := by
    rw [← measure_union hd measurableSet_Ioi,Iio_union_Ioi,
      measure_compl (measurableSet_singleton 0) (measure_ne_top _ _),hz,measure_univ,tsub_zero]
  rw [← hsym,← two_mul] at he
  exact he

theorem negative_minimum_mass (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | minimumValue T f < 0} = 1 := by
  let A := {q : ℚ // q < 0}
  let s : A → Set Path := fun q ↦ {f | minimumValue T f ≤ (q.1 : ℝ)}
  let u : A → Set ℝ := fun q ↦ Iic (q.1 : ℝ)
  have hs : Monotone s := by
    intro q r hqr f hf
    change minimumValue T f ≤ (q.1 : ℝ) at hf
    change minimumValue T f ≤ (r.1 : ℝ)
    exact hf.trans (by exact_mod_cast hqr)
  have hu : Monotone u := by
    intro q r hqr x hx
    change x ≤ (q.1 : ℝ) at hx
    change x ≤ (r.1 : ℝ)
    exact hx.trans (by exact_mod_cast hqr)
  have hsu : {f : Path | minimumValue T f < 0} = ⋃ q : A, s q := by
    ext f
    constructor
    · intro hf
      change minimumValue T f < 0 at hf
      obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn hf
      exact mem_iUnion.mpr ⟨⟨q,by exact_mod_cast hq2⟩,hq1.le⟩
    · intro hf
      obtain ⟨q,hq⟩ := mem_iUnion.mp hf
      change minimumValue T f ≤ (q.1 : ℝ) at hq
      exact hq.trans_lt (by exact_mod_cast q.2)
  have huu : Iio (0 : ℝ) = ⋃ q : A, u q := by
    ext x
    constructor
    · intro hx
      change x < 0 at hx
      obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn hx
      exact mem_iUnion.mpr ⟨⟨q,by exact_mod_cast hq2⟩,hq1.le⟩
    · intro hx
      obtain ⟨q,hq⟩ := mem_iUnion.mp hx
      change x ≤ (q.1 : ℝ) at hq
      exact hq.trans_lt (by exact_mod_cast q.2)
  calc
    _ = ⨆ q : A, pathLaw (s q) := by rw [hsu,hs.measure_iUnion]
    _ = ⨆ q : A, 2*gaussianReal 0 T (u q) := by
      apply iSup_congr
      intro q
      exact runningMinimum_tail (q.1 : ℝ) (by exact_mod_cast q.2) T hT
    _ = 2*gaussianReal 0 T (Iio 0) := by rw [huu,hu.measure_iUnion,ENNReal.mul_iSup]
    _ = 1 := twice_gaussian_negative_mass T hT

theorem ae_minimumValue_negative (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, minimumValue T f < 0 :=
  (mem_ae_iff_prob_eq_one ((continuous_minimumValue T).measurable measurableSet_Iio)).mpr
    (negative_minimum_mass T hT)

theorem ae_minimumValue_lt_start (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, minimumValue T f < f 0 := by
  filter_upwards [ae_minimumValue_negative T hT,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hm hf
  simpa only [hf] using hm

end PerronWright.BrownianMinimumNegative
