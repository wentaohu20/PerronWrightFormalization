import PerronWright.Probability.BrownianPathLaw
import PerronWright.Probability.DyadicGeometricExtension
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! # Quantitative common modulus for literal continuous paths

The dyadic extension of an already continuous path is proved to equal
that path. A common neighbor bound then gives a common quantitative
modulus, without assuming an equicontinuity conclusion.
-/

open Filter Topology Set
open scoped NNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.DyadicPathModulus

open BrownianPathLaw DyadicFloorGeometry DyadicGeometricApproximation DyadicGeometricExtension

def pathSamples (f : Path) (n k : ℕ) : ℝ := f (coordinate n k)

def NeighborBound (f : Path) (R : ℝ) : Prop :=
  ∀ n k, ‖pathSamples f n (k+1)-pathSamples f n k‖ ≤ R*ratio^n

theorem pathSamples_compatible (f : Path) : Compatible (pathSamples f) := by
  intro n k
  simp only [pathSamples,coordinate_succ_even]

theorem coordinate_index_distance (t : ℝ≥0) (n : ℕ) :
    dist (coordinate n (index n t)) t ≤ 1/(2 : ℝ)^n := by
  have hd : 0 < (2 : ℝ)^n := by positivity
  have h0 := index_le_scaled n t
  have h1 := scaled_lt_index_add_one n t
  rw [NNReal.dist_eq,coordinate_real,abs_sub_comm]
  have hnn : 0 ≤ (t : ℝ)-(index n t : ℝ)/(2 : ℝ)^n :=
    sub_nonneg.mpr ((div_le_iff₀ hd).mpr h0)
  rw [abs_of_nonneg hnn]
  apply le_of_lt
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ hd]
  simpa only [add_comm] using h1

theorem coordinate_index_tendsto (t : ℝ≥0) :
    Tendsto (fun n ↦ coordinate n (index n t)) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ dist_nonneg))
    (Eventually.of_forall (coordinate_index_distance t))
  simpa only [one_div,inv_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)

theorem path_samples_tendsto (f : Path) (t : ℝ≥0) :
    Tendsto (samples (pathSamples f) t) atTop (𝓝 (f t)) :=
  (continuous_path f).tendsto t |>.comp (coordinate_index_tendsto t)

theorem extension_pathSamples (f : Path) (t : ℝ≥0) : extension (pathSamples f) t = f t :=
  (path_samples_tendsto f t).limUnder_eq

theorem neighbor_localBound {f : Path} {R : ℝ} (hR : 0 ≤ R) (hf : NeighborBound f R) :
    LocalBound (pathSamples f) := fun _ ↦ ⟨R,hR,fun n k _ ↦ hf n k⟩

theorem path_samples_distance {f : Path} {R : ℝ} (hR : 0 ≤ R)
    (hf : NeighborBound f R) (t : ℝ≥0) (n : ℕ) :
    dist (samples (pathSamples f) t n) (f t) ≤ R*ratio^n/(1-ratio) := by
  obtain ⟨M,ht⟩ := exists_nat_gt (t : ℝ)
  simpa only [extension_pathSamples] using
    samples_extension_distance (pathSamples_compatible f) (neighbor_localBound hR hf)
      hR (fun n k _ ↦ hf n k) ht n

theorem path_near_bound {f : Path} {R : ℝ} (hR : 0 ≤ R)
    (hf : NeighborBound f R) {n : ℕ} {t s : ℝ≥0}
    (h : dist t s < 1/(2 : ℝ)^n) :
    dist (f t) (f s) ≤ R*(1+2/(1-ratio))*ratio^n := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max (t : ℝ) (s : ℝ))
  have ht := (le_max_left (t : ℝ) (s : ℝ)).trans_lt hM
  have hs := (le_max_right (t : ℝ) (s : ℝ)).trans_lt hM
  have hscaled : |(t : ℝ)-(s : ℝ)| * (2 : ℝ)^n < 1 :=
    (lt_div_iff₀ (by positivity : 0 < (2 : ℝ)^n)).mp h
  have hnear := samples_near_bound hR (fun n k _ ↦ hf n k) ht hs hscaled
  calc
    _ ≤ dist (f t) (samples (pathSamples f) t n)+
        dist (samples (pathSamples f) t n) (samples (pathSamples f) s n)+
        dist (samples (pathSamples f) s n) (f s) := dist_triangle4 _ _ _ _
    _ ≤ R*ratio^n/(1-ratio)+R*ratio^n+R*ratio^n/(1-ratio) := by
      rw [dist_comm (f t)]
      exact add_le_add (add_le_add (path_samples_distance hR hf t n) hnear)
        (path_samples_distance hR hf s n)
    _ = _ := by ring

theorem neighbor_uniformEquicontinuous {ι : Type*} (F : ι → Path)
    {R : ℝ} (hR : 0 ≤ R) (hF : ∀ i, NeighborBound (F i) R) :
    UniformEquicontinuous (fun i t ↦ F i t) := by
  apply Metric.uniformEquicontinuous_iff.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℕ ↦ R*(1+2/(1-ratio))*ratio^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_nonneg ratio_lt_one).const_mul
        (R*(1+2/(1-ratio)))
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨1/(2 : ℝ)^n,by positivity,?_⟩
  intro t s h i
  exact (path_near_bound hR (hF i) h).trans_lt hn

theorem pathSamples_integer_bound {f : Path} {R : ℝ} (hf : NeighborBound f R) (k : ℕ) :
    dist (pathSamples f 0 k) (f 0) ≤ (k : ℝ)*R := by
  induction k with
  | zero => simp [pathSamples,coordinate]
  | succ k ih =>
    have hs : dist (pathSamples f 0 (k+1)) (pathSamples f 0 k) ≤ R := by
      simpa only [dist_eq_norm,pow_zero,mul_one] using hf 0 k
    calc
      _ ≤ dist (pathSamples f 0 (k+1)) (pathSamples f 0 k)+dist (pathSamples f 0 k) (f 0) :=
        dist_triangle _ _ _
      _ ≤ R+(k : ℝ)*R := add_le_add hs ih
      _ = _ := by push_cast;ring

theorem path_norm_bound {f : Path} {R B : ℝ} (hR : 0 ≤ R)
    (hf : NeighborBound f R) (hB : ‖f 0‖ ≤ B) (t : ℝ≥0) :
    ‖f t‖ ≤ B+(index 0 t : ℝ)*R+R/(1-ratio) := by
  have hdist : dist (f t) (f 0) ≤ R/(1-ratio)+(index 0 t : ℝ)*R := by
    calc
      _ ≤ dist (f t) (samples (pathSamples f) t 0)+dist (samples (pathSamples f) t 0) (f 0) :=
        dist_triangle _ _ _
      _ ≤ _ := by
        rw [dist_comm (f t)]
        simpa only [pow_zero,mul_one,samples] using
          add_le_add (path_samples_distance hR hf t 0) (pathSamples_integer_bound hf (index 0 t))
  calc
    _ ≤ ‖f t-f 0‖+‖f 0‖ := by simpa only [add_comm] using norm_le_insert' (f t) (f 0)
    _ ≤ (R/(1-ratio)+(index 0 t : ℝ)*R)+B := add_le_add hdist hB
    _ = _ := by ring

end PerronWright.DyadicPathModulus
