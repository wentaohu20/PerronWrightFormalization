import PerronWright.Probability.ContinuousPathMinimumScaling

/-! # Genuine compact interval minima and strict separated perturbation

Literal compact-image infima are attained and continuous path functionals.
Uniformly separated perturbation slopes make equality of two compact
interval minima have at most one scalar solution. These are deterministic
lemmas, not Gaussian minimum or independence assumptions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathIntervalMinimum

open BrownianPathLaw

def intervalMinimum (l u : ℝ≥0) (f : Path) : ℝ := sInf ((fun t ↦ f t) '' Icc l u)

theorem continuous_intervalMinimum (l u : ℝ≥0) : Continuous (intervalMinimum l u) :=
  (isCompact_Icc (a := l) (b := u)).continuous_sInf continuous_joint_eval

theorem exists_intervalMinimum (l u : ℝ≥0) (hlu : l ≤ u) (f : Path) :
    ∃ t ∈ Icc l u, intervalMinimum l u f = f t ∧ ∀ s ∈ Icc l u, f t ≤ f s :=
  (isCompact_Icc (a := l) (b := u)).exists_sInf_image_eq_and_le
    (nonempty_Icc.mpr hlu) (continuous_path f).continuousOn

theorem intervalMinimum_le (l u : ℝ≥0) (hlu : l ≤ u) (f : Path) (t : ℝ≥0) (ht : t ∈ Icc l u) :
    intervalMinimum l u f ≤ f t := by
  obtain ⟨s,_,he,hm⟩ := exists_intervalMinimum l u hlu f
  rw [he]
  exact hm t ht

theorem intervalMinimum_eq_of_attains (l u : ℝ≥0) (hlu : l ≤ u) (f : Path)
    (a : ℝ) (hlo : ∀ t ∈ Icc l u, a ≤ f t) (hat : ∃ t ∈ Icc l u, f t = a) :
    intervalMinimum l u f = a := by
  obtain ⟨s,hs,he,_⟩ := exists_intervalMinimum l u hlu f
  obtain ⟨t,ht,he'⟩ := hat
  apply le_antisymm
  · rw [← he']
    exact intervalMinimum_le l u hlu f t ht
  · rw [he]
    exact hlo s hs

def perturbedPath (f ψ : Path) (z : ℝ) : Path :=
  ⟨fun t ↦ f t+ψ t*z,(continuous_path f).add ((continuous_path ψ).mul continuous_const)⟩

theorem measurable_joint_perturbedPath (ψ : Path) :
    Measurable (fun p : Path × ℝ ↦ perturbedPath p.1 ψ p.2) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun p : Path × ℝ ↦ fun q ↦ p.1 (BrownianGaussianSkeleton.rationalTimeReal q)+
    ψ (BrownianGaussianSkeleton.rationalTimeReal q)*p.2)
  exact measurable_pi_lambda _ (fun q ↦
    ((continuous_eval _).measurable.comp measurable_fst).add (measurable_snd.const_mul _))

theorem separated_minima_strict (l u v w : ℝ≥0) (hlu : l ≤ u) (hvw : v ≤ w)
    (f ψ : Path) (c d : ℝ) (hcd : c < d)
    (hleft : ∀ t ∈ Icc l u, ψ t ≤ c) (hright : ∀ t ∈ Icc v w, d ≤ ψ t)
    (x y : ℝ) (hxy : x < y) :
    intervalMinimum l u (perturbedPath f ψ y)-intervalMinimum v w (perturbedPath f ψ y) <
      intervalMinimum l u (perturbedPath f ψ x)-intervalMinimum v w (perturbedPath f ψ x) := by
  obtain ⟨a,ha,hea,_⟩ := exists_intervalMinimum l u hlu (perturbedPath f ψ x)
  obtain ⟨b,hb,heb,_⟩ := exists_intervalMinimum v w hvw (perturbedPath f ψ y)
  have hLy := intervalMinimum_le l u hlu (perturbedPath f ψ y) a ha
  have hRx := intervalMinimum_le v w hvw (perturbedPath f ψ x) b hb
  have hLa := hleft a ha
  have hRb := hright b hb
  change _ = f a+ψ a*x at hea
  change _ = f b+ψ b*y at heb
  change _ ≤ f a+ψ a*y at hLy
  change _ ≤ f b+ψ b*x at hRx
  have hmulL := mul_le_mul_of_nonneg_right hLa (sub_nonneg.mpr hxy.le)
  have hmulR := mul_le_mul_of_nonneg_right hRb (sub_nonneg.mpr hxy.le)
  have hstrict := mul_pos (sub_pos.mpr hcd) (sub_pos.mpr hxy)
  nlinarith

theorem separated_minima_tie_subsingleton (l u v w : ℝ≥0) (hlu : l ≤ u) (hvw : v ≤ w)
    (f ψ : Path) (c d : ℝ) (hcd : c < d)
    (hleft : ∀ t ∈ Icc l u, ψ t ≤ c) (hright : ∀ t ∈ Icc v w, d ≤ ψ t) :
    {z : ℝ | intervalMinimum l u (perturbedPath f ψ z) =
      intervalMinimum v w (perturbedPath f ψ z)}.Subsingleton := by
  intro x hx y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hxy|hyx
  · have h := separated_minima_strict l u v w hlu hvw f ψ c d hcd hleft hright x y hxy
    rw [hx,hy,sub_self,sub_self] at h
    exact lt_irrefl _ h
  · have h := separated_minima_strict l u v w hlu hvw f ψ c d hcd hleft hright y x hyx
    rw [hx,hy,sub_self,sub_self] at h
    exact lt_irrefl _ h

end PerronWright.ContinuousPathIntervalMinimum
