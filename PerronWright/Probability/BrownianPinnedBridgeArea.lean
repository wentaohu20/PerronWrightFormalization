import PerronWright.Probability.BrownianPinnedBridgeTilt
import PerronWright.Probability.BrownianUniformQuadrature

/-! # Literal continuous pinned-Brownian-bridge area

The signed area is the actual interval integral of the constructed
Brownian path bridge. Its law is proved from genuine finite quadratures
and bounded characteristic-function dominated convergence. The variance
T^3/12 is calculated, not assumed. This signed Gaussian bridge area is
not the area of a positive excursion.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPinnedBridgeArea

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianUniformQuadrature

def area (T : ℝ≥0) (f : Path) : ℝ :=
  ∫ s in 0..(T : ℝ), bridge T (Real.toNNReal s) f

def timeGrid (T : ℝ≥0) (m : ℕ) (i : Fin m) : ℝ≥0 := (i.val : ℝ≥0)*T/(m : ℝ≥0)

theorem timeGrid_le (T : ℝ≥0) (m : ℕ) (i : Fin m) : timeGrid T m i ≤ T := by
  exact grid_mem (T : ℝ) T.property m i.val (Nat.le_of_lt i.isLt) |>.2

theorem timeGrid_real (T : ℝ≥0) (m : ℕ) (i : Fin m) :
    (timeGrid T m i : ℝ) = grid (T : ℝ) m i.val := by
  simp [timeGrid,grid]

def quadrature (T : ℝ≥0) (m : ℕ) : Path → ℝ :=
  linearTest T (timeGrid T m) (fun _ ↦ (T : ℝ)/(m : ℝ))

theorem quadrature_eq_leftSum (T : ℝ≥0) (m : ℕ) (f : Path) :
    quadrature T m f = leftSum (T : ℝ) m (fun s ↦ bridge T (Real.toNNReal s) f) := by
  unfold quadrature linearTest leftSum
  simp only [timeGrid]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦
    (T : ℝ)/(m : ℝ)*bridge T ((i : ℝ≥0)*T/(m : ℝ≥0)) f)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  change timeGrid T m ⟨i,Finset.mem_range.mp hi⟩ = Real.toNNReal (grid (T : ℝ) m i)
  rw [← timeGrid_real T m ⟨i,Finset.mem_range.mp hi⟩,Real.toNNReal_coe]

theorem quadrature_tendsto_area (T : ℝ≥0) (f : Path) :
    Tendsto (fun n : ℕ ↦ quadrature T (n+1) f) atTop (𝓝 (area T f)) := by
  simp only [quadrature_eq_leftSum,area]
  exact leftSum_tendsto_integral (T : ℝ) T.property _
    ((continuous_sample_bridge T f).comp continuous_real_toNNReal)

theorem continuous_quadrature (T : ℝ≥0) (m : ℕ) : Continuous (quadrature T m) :=
  BrownianPinnedBridgeTilt.continuous_linearTest T (timeGrid T m) _

theorem measurable_area (T : ℝ≥0) : Measurable (area T) :=
  measurable_of_tendsto_metrizable (fun n ↦ (continuous_quadrature T (n+1)).measurable)
    (tendsto_pi_nhds.mpr (quadrature_tendsto_area T))

theorem quadrature_variance (T : ℝ≥0) (hT : 0 < T) (m : ℕ) (hm : 0 < m) :
    quadraticVariance T (timeGrid T m) (fun _ ↦ (T : ℝ)/(m : ℝ)) =
      (T : ℝ)^3/12*(1-1/(m : ℝ)^2) := by
  unfold quadraticVariance
  simp only [timeGrid_real]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ∑ j : Fin m,
    (T : ℝ)/(m : ℝ)*((T : ℝ)/(m : ℝ))*
      (min (grid (T : ℝ) m i) (grid (T : ℝ) m j.val)-
        grid (T : ℝ) m i*grid (T : ℝ) m j.val/(T : ℝ)))]
  have hj (i : ℕ) : (∑ j : Fin m,
      (T : ℝ)/(m : ℝ)*((T : ℝ)/(m : ℝ))*
        (min (grid (T : ℝ) m i) (grid (T : ℝ) m j.val)-
          grid (T : ℝ) m i*grid (T : ℝ) m j.val/(T : ℝ))) =
      ∑ j ∈ Finset.range m,
        (T : ℝ)/(m : ℝ)*((T : ℝ)/(m : ℝ))*
          (min (grid (T : ℝ) m i) (grid (T : ℝ) m j)-
            grid (T : ℝ) m i*grid (T : ℝ) m j/(T : ℝ)) :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
      (T : ℝ)/(m : ℝ)*((T : ℝ)/(m : ℝ))*
        (min (grid (T : ℝ) m i) (grid (T : ℝ) m j)-
          grid (T : ℝ) m i*grid (T : ℝ) m j/(T : ℝ))) m
  simp_rw [hj]
  exact grid_quadratic_sum (T : ℝ) hT m hm

theorem quadrature_variance_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ ↦ quadraticVariance T (timeGrid T (n+1))
      (fun _ ↦ (T : ℝ)/((n+1 : ℕ) : ℝ))) atTop (𝓝 ((T : ℝ)^3/12)) := by
  simp only [quadrature_variance T hT _ (Nat.succ_pos _)]
  have hd : Tendsto (fun n : ℕ ↦ 1/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hd2 := hd.pow 2
  simp only [one_div_pow,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hd2
  simpa only [sub_zero,mul_one] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub hd2).const_mul ((T : ℝ)^3/12)

private theorem integral_exp_quadrature (T : ℝ≥0) (hT : 0 < T) (m : ℕ) (s : ℝ) :
    (∫ f, Complex.exp ((s : ℂ)*(quadrature T m f : ℂ)*Complex.I) ∂pathLaw) =
      Complex.exp (-((quadraticVariance T (timeGrid T m)
        (fun _ ↦ (T : ℝ)/(m : ℝ)) : ℝ) : ℂ)*(s : ℂ)^2/2) := by
  have h := hasLaw_linearTest T hT (timeGrid T m) (timeGrid_le T m)
    (fun _ ↦ (T : ℝ)/(m : ℝ))
  have hc := congrFun (congrArg charFun h.map_eq) s
  rw [charFun_apply_real,integral_map h.aemeasurable (by fun_prop),charFun_gaussianReal] at hc
  simpa only [quadrature,Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,
    Real.coe_toNNReal _ (quadraticVariance_nonneg T hT (timeGrid T m) (timeGrid_le T m) _),
    neg_div,neg_mul] using hc

theorem integral_exp_area (T : ℝ≥0) (hT : 0 < T) (s : ℝ) :
    (∫ f, Complex.exp ((s : ℂ)*(area T f : ℂ)*Complex.I) ∂pathLaw) =
      Complex.exp (-(((T : ℝ)^3/12 : ℝ) : ℂ)*(s : ℂ)^2/2) := by
  have hchar : Continuous (fun x : ℝ ↦ Complex.exp ((s : ℂ)*(x : ℂ)*Complex.I)) := by fun_prop
  have hlim : Tendsto
      (fun n : ℕ ↦ ∫ f, Complex.exp ((s : ℂ)*(quadrature T (n+1) f : ℂ)*Complex.I) ∂pathLaw)
      atTop (𝓝 (∫ f, Complex.exp ((s : ℂ)*(area T f : ℂ)*Complex.I) ∂pathLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    · intro n
      exact (hchar.measurable.comp (continuous_quadrature T (n+1)).measurable).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun f ↦ by simp [Complex.norm_exp])
    · exact Eventually.of_forall (fun f ↦ (hchar.tendsto (area T f)).comp (quadrature_tendsto_area T f))
  have hformula : Tendsto
      (fun n : ℕ ↦ ∫ f, Complex.exp ((s : ℂ)*(quadrature T (n+1) f : ℂ)*Complex.I) ∂pathLaw)
      atTop (𝓝 (Complex.exp (-(((T : ℝ)^3/12 : ℝ) : ℂ)*(s : ℂ)^2/2))) := by
    simp only [integral_exp_quadrature T hT]
    have hc : Continuous (fun x : ℝ ↦ Complex.exp (-(x : ℂ)*(s : ℂ)^2/2)) := by fun_prop
    exact (hc.tendsto ((T : ℝ)^3/12)).comp (quadrature_variance_tendsto T hT)
  exact tendsto_nhds_unique hlim hformula

/-- Exact law of the literal signed bridge area, derived from actual
finite Brownian laws. It is not a positive-excursion area law. -/
theorem hasLaw_area (T : ℝ≥0) (hT : 0 < T) :
    HasLaw (area T) (gaussianReal 0 (Real.toNNReal ((T : ℝ)^3/12))) pathLaw := by
  refine ⟨(measurable_area T).aemeasurable,?_⟩
  apply Measure.ext_of_charFun
  funext s
  rw [charFun_apply_real,integral_map (measurable_area T).aemeasurable (by fun_prop),
    integral_exp_area T hT,charFun_gaussianReal]
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,neg_div,neg_mul,
    Real.coe_toNNReal _ (by positivity : 0 ≤ (T : ℝ)^3/12)]

theorem area_hasGaussianLaw (T : ℝ≥0) (hT : 0 < T) : HasGaussianLaw (area T) pathLaw :=
  (hasLaw_area T hT).hasGaussianLaw

theorem integral_area (T : ℝ≥0) (hT : 0 < T) : (∫ f, area T f ∂pathLaw) = 0 := by
  rw [(hasLaw_area T hT).integral_eq,integral_id_gaussianReal]

theorem variance_area (T : ℝ≥0) (hT : 0 < T) : Var[area T;pathLaw] = (T : ℝ)^3/12 := by
  rw [(hasLaw_area T hT).variance_eq]
  rw [variance_id_gaussianReal,Real.coe_toNNReal _ (by positivity : 0 ≤ (T : ℝ)^3/12)]

private theorem measurable_area_from_bridge (T : ℝ≥0) :
    Measurable[MeasurableSpace.comap (fun f : Path ↦ fun t : Iic T ↦ bridge T t f)
      inferInstance] (area T) := by
  let B := fun f : Path ↦ fun t : Iic T ↦ bridge T t f
  let m : MeasurableSpace Path := MeasurableSpace.comap B inferInstance
  have hB : Measurable[m] B := comap_measurable B
  have hq (n : ℕ) : Measurable[m] (quadrature T (n+1)) := by
    unfold quadrature linearTest
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply ⟨timeGrid T (n+1) i,timeGrid_le T (n+1) i⟩).comp hB).const_mul _
  let : MeasurableSpace Path := m
  exact measurable_of_tendsto_metrizable hq
    (tendsto_pi_nhds.mpr (quadrature_tendsto_area T))

theorem area_independent_endpoint (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (area T) (fun f : Path ↦ f T) pathLaw := by
  apply (IndepFun_iff _ _ _).mpr
  intro u v hu hv
  exact ((IndepFun_iff _ _ _).mp (bridge_process_independent_endpoint T hT)) u v
    ((measurable_area_from_bridge T).comap_le u hu) hv

theorem area_endpoint_jointLaw_eq_prod (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f : Path ↦ (area T f,f T)) =
      (gaussianReal 0 (Real.toNNReal ((T : ℝ)^3/12))).prod (gaussianReal 0 T) := by
  rw [(area_independent_endpoint T hT).map_prod_eq_prod_map_map
    (measurable_area T).aemeasurable (continuous_eval T).measurable.aemeasurable,
    (hasLaw_area T hT).map_eq,isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T |>.map_eq]

end PerronWright.BrownianPinnedBridgeArea
