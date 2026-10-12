import PerronWright.Probability.CriticalEnumeratorExponent
import PerronWright.Probability.FactorialWindowBounds
import PerronWright.Probability.CriticalStirlingNormalization

/-! # Exact size-factor rescaling for literal local component floors -/

open Filter Topology
open scoped Real Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CriticalLocalSizeFactor

theorem sizeFactor_scaled_identity (beta : ℝ) {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (r : ℕ) :
    (n : ℝ)^(5/3-(r : ℝ)) * FactorialDensity.sizeFactor beta (k : ℝ) r =
      FactorialDensity.sizeFactor beta ((k : ℝ)/(n : ℝ)^(2/3 : ℝ)) r := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hp : ((k : ℝ)/(n : ℝ)^(2/3 : ℝ))^(3*(r : ℝ)/2-5/2) =
      (k : ℝ)^(3*(r : ℝ)/2-5/2) * (n : ℝ)^(5/3-(r : ℝ)) := by
    rw [Real.div_rpow hkR.le (Real.rpow_nonneg hnR.le _),
      ← Real.rpow_mul hnR.le,div_eq_mul_inv,← Real.rpow_neg hnR.le]
    congr 1
    congr 1
    ring
  unfold FactorialDensity.sizeFactor
  rw [hp]
  ring

theorem sizeFactor_continuousAt_positive (beta : ℝ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun x ↦ FactorialDensity.sizeFactor beta x r) x := by
  unfold FactorialDensity.sizeFactor
  exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hx.ne'))

/-- The exact scaled factor converges for the actual integer floor, not
for a continuous-size replacement assumed asymptotically equivalent. -/
theorem scaled_sizeFactor_tendsto_floor (beta : ℝ) (r : ℕ)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ m, 0 ≤ x m) {s : ℝ} (hs : 0 < s)
    (hxs : Tendsto x atTop (𝓝 s)) :
    Tendsto (fun m ↦ (N m : ℝ)^(5/3-(r : ℝ)) *
      FactorialDensity.sizeFactor beta (CriticalScaling.size (x m) (N m) : ℝ) r)
      atTop (𝓝 (FactorialDensity.sizeFactor beta s r)) := by
  have hk := CriticalSizeTuple.size_normalized_varying_tendsto N hN hNt x hx hxs
  have hpos : ∀ᶠ m in atTop, 0 < CriticalScaling.size (x m) (N m) := by
    filter_upwards [hk.eventually (Ioi_mem_nhds hs)] with m hm
    have hn : (0 : ℝ) < (N m : ℝ)^(2/3 : ℝ) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hN m)) _
    have h : (0 : ℝ) < CriticalScaling.size (x m) (N m) :=
      (div_pos_iff_of_pos_right hn).mp hm
    exact Nat.cast_pos.mp h
  have ht := (sizeFactor_continuousAt_positive beta r hs).tendsto.comp hk
  apply ht.congr'
  filter_upwards [hpos] with m hm
  exact (sizeFactor_scaled_identity beta hm (hN m) r).symm

theorem scaled_sizeFactor_gaussian_tendsto_floor (beta gamma lambda : ℝ) (r : ℕ)
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ m, 0 ≤ x m) {s : ℝ} (hs : 0 < s)
    (hxs : Tendsto x atTop (𝓝 s)) :
    Tendsto (fun m ↦ (N m : ℝ)^(5/3-(r : ℝ)) *
      FactorialDensity.sizeFactor beta (CriticalScaling.size (x m) (N m) : ℝ) r *
      Real.exp (-gamma*(CriticalScaling.time lambda (N m)-1)^2*
        (CriticalScaling.size (x m) (N m) : ℝ)))
      atTop (𝓝 (FactorialDensity.sizeFactor beta s r * Real.exp (-gamma*(lambda^2*s)))) := by
  have hsize := scaled_sizeFactor_tendsto_floor beta r N hN hNt x hx hs hxs
  have hnorm := CriticalSizeTuple.size_normalized_varying_tendsto N hN hNt x hx hxs
  have hrate := (CriticalEnumeratorExponent.quadratic_time_size_tendsto
    N (fun m ↦ CriticalScaling.size (x m) (N m)) hN hNt lambda hnorm).const_mul (-gamma)
  have he := (Real.continuous_exp.tendsto _).comp hrate
  have h := hsize.mul he
  simpa only [neg_mul,mul_assoc,Function.comp_def] using h

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal factorial-divided connected enumeration, on the local
graph scale, has the actual size-factor Gaussian limit. This is the
enumeration contribution; the component selection/residual contribution
is a separate probabilistic step. -/
theorem single_component_enumeration_tendsto (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (r : ℕ) (N : ℕ → ℕ)
    (hN : ∀ m, 0 < N m) (hNt : Tendsto N atTop atTop)
    (x : ℕ → ℝ) (lambda a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hxa : ∀ m, a ≤ x m) (hxb : ∀ m, x m ≤ b)
    {s : ℝ} (hs : 0 < s) (hxs : Tendsto x atTop (𝓝 s)) :
    Tendsto (fun m ↦ (N m : ℝ)^(5/3-(r : ℝ)) *
      (M.connectedWeight (CriticalScaling.time lambda (N m))
        (CriticalScaling.size (x m) (N m)) r /
        ((CriticalScaling.size (x m) (N m)).factorial : ℝ)))
      atTop (𝓝 (FactorialDensity.sizeFactor (M.beta hM) s r *
        Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM*(lambda^2*s)))) := by
  let k m := CriticalScaling.size (x m) (N m)
  have hx (m) : 0 ≤ x m := ha.le.trans (hxa m)
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [CriticalConnectedSampling.eventually_size_ge_on_window N hNt a ha K] with m hm
    exact hm (x m) (hxa m)
  have hsize : ∀ᶠ m in atTop, (k m : ℝ) ≤ b*(N m : ℝ)^(2/3 : ℝ) :=
    Eventually.of_forall (fun m ↦ (CriticalSizeTuple.size_le_scaled (hx m) _).trans
      (mul_le_mul_of_nonneg_right (hxb m) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hratio := CriticalStirlingNormalization.connectedWeight_div_factorial_gaussian_ratio_tendsto_one
    M hM r N k (fun _ ↦ r) hN hNt hk lambda b hb hsize (Eventually.of_forall (fun _ ↦ le_rfl))
  have hmain := scaled_sizeFactor_gaussian_tendsto_floor (M.beta hM)
    (CriticalWindowRadiusConversion.criticalQuadraticRate M hM) lambda r N hN hNt x hx hs hxs
  have ht := hratio.mul hmain
  rw [one_mul] at ht
  apply ht.congr'
  filter_upwards [hk.eventually (eventually_ge_atTop 1)] with m hm
  have hkR : (0 : ℝ) < k m := Nat.cast_pos.mpr (by omega)
  have hSF : FactorialDensity.sizeFactor (M.beta hM) (k m : ℝ) r ≠ 0 :=
    (FactorialDensity.sizeFactor_pos (M.beta_pos hM) hkR r).ne'
  have hE : Real.exp (-CriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (k m : ℝ)*(CriticalScaling.time lambda (N m)-1)^2) ≠ 0 := (Real.exp_pos _).ne'
  change (M.connectedWeight _ (k m) r / ((k m).factorial : ℝ)) /
      (FactorialDensity.sizeFactor (M.beta hM) (k m : ℝ) r * Real.exp (_)) *
      ((N m : ℝ)^(5/3-(r : ℝ)) * FactorialDensity.sizeFactor (M.beta hM) (k m : ℝ) r *
        Real.exp (_)) = _
  rw [show -CriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (CriticalScaling.time lambda (N m)-1)^2*(k m : ℝ) =
    -CriticalWindowRadiusConversion.criticalQuadraticRate M hM *
      (k m : ℝ)*(CriticalScaling.time lambda (N m)-1)^2 by ring]
  field_simp
  all_goals ring

end PerronWright.CriticalLocalSizeFactor
