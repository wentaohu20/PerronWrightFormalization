import PerronWright.Probability.BrownianKilledBoundaryInsertionRecurrence
import PerronWright.Probability.BrownianKilledFreeEntranceGeometry

/-! # Genuine height-weighted Green chains

Finite-dimensional Lebesgue disintegration and the already proved Kac
insertion recursion identify the literal Green state chain with the
actual boundary slope. All orders, including the empty chain, are real
state-vector integrals; no area-duration identity is a premise.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBoundaryGreenStateChain

open BrownianKilledBoundaryInsertionRecurrence BrownianKilledAreaMomentResolvent
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFreeEntranceGeometry

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def stateHeightWeight (n : ℕ) (v : FreeVector n) : ℝ≥0∞ := ∏ i, ENNReal.ofReal (v i)

theorem measurable_stateHeightWeight (n : ℕ) : Measurable (stateHeightWeight n) := by
  unfold stateHeightWeight
  exact Finset.measurable_prod _ (fun i _ ↦ (measurable_pi_apply i).ennreal_ofReal)

private def kernelStateChain : (n : ℕ) → (ℝ → ℝ → ℝ≥0∞) → (ℝ → ℝ≥0∞) →
    ℝ → FreeVector n → ℝ≥0∞
  | 0, _, H, y, _ => H y
  | n+1, K, H, y, v => K y (v 0)*ENNReal.ofReal (v 0)*
      kernelStateChain n K H (v 0) (Fin.tail v)

def anchoredStateChain (n : ℕ) (p y : ℝ) (v : FreeVector n) : ℝ≥0∞ :=
  kernelStateChain n (resolvent 0 p) (boundarySlopeNN 0 p) y v

theorem anchoredStateChain_freeCons (n : ℕ) (p y z : ℝ) (v : FreeVector n) :
    anchoredStateChain (n+1) p y (freeCons n (z,v)) =
      resolvent 0 p y z*ENNReal.ofReal z*anchoredStateChain n p z v := by
  simp only [anchoredStateChain,kernelStateChain,freeCons,Fin.cons_zero,Fin.tail_cons]

theorem measurable_anchoredStateChain (n : ℕ) (p : ℝ) :
    Measurable (fun q : ℝ × FreeVector n ↦ anchoredStateChain n p q.1 q.2) := by
  induction n with
  | zero =>
    change Measurable (fun q : ℝ × FreeVector 0 ↦ boundarySlopeNN 0 p q.1)
    exact (measurable_boundarySlopeNN 0 p).comp measurable_fst
  | succ n ih =>
    have h0 : Measurable (fun q : ℝ × FreeVector (n+1) ↦ q.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    have ht : Measurable (fun q : ℝ × FreeVector (n+1) ↦ Fin.tail q.2) := by
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply i.succ).comp measurable_snd
    have hk := (measurable_resolvent 0 p).comp (measurable_fst.prodMk h0)
    change Measurable (fun q : ℝ × FreeVector (n+1) ↦
      resolvent 0 p q.1 (q.2 0)*ENNReal.ofReal (q.2 0)*
        anchoredStateChain n p (q.2 0) (Fin.tail q.2))
    exact (hk.mul h0.ennreal_ofReal).mul (ih.comp (h0.prodMk ht))

private theorem measurable_kernelStateChain_joint (n : ℕ)
    (K : ℝ → ℝ → ℝ≥0∞) (H : ℝ → ℝ≥0∞)
    (hK : Measurable (fun q : ℝ × ℝ ↦ K q.1 q.2)) (hH : Measurable H) :
    Measurable (fun q : ℝ × FreeVector n ↦ kernelStateChain n K H q.1 q.2) := by
  induction n with
  | zero => exact hH.comp measurable_fst
  | succ n ih =>
    have h0 : Measurable (fun q : ℝ × FreeVector (n+1) ↦ q.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    have ht : Measurable (fun q : ℝ × FreeVector (n+1) ↦ Fin.tail q.2) :=
      measurable_pi_lambda _ (fun i ↦ (measurable_pi_apply i.succ).comp measurable_snd)
    exact ((hK.comp (measurable_fst.prodMk h0)).mul h0.ennreal_ofReal).mul
      (ih.comp (h0.prodMk ht))

private theorem measurable_kernelStateChain_fixed (n : ℕ)
    (K : ℝ → ℝ → ℝ≥0∞) (H : ℝ → ℝ≥0∞)
    (hK : Measurable (fun q : ℝ × ℝ ↦ K q.1 q.2)) (hH : Measurable H) (y : ℝ) :
    Measurable (kernelStateChain n K H y) := by
  have h := (measurable_kernelStateChain_joint n K H hK hH).comp
    (show Measurable (fun v : FreeVector n ↦ (y,v)) from
      measurable_const.prodMk measurable_id)
  simpa only [Function.comp_def] using h

private theorem kernelStateChain_eq_product (n : ℕ)
    (K : ℝ → ℝ → ℝ≥0∞) (H : ℝ → ℝ≥0∞) (y : ℝ) (v : FreeVector n) :
    kernelStateChain n K H y v =
      (∏ i : Fin n, K (prependInitial n y v i.castSucc) (v i))*
        stateHeightWeight n v*H (lastState n y v) := by
  induction n generalizing y with
  | zero =>
    simp [kernelStateChain,stateHeightWeight,lastState,prependInitial,Fin.last_zero]
  | succ n ih =>
    have hv : freeCons n (v 0,Fin.tail v) = v := by
      simpa only [freeCons] using Fin.cons_self_tail v
    rw [← hv]
    simp only [kernelStateChain,freeCons,Fin.cons_zero,Fin.tail_cons]
    rw [ih]
    simp only [stateHeightWeight,Fin.prod_univ_succ,prependInitial,Fin.cons_zero,
      Fin.cons_succ,Fin.castSucc_zero,lastState]
    have hlast : (Fin.cons y (Fin.cons (v 0) (Fin.tail v)) : FreeVector (n+2)) (Fin.last (n+1)) =
        (Fin.cons (v 0) (Fin.tail v) : FreeVector (n+1)) (Fin.last n) := by
      rw [← Fin.succ_last,Fin.cons_succ]
    rw [hlast]
    have hprod : (∏ i : Fin n,
        K ((Fin.cons y (Fin.cons (v 0) (Fin.tail v)) : FreeVector (n+2)) i.succ.castSucc)
          (Fin.tail v i)) =
        ∏ i : Fin n, K ((Fin.cons (v 0) (Fin.tail v) : FreeVector (n+1)) i.castSucc) (Fin.tail v i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Fin.succ_castSucc,Fin.cons_succ]
    rw [hprod]
    ac_rfl

theorem anchoredStateChain_eq_product (n : ℕ) (p y : ℝ) (v : FreeVector n) :
    anchoredStateChain n p y v =
      (∏ i : Fin n, resolvent 0 p (prependInitial n y v i.castSucc) (v i))*
        stateHeightWeight n v*boundarySlopeNN 0 p (lastState n y v) :=
  kernelStateChain_eq_product n (resolvent 0 p) (boundarySlopeNN 0 p) y v

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem factorial_stateChain_eq_actual_boundary (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    (n.factorial : ℝ≥0∞)*(∫⁻ v : FreeVector n, anchoredStateChain n p y v) =
      boundarySlopeNN n p y := by
  induction n generalizing y with
  | zero =>
    simp only [Nat.factorial_zero,Nat.cast_one,one_mul,anchoredStateChain,kernelStateChain,lintegral_const,
      volume_pi,Measure.pi_empty_univ,mul_one]
  | succ n ih =>
    have hm : Measurable (anchoredStateChain (n+1) p y) :=
      measurable_kernelStateChain_fixed (n+1) (resolvent 0 p) (boundarySlopeNN 0 p)
        (measurable_resolvent 0 p) (measurable_boundarySlopeNN 0 p) y
    have htail (z : ℝ) : Measurable (anchoredStateChain n p z) :=
      measurable_kernelStateChain_fixed n (resolvent 0 p) (boundarySlopeNN 0 p)
        (measurable_resolvent 0 p) (measurable_boundarySlopeNN 0 p) z
    rw [lintegral_volume_freeCons n hm]
    simp_rw [anchoredStateChain_freeCons,lintegral_const_mul _ (htail _)]
    rw [Nat.factorial_succ,Nat.cast_mul,mul_assoc]
    have hpull : (n.factorial : ℝ≥0∞)*
        (∫⁻ z : ℝ, (resolvent 0 p y z*ENNReal.ofReal z)*
          (∫⁻ v : FreeVector n, anchoredStateChain n p z v)) =
        ∫⁻ z : ℝ, (resolvent 0 p y z*ENNReal.ofReal z)*boundarySlopeNN n p z := by
      rw [← lintegral_const_mul' _ _ (by simp : (n.factorial : ℝ≥0∞) ≠ ⊤)]
      apply lintegral_congr
      intro z
      calc
        _ = (resolvent 0 p y z*ENNReal.ofReal z)*
            ((n.factorial : ℝ≥0∞)*(∫⁻ v : FreeVector n, anchoredStateChain n p z v)) := by ac_rfl
        _ = _ := by rw [ih z]
    rw [hpull]
    exact (boundarySlopeNN_recurrence n p hp y).symm

end PerronWright.BrownianBoundaryGreenStateChain
