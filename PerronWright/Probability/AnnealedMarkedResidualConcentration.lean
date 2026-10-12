import PerronWright.Probability.AnnealedMarkedResidualTransfer

/-!
# Joint component weak marks under the actual residual-weighted law

Each component mark concentrates by its genuine connected-law theorem.
Actual pi marginals and finite unions give joint concentration.  The
literal residual L1 theorem transfers this to the genuine weighted laws.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedResidualConcentration

open AnnealedMarkedResidualLaw AnnealedMarkedResidualTransfer EmpiricalTypeMarks
  EmpiricalMarkConcentration EmpiricalMarkWeakConcentration ProfileFiniteCollection
  AnnealedProfileFunctionalObservable AnnealedProfileFunctionalExpectation
  AnnealedTupleResidualCounting

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def componentMarks {q : ℕ} {k : Fin q → ℕ} (hk : ∀ i, 0 < k i)
    (p : StateFamily (S := S) k) : Fin q → ProbabilityMeasure S :=
  fun i ↦ connectedMark (hk i) (p i)

def perronMarks (M : CompactBJRModel S) (hM : M.IsRegularCritical) (q : ℕ) : Fin q → ProbabilityMeasure S :=
  fun _ ↦ perronMark M hM

theorem component_probability_outside_weak_nhds_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R q : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i) (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ)*‖g n i‖ ≤ L)
    (i : Fin q) (U : Set (ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMark M hM)) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | componentMarks (hk n) p i ∉ U}) atTop (𝓝 0) := by
  have hh := connectedMark_probability_outside_weak_nhds_tendsto_zero M hM R L hL
    (fun n ↦ k n i) (fun n ↦ r n i) (fun n ↦ hk n i) (fun n ↦ g n i) (fun n ↦ hC n i)
    (hkTop i) (hr.mono (fun n hn ↦ hn i)) (hg.mono (fun n hn ↦ hn i)) U hU
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hh
  exact Eventually.of_forall (fun n ↦ measurePreserving_real_preimage_le
    (measurePreserving_eval (fun i ↦ ConnectedTypeLaw.law M (g n i) (k n i) (r n i) (hC n i)) i)
    {p | connectedMark (hk n i) p ∉ U})

theorem joint_probability_outside_coordinate_nhds_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R q : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i) (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ)*‖g n i‖ ≤ L)
    (U : Fin q → Set (ProbabilityMeasure S)) (hU : ∀ i, U i ∈ 𝓝 (perronMark M hM)) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | ∃ i, componentMarks (hk n) p i ∉ U i}) atTop (𝓝 0) := by
  have hh : Tendsto (fun n ↦ ∑ i : Fin q, (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | componentMarks (hk n) p i ∉ U i}) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ ↦
      component_probability_outside_weak_nhds_tendsto_zero M hM R q L hL k r hk g hC hkTop hr hg i (U i) (hU i))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hh
  exact Eventually.of_forall (fun n ↦ by
    have he : {p : StateFamily (S := S) (k n) | ∃ i, componentMarks (hk n) p i ∉ U i} =
        ⋃ i ∈ (Finset.univ : Finset (Fin q)), {p | componentMarks (hk n) p i ∉ U i} := by ext p; simp
    rw [he]
    exact measureReal_biUnion_finset_le _ _)

/-- Genuine joint weak-neighborhood concentration, not merely pooled
mark concentration.  Neighborhoods need not be measurable. -/
theorem joint_probability_outside_weak_nhds_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R q : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i) (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ)*‖g n i‖ ≤ L)
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMarks M hM q)) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | componentMarks (hk n) p ∉ U}) atTop (𝓝 0) := by
  rw [nhds_pi] at hU
  obtain ⟨I,V,hV,hVU⟩ := Filter.mem_pi'.mp hU
  have hh := joint_probability_outside_coordinate_nhds_tendsto_zero M hM R q L hL k r hk g hC
    hkTop hr hg V hV
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hh
  exact Eventually.of_forall (fun n ↦ measureReal_mono (by
    intro p hp
    by_contra hbad
    apply hp
    apply hVU
    intro i _
    by_contra hnot
    exact hbad ⟨i,hnot⟩))

theorem totalSize_tendsto_of_components (q : ℕ) (hq : 0 < q)
    (k : ℕ → Fin q → ℕ) (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop) :
    Tendsto (fun n ↦ ∑ i,(k n i:ℝ)) atTop atTop := by
  let i : Fin q := ⟨0,hq⟩
  exact tendsto_atTop_mono (fun n ↦ Finset.single_le_sum (fun j _ ↦ Nat.cast_nonneg (k n j))
    (Finset.mem_univ i)) (tendsto_natCast_atTop_atTop.comp (hkTop i))

section Critical

variable (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
  (R q : ℕ) (hq : 0 < q) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C) (lambda : ℝ)
  (N : ℕ → ℕ) (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
  (f : ∀ n, Placements (N n) (k n)) (s₀ : S)
  (hweight : ∀ n i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda (N n)))
    (k n i) (r n i))
  (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
  (hkTop : ∀ i, Tendsto (fun n ↦ k n i) atTop atTop)
  (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
  (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i:ℝ) *
    ‖M.scalarField (CriticalScaling.time lambda (N n))‖ ≤ L)
  (hsize : ∀ᶠ n in atTop, (∑ i,(k n i:ℝ)) ≤ C*(N n:ℝ)^(2/3:ℝ))
  {s : ℝ} (hs : Tendsto (fun n ↦ (∑ i,k n i:ℕ)/(N n:ℝ)^(2/3:ℝ)) atTop (𝓝 s))

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
theorem normalizedDensity_l1_tendsto_zero :
    Tendsto (fun n ↦ ∫ p,
      |normalizedResidualObservable M hM lambda (hk n) (f n) s₀ p /
        (∫ z, normalizedResidualObservable M hM lambda (hk n) (f n) s₀ z
          ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))-1|
      ∂productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n))
        atTop (𝓝 0) := by
  let μ n := productLaw M (k n) (r n) (fun _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) (hweight n)
  let F n := normalizedResidualObservable M hM lambda (hk n) (f n) s₀
  let Z n := ∫ p, F n p ∂μ n
  have hh := normalizedResidualObservable_l1_and_mean_tendsto M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt (totalSize_tendsto_of_components q hq k hkTop) hr hg hsize hs
  have hz : Tendsto Z atTop (𝓝 1) := hh.2
  have habs : Tendsto (fun n ↦ |Z n-1|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hz.sub (tendsto_const_nhds (x := (1:ℝ)))).abs
  have hl : Tendsto (fun n ↦ ∫ p, |F n p-1| ∂μ n) atTop (𝓝 0) := hh.1
  have hu : Tendsto (fun n ↦ ((∫ p, |F n p-1| ∂μ n)+|Z n-1|)/Z n) atTop (𝓝 0) := by
    convert (hl.add habs).div hz (by norm_num : (1:ℝ) ≠ 0) using 1 <;>
      first | rfl | norm_num
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ integral_nonneg (fun _ ↦ abs_nonneg _))) _ hu
  exact Eventually.of_forall (fun n ↦ integral_abs_normalized_density_sub_one_le (μ n) (F n)
    (normalizedResidualObservable_integrable_alltime M hM lambda (hN n) (hk n) (f n) s₀ (hweight n))
    (residualExpectation_pos M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)))

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
/-- Every genuine joint weak bad-neighborhood has vanishing literal
normalized-residual weighted mass.  Its measurability is not assumed. -/
theorem weightedMeasure_outside_joint_weak_nhds_tendsto_zero
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMarks M hM q)) :
    Tendsto (fun n ↦ (weightedMeasure M hM lambda (hk n) (f n) s₀ (hweight n)).real
      {p | componentMarks (hk n) p ∉ U}) atTop (𝓝 0) := by
  have hbad := joint_probability_outside_weak_nhds_tendsto_zero M hM R q L hL k r hk
    (fun n _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) hweight hkTop hr hg U hU
  have hF := (normalizedResidualObservable_l1_and_mean_tendsto M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt (totalSize_tendsto_of_components q hq k hkTop) hr hg hsize hs).1
  have hu := hbad.add hF
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hu
  exact Eventually.of_forall (fun n ↦ densityMeasure_real_le _ _
    (normalizedResidualObservable_integrable_alltime M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)) _)

include hQP hq hL hC hN hNt hkTop hr hg hsize hs in
/-- Joint component weak marks still concentrate under the actual
probability law obtained by dividing by the genuine residual expectation. -/
theorem weightedLaw_outside_joint_weak_nhds_tendsto_zero
    (U : Set (Fin q → ProbabilityMeasure S)) (hU : U ∈ 𝓝 (perronMarks M hM q)) :
    Tendsto (fun n ↦ (weightedLaw M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).toMeasure.real
      {p | componentMarks (hk n) p ∉ U}) atTop (𝓝 0) := by
  have hbad := joint_probability_outside_weak_nhds_tendsto_zero M hM R q L hL k r hk
    (fun n _ ↦ M.scalarField (CriticalScaling.time lambda (N n))) hweight hkTop hr hg U hU
  have hF := normalizedDensity_l1_tendsto_zero M hM hQP R q hq L C hL hC lambda
    N k r hk f s₀ hweight hN hNt hkTop hr hg hsize hs
  have hu := hbad.add hF
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ measureReal_nonneg)) _ hu
  exact Eventually.of_forall (fun n ↦ densityMeasure_real_le _ _
    ((normalizedResidualObservable_integrable_alltime M hM lambda (hN n) (hk n) (f n) s₀ (hweight n)).div_const _) _)

end Critical

end PerronWright.AnnealedMarkedResidualConcentration
