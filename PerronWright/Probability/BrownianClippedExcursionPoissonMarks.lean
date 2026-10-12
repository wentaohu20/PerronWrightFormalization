import PerronWright.Probability.BrownianWindowExcursionAreas
import PerronWright.Probability.CountablePoissonKernel

/-!
# Actual area-rate countable Poisson marks of clipped Brownian excursions

The rates are the proved literal areas of the nonrepeating rational
component section. Encoding is injective and decoding recovers every
rational anchor; unused codes and duplicate anchors have zero rate.
The genuine countable Poisson kernel constructs the conditional marking
law and an actual Brownian-source/count joint probability law. These are
clipped-window marks, not a spatial Poisson process or an excursion-density
identity, and unconditional independence is not asserted.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianClippedExcursionPoissonMarks

open BrownianPathLaw BrownianWindowExcursions BrownianWindowExcursionAreas
open BrownianPathReflectionLaw BrownianGaussianSkeleton

def naturalRates (H lambda : ℝ) (f : Path) (n : ℕ) : ℝ≥0 :=
  match Encodable.decode₂ ℚ n with
  | none => 0
  | some q => retainedArea H lambda q f

theorem measurable_naturalRates (H lambda : ℝ) : Measurable (naturalRates H lambda) := by
  apply measurable_pi_lambda
  intro n
  cases hn : Encodable.decode₂ ℚ n with
  | none => simpa only [naturalRates,hn] using (measurable_const : Measurable (fun _ : Path ↦ (0 : ℝ≥0)))
  | some q =>
      simpa only [naturalRates,hn,Function.comp_def,areaData] using
        (measurable_pi_apply q).comp (measurable_areaData H lambda)

theorem measurable_naturalRates_all_parameters (H : ℝ) : Measurable
    (fun p : ℝ × Path ↦ naturalRates H p.1 p.2) := by
  apply measurable_pi_lambda
  intro n
  cases hn : Encodable.decode₂ ℚ n with
  | none => simpa only [naturalRates,hn] using
      (measurable_const : Measurable (fun _ : ℝ × Path ↦ (0 : ℝ≥0)))
  | some q =>
      simpa only [naturalRates,hn] using measurable_retainedArea_all_parameters H q

@[simp] theorem naturalRates_encode (H lambda : ℝ) (f : Path) (q : ℚ) :
    naturalRates H lambda f (Encodable.encode q) = retainedArea H lambda q f := by
  simp only [naturalRates,Encodable.decode₂_encode]

theorem naturalRates_eq_zero_outside_range {H lambda : ℝ} {f : Path} {n : ℕ}
    (hn : n ∉ Set.range (Encodable.encode : ℚ → ℕ)) : naturalRates H lambda f n = 0 := by
  have hd : Encodable.decode₂ ℚ n = none := by
    apply not_ne_iff.mp
    intro hne
    exact hn (Encodable.decode₂_ne_none_iff.mp hne)
  simp only [naturalRates,hd]

theorem naturalRates_eq_area_of_representative {H lambda : ℝ} {f : Path} {q : ℚ}
    (hq : Representative H (driftedReflectionPath lambda f) q) :
    naturalRates H lambda f (Encodable.encode q) = excursionArea H (q : ℝ) lambda f := by
  rw [naturalRates_encode]
  exact if_pos hq

theorem naturalRates_eq_zero_of_not_representative {H lambda : ℝ} {f : Path} {q : ℚ}
    (hq : ¬Representative H (driftedReflectionPath lambda f) q) :
    naturalRates H lambda f (Encodable.encode q) = 0 := by
  rw [naturalRates_encode]
  exact if_neg hq

def rationalCount (m : ℕ → ℕ) (q : ℚ) : ℕ := m (Encodable.encode q)

def markLaw (H lambda : ℝ) (f : Path) : Measure (ℕ → ℕ) :=
  CountablePoissonKernel.countLaw (naturalRates H lambda f)

instance (H lambda : ℝ) (f : Path) : IsProbabilityMeasure (markLaw H lambda f) :=
  inferInstanceAs (IsProbabilityMeasure (CountablePoissonKernel.countLaw (naturalRates H lambda f)))

theorem measurable_markLaw (H lambda : ℝ) : Measurable (markLaw H lambda) :=
  CountablePoissonKernel.measurable_countLaw.comp (measurable_naturalRates H lambda)

/-- True conditional Poisson laws at the actual rational component areas. -/
theorem markLaw_hasLaw_rationalCount (H lambda : ℝ) (f : Path) (q : ℚ) :
    HasLaw (fun m ↦ rationalCount m q) (poissonMeasure (retainedArea H lambda q f)) (markLaw H lambda f) := by
  simpa only [markLaw,rationalCount,naturalRates_encode] using
    CountablePoissonKernel.countLaw_hasLaw_eval (naturalRates H lambda f) (Encodable.encode q)

theorem markLaw_rationalCounts_independent (H lambda : ℝ) (f : Path) :
    iIndepFun (fun q (m : ℕ → ℕ) ↦ rationalCount m q) (markLaw H lambda f) :=
  iIndepFun.precomp Encodable.encode_injective (CountablePoissonKernel.countLaw_independent (naturalRates H lambda f))

theorem markLaw_finite_rational_count_event (H lambda : ℝ) (f : Path)
    (I : Finset ℚ) (k : ℚ → ℕ) :
    markLaw H lambda f (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) =
      ∏ q ∈ I, ENNReal.ofReal (Real.exp (-(retainedArea H lambda q f : ℝ)) *
        (retainedArea H lambda q f : ℝ) ^ k q / ((k q).factorial : ℝ)) := by
  have hi := (markLaw_rationalCounts_independent H lambda f).measure_inter_preimage_eq_mul
    I (sets := fun q ↦ {k q}) (fun q _ ↦ measurableSet_singleton (k q))
  have hs : (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) =
      (⋂ q ∈ I, (fun m : ℕ → ℕ ↦ rationalCount m q) ⁻¹' {k q}) := by
    ext m
    simp only [mem_iInter,mem_ofPred_eq,mem_preimage,mem_singleton_iff]
  rw [hs,hi]
  apply Finset.prod_congr rfl
  intro q _
  calc
    _ = poissonMeasure (retainedArea H lambda q f) {k q} := by
      convert (markLaw_hasLaw_rationalCount H lambda f q).measure_eq
        (measurableSet_singleton (k q)) using 1
      · congr 1
      · congr 1
    _ = _ := poissonMeasure_singleton _ _

theorem ae_markLaw_zero_at_zero_rate (H lambda : ℝ) (f : Path) (n : ℕ)
    (hn : naturalRates H lambda f n = 0) :
    ∀ᵐ m ∂markLaw H lambda f, m n = 0 := by
  rw [ae_iff_prob_eq_one ((measurable_pi_apply n).eq measurable_const)]
  have hm := (CountablePoissonKernel.countLaw_hasLaw_eval
    (naturalRates H lambda f) n).measure_eq
      (show MeasurableSet {a : ℕ | a = 0} from measurableSet_singleton 0)
  change CountablePoissonKernel.countLaw (naturalRates H lambda f) {m | m n = 0} = 1
  rw [hm,hn]
  simp [ofPred_eq_eq_singleton,poissonMeasure_singleton]

/-- Zero rates really suppress duplicate representatives and unused codes. -/
theorem ae_markLaw_inactive_counts_zero (H lambda : ℝ) (f : Path) :
    ∀ᵐ m ∂markLaw H lambda f,
      (∀ q : ℚ, ¬Representative H (driftedReflectionPath lambda f) q → rationalCount m q = 0) ∧
      (∀ n : ℕ, n ∉ Set.range (Encodable.encode : ℚ → ℕ) → m n = 0) := by
  have hq : ∀ᵐ m ∂markLaw H lambda f,
      ∀ q : ℚ, ¬Representative H (driftedReflectionPath lambda f) q → rationalCount m q = 0 := by
    rw [ae_all_iff]
    intro q
    by_cases hq : Representative H (driftedReflectionPath lambda f) q
    · exact Eventually.of_forall (fun _ ↦ fun h ↦ (h hq).elim)
    · exact (ae_markLaw_zero_at_zero_rate H lambda f (Encodable.encode q)
        (naturalRates_eq_zero_of_not_representative hq)).mono (fun _ h _ ↦ h)
  have hn : ∀ᵐ m ∂markLaw H lambda f,
      ∀ n : ℕ, n ∉ Set.range (Encodable.encode : ℚ → ℕ) → m n = 0 := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n ∈ Set.range (Encodable.encode : ℚ → ℕ)
    · exact Eventually.of_forall (fun _ ↦ fun h ↦ (h hn).elim)
    · exact (ae_markLaw_zero_at_zero_rate H lambda f n
        (naturalRates_eq_zero_outside_range hn)).mono (fun _ h _ ↦ h)
  filter_upwards [hq,hn] with m hq hn using ⟨hq,hn⟩

def inactiveCountsZero (H lambda : ℝ) (f : Path) (m : ℕ → ℕ) : Prop :=
  (∀ q : ℚ, ¬Representative H (driftedReflectionPath lambda f) q → rationalCount m q = 0) ∧
  (∀ n : ℕ, n ∉ Set.range (Encodable.encode : ℚ → ℕ) → m n = 0)

theorem measurable_inactiveCountsZero (H lambda : ℝ) :
    Measurable (fun p : Path × (ℕ → ℕ) ↦ inactiveCountsZero H lambda p.1 p.2) := by
  apply Measurable.and
  · apply Measurable.forall
    intro q
    have hr : Measurable (fun p : Path × (ℕ → ℕ) ↦
        Representative H (driftedReflectionPath lambda p.1) q) :=
      measurableSet_setOfPred.mp ((measurableSet_representative H q).preimage
        ((measurable_driftedReflectionPath lambda).comp measurable_fst))
    exact hr.not.imp (((measurable_pi_apply (Encodable.encode q)).comp measurable_snd).eq
      measurable_const)
  · apply Measurable.forall
    intro n
    exact (measurable_const : Measurable (fun _ : Path × (ℕ → ℕ) ↦
      n ∉ Set.range (Encodable.encode : ℚ → ℕ))).imp
        (((measurable_pi_apply n).comp measurable_snd).eq measurable_const)

def pathJointLaw (H lambda : ℝ) : Measure (Path × (ℕ → ℕ)) :=
  CountablePoissonKernel.jointLaw pathLaw (naturalRates H lambda) (measurable_naturalRates H lambda)

instance (H lambda : ℝ) : IsProbabilityMeasure (pathJointLaw H lambda) :=
  inferInstanceAs (IsProbabilityMeasure (CountablePoissonKernel.jointLaw pathLaw
    (naturalRates H lambda) (measurable_naturalRates H lambda)))

theorem pathJointLaw_source (H lambda : ℝ) : (pathJointLaw H lambda).map Prod.fst = pathLaw :=
  CountablePoissonKernel.jointLaw_source pathLaw _ _

theorem ae_pathJointLaw_inactive_counts_zero (H lambda : ℝ) :
    ∀ᵐ p ∂pathJointLaw H lambda, inactiveCountsZero H lambda p.1 p.2 := by
  apply Measure.ae_compProd_of_ae_ae (measurable_inactiveCountsZero H lambda).setOf
  exact Eventually.of_forall (fun f ↦ ae_markLaw_inactive_counts_zero H lambda f)

theorem pathJointLaw_finite_rational_count_event (H lambda : ℝ)
    (s : Set Path) (hs : MeasurableSet s) (I : Finset ℚ) (k : ℚ → ℕ) :
    pathJointLaw H lambda (s ×ˢ (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q})) =
      ∫⁻ f in s, ∏ q ∈ I, ENNReal.ofReal (Real.exp (-(retainedArea H lambda q f : ℝ)) *
        (retainedArea H lambda q f : ℝ) ^ k q / ((k q).factorial : ℝ)) ∂pathLaw := by
  have hc : MeasurableSet (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) :=
    MeasurableSet.iInter (fun q ↦ MeasurableSet.iInter (fun _ ↦
      measurableSet_eq_fun (measurable_pi_apply (Encodable.encode q)) measurable_const))
  rw [pathJointLaw,CountablePoissonKernel.jointLaw,Measure.compProd_apply_prod hs hc]
  simp only [CountablePoissonKernel.rateKernel,Kernel.coe_mk]
  apply lintegral_congr
  intro f
  exact markLaw_finite_rational_count_event H lambda f I k

theorem pathJointLaw_hasLaw_finite (H lambda : ℝ) (I : Finset ℝ≥0) :
    HasLaw (fun p : Path × (ℕ → ℕ) ↦ I.restrict (fun t ↦ p.1 t))
      (ProbabilityTheory.BrownianReal.projectiveFamily I) (pathJointLaw H lambda) :=
  (pathLaw_hasLaw_finite I).fun_comp
    (show HasLaw (Prod.fst : Path × (ℕ → ℕ) → Path) pathLaw (pathJointLaw H lambda) from
      ⟨measurable_fst.aemeasurable,pathJointLaw_source H lambda⟩)

/-- The constructed marking law retains the actual Brownian driver,
including its exact real finite laws and its genuinely continuous paths. -/
theorem isBrownian_pathJointLaw (H lambda : ℝ) :
    IsBrownianReal (fun t (p : Path × (ℕ → ℕ)) ↦ p.1 t) (pathJointLaw H lambda) :=
  ⟨⟨pathJointLaw_hasLaw_finite H lambda⟩,Eventually.of_forall (fun p ↦ continuous_path p.1)⟩

def actualRates (H lambda : ℝ) (x : ℕ → ℝ) : ℕ → ℝ≥0 := naturalRates H lambda (measurablePath x)

theorem measurable_actualRates (H lambda : ℝ) : Measurable (actualRates H lambda) :=
  (measurable_naturalRates H lambda).comp measurable_measurablePath

def actualJointLaw (H lambda : ℝ) : Measure ((ℕ → ℝ) × (ℕ → ℕ)) :=
  CountablePoissonKernel.jointLaw rationalLaw (actualRates H lambda) (measurable_actualRates H lambda)

instance (H lambda : ℝ) : IsProbabilityMeasure (actualJointLaw H lambda) :=
  inferInstanceAs (IsProbabilityMeasure (CountablePoissonKernel.jointLaw rationalLaw
    (actualRates H lambda) (measurable_actualRates H lambda)))

theorem actualJointLaw_source (H lambda : ℝ) : (actualJointLaw H lambda).map Prod.fst = rationalLaw :=
  CountablePoissonKernel.jointLaw_source rationalLaw _ _

set_option backward.isDefEq.respectTransparency true in
theorem ae_actualJointLaw_inactive_counts_zero (H lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw H lambda,
      inactiveCountsZero H lambda (measurablePath p.1) p.2 := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
      inactiveCountsZero H lambda (measurablePath p.1) p.2) :=
    (measurable_inactiveCountsZero H lambda).comp
      (f := fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2))
      ((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd)
  apply Measure.ae_compProd_of_ae_ae hm.setOf
  exact Eventually.of_forall (fun x ↦ ae_markLaw_inactive_counts_zero H lambda (measurablePath x))

theorem actualJointLaw_finite_count_event (H lambda : ℝ)
    (s : Set (ℕ → ℝ)) (hs : MeasurableSet s) (I : Finset ℕ) (k : I → ℕ) :
    actualJointLaw H lambda (s ×ˢ cylinder (α := fun _ : ℕ ↦ ℕ) I {k}) =
      ∫⁻ x in s, ∏ i : I, ENNReal.ofReal (Real.exp (-(actualRates H lambda x i : ℝ)) *
        (actualRates H lambda x i : ℝ) ^ k i / ((k i).factorial : ℝ)) ∂rationalLaw :=
  CountablePoissonKernel.jointLaw_source_finite_count_event rationalLaw _ _ s hs I k

theorem actualRates_encode (H lambda : ℝ) (x : ℕ → ℝ) (q : ℚ) :
    actualRates H lambda x (Encodable.encode q) = retainedArea H lambda q (measurablePath x) :=
  naturalRates_encode H lambda (measurablePath x) q

theorem actualJointLaw_finite_rational_count_event (H lambda : ℝ)
    (s : Set (ℕ → ℝ)) (hs : MeasurableSet s) (I : Finset ℚ) (k : ℚ → ℕ) :
    actualJointLaw H lambda (s ×ˢ (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q})) =
      ∫⁻ x in s, ∏ q ∈ I, ENNReal.ofReal
        (Real.exp (-(retainedArea H lambda q (measurablePath x) : ℝ)) *
        (retainedArea H lambda q (measurablePath x) : ℝ) ^ k q / ((k q).factorial : ℝ)) ∂rationalLaw := by
  have hc : MeasurableSet (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) :=
    MeasurableSet.iInter (fun q ↦ MeasurableSet.iInter (fun _ ↦
      measurableSet_eq_fun (measurable_pi_apply (Encodable.encode q)) measurable_const))
  rw [actualJointLaw,CountablePoissonKernel.jointLaw,Measure.compProd_apply_prod hs hc]
  simp only [CountablePoissonKernel.rateKernel,Kernel.coe_mk,actualRates]
  apply lintegral_congr
  intro x
  exact markLaw_finite_rational_count_event H lambda (measurablePath x) I k

end PerronWright.BrownianClippedExcursionPoissonMarks
