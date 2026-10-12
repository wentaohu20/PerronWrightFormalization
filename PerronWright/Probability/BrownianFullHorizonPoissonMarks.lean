import PerronWright.Probability.BrownianFullHorizonExcursionAreas
import PerronWright.Probability.CountablePoissonKernel

/-!
# Actual full-horizon excursion-area Poisson marking law

The rates are the literal areas of the full, untruncated excursions,
indexed by the proved nonrepeating rational section. A genuine countable
Poisson kernel constructs the conditional marking law and the joint laws
with the actual Brownian source. Inactive anchors and unused codes have
zero counts. Independence is conditional on the path, not unconditional.
Spatial Poisson realization and the Wright density identity are separate
proof obligations.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonPoissonMarks

open BrownianPathLaw FullHorizonExcursionSection BrownianFullHorizonExcursionAreas
open BrownianPathReflectionLaw BrownianGaussianSkeleton

def naturalRates (lambda : ℝ) (f : Path) (n : ℕ) : ℝ≥0 :=
  match Encodable.decode₂ ℚ n with
  | none => 0
  | some q => retainedArea q lambda f

theorem measurable_naturalRates (lambda : ℝ) : Measurable (naturalRates lambda) := by
  apply measurable_pi_lambda
  intro n
  cases hn : Encodable.decode₂ ℚ n with
  | none => simpa only [naturalRates,hn] using (measurable_const : Measurable (fun _ : Path ↦ (0 : ℝ≥0)))
  | some q =>
      simpa only [naturalRates,hn,Function.comp_def,areaData] using
        (measurable_pi_apply q).comp (measurable_areaData lambda)

theorem measurable_naturalRates_all_parameters : Measurable
    (fun p : ℝ × Path ↦ naturalRates p.1 p.2) := by
  apply measurable_pi_lambda
  intro n
  cases hn : Encodable.decode₂ ℚ n with
  | none => simpa only [naturalRates,hn] using
      (measurable_const : Measurable (fun _ : ℝ × Path ↦ (0 : ℝ≥0)))
  | some q =>
      simpa only [naturalRates,hn] using measurable_retainedArea_all_parameters q

@[simp] theorem naturalRates_encode (lambda : ℝ) (f : Path) (q : ℚ) :
    naturalRates lambda f (Encodable.encode q) = retainedArea q lambda f := by
  simp only [naturalRates,Encodable.decode₂_encode]

theorem naturalRates_eq_zero_outside_range {lambda : ℝ} {f : Path} {n : ℕ}
    (hn : n ∉ Set.range (Encodable.encode : ℚ → ℕ)) : naturalRates lambda f n = 0 := by
  have hd : Encodable.decode₂ ℚ n = none := by
    apply not_ne_iff.mp
    intro hne
    exact hn (Encodable.decode₂_ne_none_iff.mp hne)
  simp only [naturalRates,hd]

theorem naturalRates_eq_area_of_representative {lambda : ℝ} {f : Path} {q : ℚ}
    (hq : Representative (driftedReflectionPath lambda f) q) :
    naturalRates lambda f (Encodable.encode q) = excursionArea (q : ℝ) lambda f := by
  rw [naturalRates_encode]
  exact if_pos hq

theorem naturalRates_eq_zero_of_not_representative {lambda : ℝ} {f : Path} {q : ℚ}
    (hq : ¬Representative (driftedReflectionPath lambda f) q) :
    naturalRates lambda f (Encodable.encode q) = 0 := by
  rw [naturalRates_encode]
  exact if_neg hq

def rationalCount (m : ℕ → ℕ) (q : ℚ) : ℕ := m (Encodable.encode q)

def markLaw (lambda : ℝ) (f : Path) : Measure (ℕ → ℕ) :=
  CountablePoissonKernel.countLaw (naturalRates lambda f)

instance (lambda : ℝ) (f : Path) : IsProbabilityMeasure (markLaw lambda f) :=
  inferInstanceAs (IsProbabilityMeasure (CountablePoissonKernel.countLaw (naturalRates lambda f)))

theorem measurable_markLaw (lambda : ℝ) : Measurable (markLaw lambda) :=
  CountablePoissonKernel.measurable_countLaw.comp (measurable_naturalRates lambda)

/-- True conditional Poisson laws at the actual rational component areas. -/
theorem markLaw_hasLaw_rationalCount (lambda : ℝ) (f : Path) (q : ℚ) :
    HasLaw (fun m ↦ rationalCount m q) (poissonMeasure (retainedArea q lambda f)) (markLaw lambda f) := by
  simpa only [markLaw,rationalCount,naturalRates_encode] using
    CountablePoissonKernel.countLaw_hasLaw_eval (naturalRates lambda f) (Encodable.encode q)

theorem markLaw_rationalCounts_independent (lambda : ℝ) (f : Path) :
    iIndepFun (fun q (m : ℕ → ℕ) ↦ rationalCount m q) (markLaw lambda f) :=
  iIndepFun.precomp Encodable.encode_injective (CountablePoissonKernel.countLaw_independent (naturalRates lambda f))

theorem markLaw_finite_rational_count_event (lambda : ℝ) (f : Path)
    (I : Finset ℚ) (k : ℚ → ℕ) :
    markLaw lambda f (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) =
      ∏ q ∈ I, ENNReal.ofReal (Real.exp (-(retainedArea q lambda f : ℝ)) *
        (retainedArea q lambda f : ℝ) ^ k q / ((k q).factorial : ℝ)) := by
  have hi := (markLaw_rationalCounts_independent lambda f).measure_inter_preimage_eq_mul
    I (sets := fun q ↦ {k q}) (fun q _ ↦ measurableSet_singleton (k q))
  have hs : (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) =
      (⋂ q ∈ I, (fun m : ℕ → ℕ ↦ rationalCount m q) ⁻¹' {k q}) := by
    ext m
    simp only [mem_iInter,mem_ofPred_eq,mem_preimage,mem_singleton_iff]
  rw [hs,hi]
  apply Finset.prod_congr rfl
  intro q _
  calc
    _ = poissonMeasure (retainedArea q lambda f) {k q} := by
      convert (markLaw_hasLaw_rationalCount lambda f q).measure_eq
        (measurableSet_singleton (k q)) using 1
      · congr 1
      · congr 1
    _ = _ := poissonMeasure_singleton _ _

theorem ae_markLaw_zero_at_zero_rate (lambda : ℝ) (f : Path) (n : ℕ)
    (hn : naturalRates lambda f n = 0) :
    ∀ᵐ m ∂markLaw lambda f, m n = 0 := by
  rw [ae_iff_prob_eq_one ((measurable_pi_apply n).eq measurable_const)]
  have hm := (CountablePoissonKernel.countLaw_hasLaw_eval
    (naturalRates lambda f) n).measure_eq
      (show MeasurableSet {a : ℕ | a = 0} from measurableSet_singleton 0)
  change CountablePoissonKernel.countLaw (naturalRates lambda f) {m | m n = 0} = 1
  rw [hm,hn]
  simp [ofPred_eq_eq_singleton,poissonMeasure_singleton]

/-- Zero rates really suppress duplicate representatives and unused codes. -/
theorem ae_markLaw_inactive_counts_zero (lambda : ℝ) (f : Path) :
    ∀ᵐ m ∂markLaw lambda f,
      (∀ q : ℚ, ¬Representative (driftedReflectionPath lambda f) q → rationalCount m q = 0) ∧
      (∀ n : ℕ, n ∉ Set.range (Encodable.encode : ℚ → ℕ) → m n = 0) := by
  have hq : ∀ᵐ m ∂markLaw lambda f,
      ∀ q : ℚ, ¬Representative (driftedReflectionPath lambda f) q → rationalCount m q = 0 := by
    rw [ae_all_iff]
    intro q
    by_cases hq : Representative (driftedReflectionPath lambda f) q
    · exact Eventually.of_forall (fun _ ↦ fun h ↦ (h hq).elim)
    · exact (ae_markLaw_zero_at_zero_rate lambda f (Encodable.encode q)
        (naturalRates_eq_zero_of_not_representative hq)).mono (fun _ h _ ↦ h)
  have hn : ∀ᵐ m ∂markLaw lambda f,
      ∀ n : ℕ, n ∉ Set.range (Encodable.encode : ℚ → ℕ) → m n = 0 := by
    rw [ae_all_iff]
    intro n
    by_cases hn : n ∈ Set.range (Encodable.encode : ℚ → ℕ)
    · exact Eventually.of_forall (fun _ ↦ fun h ↦ (h hn).elim)
    · exact (ae_markLaw_zero_at_zero_rate lambda f n
        (naturalRates_eq_zero_outside_range hn)).mono (fun _ h _ ↦ h)
  filter_upwards [hq,hn] with m hq hn using ⟨hq,hn⟩

def inactiveCountsZero (lambda : ℝ) (f : Path) (m : ℕ → ℕ) : Prop :=
  (∀ q : ℚ, ¬Representative (driftedReflectionPath lambda f) q → rationalCount m q = 0) ∧
  (∀ n : ℕ, n ∉ Set.range (Encodable.encode : ℚ → ℕ) → m n = 0)

theorem measurable_inactiveCountsZero (lambda : ℝ) :
    Measurable (fun p : Path × (ℕ → ℕ) ↦ inactiveCountsZero lambda p.1 p.2) := by
  apply Measurable.and
  · apply Measurable.forall
    intro q
    have hr : Measurable (fun p : Path × (ℕ → ℕ) ↦
        Representative (driftedReflectionPath lambda p.1) q) :=
      measurableSet_setOfPred.mp ((measurableSet_representative q).preimage
        ((measurable_driftedReflectionPath lambda).comp measurable_fst))
    exact hr.not.imp (((measurable_pi_apply (Encodable.encode q)).comp measurable_snd).eq
      measurable_const)
  · apply Measurable.forall
    intro n
    exact (measurable_const : Measurable (fun _ : Path × (ℕ → ℕ) ↦
      n ∉ Set.range (Encodable.encode : ℚ → ℕ))).imp
        (((measurable_pi_apply n).comp measurable_snd).eq measurable_const)

def pathJointLaw (lambda : ℝ) : Measure (Path × (ℕ → ℕ)) :=
  CountablePoissonKernel.jointLaw pathLaw (naturalRates lambda) (measurable_naturalRates lambda)

instance (lambda : ℝ) : IsProbabilityMeasure (pathJointLaw lambda) :=
  inferInstanceAs (IsProbabilityMeasure (CountablePoissonKernel.jointLaw pathLaw
    (naturalRates lambda) (measurable_naturalRates lambda)))

theorem pathJointLaw_source (lambda : ℝ) : (pathJointLaw lambda).map Prod.fst = pathLaw :=
  CountablePoissonKernel.jointLaw_source pathLaw _ _

theorem ae_pathJointLaw_inactive_counts_zero (lambda : ℝ) :
    ∀ᵐ p ∂pathJointLaw lambda, inactiveCountsZero lambda p.1 p.2 := by
  apply Measure.ae_compProd_of_ae_ae (measurable_inactiveCountsZero lambda).setOf
  exact Eventually.of_forall (fun f ↦ ae_markLaw_inactive_counts_zero lambda f)

theorem pathJointLaw_finite_rational_count_event (lambda : ℝ)
    (s : Set Path) (hs : MeasurableSet s) (I : Finset ℚ) (k : ℚ → ℕ) :
    pathJointLaw lambda (s ×ˢ (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q})) =
      ∫⁻ f in s, ∏ q ∈ I, ENNReal.ofReal (Real.exp (-(retainedArea q lambda f : ℝ)) *
        (retainedArea q lambda f : ℝ) ^ k q / ((k q).factorial : ℝ)) ∂pathLaw := by
  have hc : MeasurableSet (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) :=
    MeasurableSet.iInter (fun q ↦ MeasurableSet.iInter (fun _ ↦
      measurableSet_eq_fun (measurable_pi_apply (Encodable.encode q)) measurable_const))
  rw [pathJointLaw,CountablePoissonKernel.jointLaw,Measure.compProd_apply_prod hs hc]
  simp only [CountablePoissonKernel.rateKernel,Kernel.coe_mk]
  apply lintegral_congr
  intro f
  exact markLaw_finite_rational_count_event lambda f I k

theorem pathJointLaw_hasLaw_finite (lambda : ℝ) (I : Finset ℝ≥0) :
    HasLaw (fun p : Path × (ℕ → ℕ) ↦ I.restrict (fun t ↦ p.1 t))
      (ProbabilityTheory.BrownianReal.projectiveFamily I) (pathJointLaw lambda) :=
  (pathLaw_hasLaw_finite I).fun_comp
    (show HasLaw (Prod.fst : Path × (ℕ → ℕ) → Path) pathLaw (pathJointLaw lambda) from
      ⟨measurable_fst.aemeasurable,pathJointLaw_source lambda⟩)

/-- The constructed marking law retains the actual Brownian driver,
including its exact real finite laws and its genuinely continuous paths. -/
theorem isBrownian_pathJointLaw (lambda : ℝ) :
    IsBrownianReal (fun t (p : Path × (ℕ → ℕ)) ↦ p.1 t) (pathJointLaw lambda) :=
  ⟨⟨pathJointLaw_hasLaw_finite lambda⟩,Eventually.of_forall (fun p ↦ continuous_path p.1)⟩

def actualRates (lambda : ℝ) (x : ℕ → ℝ) : ℕ → ℝ≥0 := naturalRates lambda (measurablePath x)

theorem measurable_actualRates (lambda : ℝ) : Measurable (actualRates lambda) :=
  (measurable_naturalRates lambda).comp measurable_measurablePath

def actualJointLaw (lambda : ℝ) : Measure ((ℕ → ℝ) × (ℕ → ℕ)) :=
  CountablePoissonKernel.jointLaw rationalLaw (actualRates lambda) (measurable_actualRates lambda)

instance (lambda : ℝ) : IsProbabilityMeasure (actualJointLaw lambda) :=
  inferInstanceAs (IsProbabilityMeasure (CountablePoissonKernel.jointLaw rationalLaw
    (actualRates lambda) (measurable_actualRates lambda)))

theorem actualJointLaw_source (lambda : ℝ) : (actualJointLaw lambda).map Prod.fst = rationalLaw :=
  CountablePoissonKernel.jointLaw_source rationalLaw _ _

set_option backward.isDefEq.respectTransparency true in
theorem ae_actualJointLaw_inactive_counts_zero (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda,
      inactiveCountsZero lambda (measurablePath p.1) p.2 := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
      inactiveCountsZero lambda (measurablePath p.1) p.2) :=
    (measurable_inactiveCountsZero lambda).comp
      (f := fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2))
      ((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd)
  apply Measure.ae_compProd_of_ae_ae hm.setOf
  exact Eventually.of_forall (fun x ↦ ae_markLaw_inactive_counts_zero lambda (measurablePath x))

theorem actualJointLaw_finite_count_event (lambda : ℝ)
    (s : Set (ℕ → ℝ)) (hs : MeasurableSet s) (I : Finset ℕ) (k : I → ℕ) :
    actualJointLaw lambda (s ×ˢ cylinder (α := fun _ : ℕ ↦ ℕ) I {k}) =
      ∫⁻ x in s, ∏ i : I, ENNReal.ofReal (Real.exp (-(actualRates lambda x i : ℝ)) *
        (actualRates lambda x i : ℝ) ^ k i / ((k i).factorial : ℝ)) ∂rationalLaw :=
  CountablePoissonKernel.jointLaw_source_finite_count_event rationalLaw _ _ s hs I k

theorem actualRates_encode (lambda : ℝ) (x : ℕ → ℝ) (q : ℚ) :
    actualRates lambda x (Encodable.encode q) = retainedArea q lambda (measurablePath x) :=
  naturalRates_encode lambda (measurablePath x) q

theorem actualJointLaw_finite_rational_count_event (lambda : ℝ)
    (s : Set (ℕ → ℝ)) (hs : MeasurableSet s) (I : Finset ℚ) (k : ℚ → ℕ) :
    actualJointLaw lambda (s ×ˢ (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q})) =
      ∫⁻ x in s, ∏ q ∈ I, ENNReal.ofReal
        (Real.exp (-(retainedArea q lambda (measurablePath x) : ℝ)) *
        (retainedArea q lambda (measurablePath x) : ℝ) ^ k q / ((k q).factorial : ℝ)) ∂rationalLaw := by
  have hc : MeasurableSet (⋂ q ∈ I, {m : ℕ → ℕ | rationalCount m q = k q}) :=
    MeasurableSet.iInter (fun q ↦ MeasurableSet.iInter (fun _ ↦
      measurableSet_eq_fun (measurable_pi_apply (Encodable.encode q)) measurable_const))
  rw [actualJointLaw,CountablePoissonKernel.jointLaw,Measure.compProd_apply_prod hs hc]
  simp only [CountablePoissonKernel.rateKernel,Kernel.coe_mk,actualRates]
  apply lintegral_congr
  intro x
  exact markLaw_finite_rational_count_event lambda (measurablePath x) I k

end PerronWright.BrownianFullHorizonPoissonMarks
