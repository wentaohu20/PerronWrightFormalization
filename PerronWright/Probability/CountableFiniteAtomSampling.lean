import PerronWright.Probability.FinitePointMeasureFintype

/-!
# Measurable genuine finite atomic measures from countable selections

A countable measurable index selection is reduced to its actual finite
set whenever finite, with the explicit empty branch otherwise. Fixed
finite atom maps and countable measurable partitioning prove weak-Borel
measurability; no random-enumeration interface is assumed.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableFiniteAtomSampling

open FinitePointMeasureCompact FinitePointMeasureFintype

variable {S I E : Type*} [MeasurableSpace S] [Countable I]

def selectedFinset (A : S → Set I) (s : S) : Finset I :=
  if h : (A s).Finite then h.toFinset else ∅

omit [MeasurableSpace S] [Countable I] in
theorem mem_selectedFinset (A : S → Set I) (s : S) (i : I) :
    i ∈ selectedFinset A s ↔ (A s).Finite ∧ i ∈ A s := by
  by_cases h : (A s).Finite <;> simp [selectedFinset,h]

theorem measurable_selectedFinset (A : S → Set I) (hA : Measurable A) :
    Measurable (selectedFinset A) := by
  apply measurable_finset_iff.mpr
  intro i
  have hf : Measurable (fun s : S ↦ (A s).Finite) :=
    measurableSet_setOfPred.mp (MeasurableSet.setOfPred_finite.preimage hA)
  simpa only [mem_selectedFinset, Function.comp_def] using hf.and ((measurable_set_mem i).comp hA)

variable [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E]

def ofFinset (t : Finset I) (x : I → E) : PointMeasure E :=
  ofFintype (fun i : t ↦ x i.1)

omit [Countable I] in
theorem measurable_ofFinset (t : Finset I) : Measurable (ofFinset (E := E) t) := by
  have he : (ofFinset (E := E) t : (I → E) → PointMeasure E) =
      (fun x ↦ ofAtomsPoint ((fun i : t ↦ x i.1) ∘ (Fintype.equivFin t).symm)) := by
    funext x
    exact ofFintype_eq_ofAtomsPoint _
  rw [he]
  exact (measurable_ofAtomsPoint (Fintype.card t)).comp
    (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _))

def pointMeasure (A : S → Set I) (X : S → I → E) (s : S) : PointMeasure E :=
  ofFinset (selectedFinset A s) (X s)

theorem measurable_pointMeasure (A : S → Set I) (hA : Measurable A)
    (X : S → I → E) (hX : Measurable X) : Measurable (pointMeasure A X) := by
  have hm : Measurable (fun p : S × Finset I ↦ ofFinset p.2 (X p.1)) :=
    measurable_from_prod_countable_left (fun t ↦ (measurable_ofFinset t).comp hX)
  exact hm.comp (measurable_id.prodMk (measurable_selectedFinset A hA))

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem pointMeasure_eq_ofFinset (A : S → Set I) (X : S → I → E)
    (s : S) (t : Finset I) (ht : A s = (t : Set I)) :
    pointMeasure A X s = ofFinset t (X s) := by
  have hf : (A s).Finite := ht ▸ t.finite_toSet
  have he : hf.toFinset = t := by ext i; simp only [Set.Finite.mem_toFinset,ht,Finset.mem_coe]
  simp only [pointMeasure,selectedFinset,dif_pos hf,he]

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem size_pointMeasure (A : S → Set I) (X : S → I → E)
    (s : S) (hf : (A s).Finite) : size (pointMeasure A X s) = hf.toFinset.card := by
  simp only [pointMeasure,selectedFinset,dif_pos hf,ofFinset,size_ofFintype,Fintype.card_coe]

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem ofFinset_toMeasure (t : Finset I) (x : I → E) :
    ((ofFinset t x : FiniteMeasure E) : Measure E) =
      ∑ i ∈ t, Measure.dirac (x i) := by
  exact Finset.sum_coe_sort t (fun i ↦ Measure.dirac (x i))

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem pointMeasure_integral [MeasurableSingletonClass E]
    (A : S → Set I) (X : S → I → E) (s : S)
    (hf : (A s).Finite) (f : E → ℝ) :
    (∫ z, f z ∂((pointMeasure A X s : FiniteMeasure E) : Measure E)) =
      ∑ i ∈ hf.toFinset, f (X s i) := by
  have ht : A s = (hf.toFinset : Set I) := by ext i; simp
  rw [pointMeasure_eq_ofFinset A X s hf.toFinset ht]
  unfold ofFinset
  rw [ofFintype_integral]
  exact Finset.sum_coe_sort hf.toFinset (fun i ↦ f (X s i))

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem sum_dirac_eq_ofFinset (A : Set I) (hA : A.Finite) (x : I → E) :
    Measure.sum (fun i ↦ if i ∈ A then Measure.dirac (x i) else 0) =
      ((ofFinset hA.toFinset x : FiniteMeasure E) : Measure E) := by
  ext B hB
  rw [Measure.sum_apply _ hB, ofFinset_toMeasure, Measure.finsetSum_apply]
  rw [tsum_eq_sum (s := hA.toFinset) (fun i hi ↦ by
    have hn : i ∉ A := by simpa only [Set.Finite.mem_toFinset] using hi
    simp [hn])]
  apply Finset.sum_congr rfl
  intro i hi
  have hm : i ∈ A := by simpa using hi
  rw [if_pos hm]

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem restrict_sum_dirac [MeasurableSingletonClass E]
    (A : Set I) (x : I → E) (K : Set E)
    (hK : MeasurableSet K) :
    (Measure.sum (fun i ↦ if i ∈ A then Measure.dirac (x i) else 0)).restrict K =
      Measure.sum (fun i ↦ if i ∈ {i | i ∈ A ∧ x i ∈ K} then
        Measure.dirac (x i) else 0) := by
  rw [Measure.restrict_sum _ hK]
  congr 1
  funext i
  by_cases ha : i ∈ A <;> by_cases hk : x i ∈ K <;>
    simp [ha, hk, restrict_dirac]

omit [MeasurableSpace S] [Countable I] [TopologicalSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
theorem restrict_sum_dirac_eq_ofFinset [MeasurableSingletonClass E]
    (A : Set I) (x : I → E) (K : Set E)
    (hK : MeasurableSet K) (hf : {i | i ∈ A ∧ x i ∈ K}.Finite) :
    (Measure.sum (fun i ↦ if i ∈ A then Measure.dirac (x i) else 0)).restrict K =
      ((ofFinset hf.toFinset x : FiniteMeasure E) : Measure E) := by
  rw [restrict_sum_dirac A x K hK]
  convert sum_dirac_eq_ofFinset _ hf x using 1
  congr 1
  funext i
  split_ifs <;> rfl

end PerronWright.CountableFiniteAtomSampling
