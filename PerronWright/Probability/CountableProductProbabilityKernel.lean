import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Genuine countable products of measurable probability kernels

The infinite product is constructed from the actual kernel measures.
Its measurability is proved on finite generating cylinders. No product
measurability or conditional-independence interface is assumed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CountableProductProbabilityKernel

variable {S E F : Type*} [MeasurableSpace S] [MeasurableSpace E] [MeasurableSpace F]

def law (κ : ℕ → Kernel S E) (s : S) : Measure (ℕ → E) :=
  Measure.infinitePi (fun i ↦ κ i s)

instance (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] (s : S) :
    IsProbabilityMeasure (law κ s) := by
  unfold law
  infer_instance

theorem measurable_finiteProduct (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (I : Finset ℕ) : Measurable (fun s ↦ Measure.pi (fun i : I ↦ κ i.val s)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi
  rintro _ ⟨A,hA,rfl⟩
  have hAm : ∀ i : I, MeasurableSet (A i) := fun i ↦ hA i (mem_univ i)
  simp only [Measure.pi_pi]
  exact Finset.measurable_prod Finset.univ (fun i _ ↦
    (Measure.measurable_coe (hAm i)).comp (κ i.val).measurable)

theorem law_map_restrict (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (s : S) (I : Finset ℕ) :
    (law κ s).map I.restrict = Measure.pi (fun i : I ↦ κ i.val s) :=
  Measure.infinitePi_map_restrict _

theorem law_cylinder (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (s : S) (I : Finset ℕ) (A : Set (I → E)) (hA : MeasurableSet A) :
    law κ s (cylinder I A) = Measure.pi (fun i : I ↦ κ i.val s) A :=
  Measure.infinitePi_cylinder _ hA

theorem measurable_law (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (law κ) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  intro A hA
  obtain ⟨I,B,hB,rfl⟩ := (mem_measurableCylinders A).mp hA
  simp only [law_cylinder κ _ I B hB]
  exact (Measure.measurable_coe hB).comp (measurable_finiteProduct κ I)

def productKernel (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] : Kernel S (ℕ → E) :=
  ⟨law κ,measurable_law κ⟩

instance (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (productKernel κ) :=
  ⟨fun s ↦ inferInstanceAs (IsProbabilityMeasure (law κ s))⟩

theorem law_hasLaw_eval (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (s : S) (i : ℕ) : HasLaw (fun x : ℕ → E ↦ x i) (κ i s) (law κ s) :=
  (measurePreserving_eval_infinitePi (fun j ↦ κ j s) i).hasLaw

theorem law_independent (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] (s : S) :
    iIndepFun (fun i (x : ℕ → E) ↦ x i) (law κ s) :=
  iIndepFun_infinitePi (X := fun _ (x : E) ↦ x) (fun _ ↦ measurable_id)

theorem law_map_coordinatewise (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (s : S) (f : ℕ → E → F) (hf : ∀ i, Measurable (f i)) :
    (law κ s).map (fun x i ↦ f i (x i)) =
      Measure.infinitePi (fun i ↦ (κ i s).map (f i)) :=
  Measure.infinitePi_map_pi _ hf

theorem ae_all_coordinates (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (s : S) (p : ℕ → E → Prop) (hp : ∀ i, ∀ᵐ x ∂κ i s, p i x) :
    ∀ᵐ x ∂law κ s, ∀ i, p i (x i) := by
  apply ae_all_iff.mpr
  intro i
  have hm := (law_hasLaw_eval κ s i).map_eq
  apply ae_of_ae_map (measurable_pi_apply i).aemeasurable
  rw [hm]
  exact hp i

def jointLaw (μ : Measure S) (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] :
    Measure (S × (ℕ → E)) := μ ⊗ₘ productKernel κ

instance (μ : Measure S) [IsProbabilityMeasure μ]
    (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] :
    IsProbabilityMeasure (jointLaw μ κ) := by
  unfold jointLaw
  infer_instance

theorem jointLaw_source (μ : Measure S) [IsProbabilityMeasure μ]
    (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)] :
    (jointLaw μ κ).map Prod.fst = μ := Measure.fst_compProd _ _

theorem jointLaw_source_cylinder (μ : Measure S) [IsProbabilityMeasure μ]
    (κ : ℕ → Kernel S E) [∀ i, IsMarkovKernel (κ i)]
    (A : Set S) (hA : MeasurableSet A) (I : Finset ℕ)
    (B : Set (I → E)) (hB : MeasurableSet B) :
    jointLaw μ κ (A ×ˢ cylinder I B) =
      ∫⁻ s in A, Measure.pi (fun i : I ↦ κ i.val s) B ∂μ := by
  have hc : MeasurableSet (cylinder (α := fun _ : ℕ ↦ E) I B) :=
    hB.preimage (measurable_pi_lambda _ (fun i : I ↦ measurable_pi_apply i.val))
  rw [jointLaw,Measure.compProd_apply_prod hA hc]
  simp only [productKernel,Kernel.coe_mk,law_cylinder κ _ I B hB]

end PerronWright.CountableProductProbabilityKernel
