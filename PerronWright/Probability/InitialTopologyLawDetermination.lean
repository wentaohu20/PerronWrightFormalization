import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Actual law determination in a test-induced topology

An open neighborhood of a compact set in a topology induced by real
tests contains a finite-coordinate cylinder neighborhood of that compact
set. Thus genuine inner-regular finite measures are determined by their
actual finite-dimensional test pushforwards. No countable-generation,
Polishness, or measure-determination interface is assumed.

For a genuinely hereditarily Lindelöf test-induced space, we additionally
prove that finite test cylinders generate its actual Borel sigma algebra
and determine every finite Borel measure, without requiring a candidate
measure to be inner regular.
-/

open MeasureTheory Topology
open scoped Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.InitialTopologyLawDetermination

variable {X I : Type*} [TopologicalSpace X]

def finiteProjection (e : X → I → ℝ) (F : Finset I) : X → (F → ℝ) :=
  fun x i ↦ e x i.val

theorem continuous_finiteProjection {e : X → I → ℝ} (he : Continuous e) (F : Finset I) :
    Continuous (finiteProjection e F) :=
  continuous_pi (fun i ↦ (continuous_apply i.val).comp he)

/-- A compact set inside an open set has one finite-coordinate open
cylinder neighborhood contained in the given open set. -/
theorem exists_finiteCylinder_of_compact_subset_open (e : X → I → ℝ)
    (he : IsInducing e) {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ F : Finset I, ∃ V : Set (F → ℝ), IsOpen V ∧
      K ⊆ finiteProjection e F ⁻¹' V ∧ finiteProjection e F ⁻¹' V ⊆ U := by
  obtain ⟨W, hW, hUW⟩ := he.isOpen_iff.mp hU
  have hb : ∀ x : K, ∃ (F : Finset I) (u : I → Set ℝ),
      (∀ i ∈ F, IsOpen (u i) ∧ e x.val i ∈ u i) ∧ (F : Set I).pi u ⊆ W := by
    intro x
    apply isOpen_pi_iff.mp hW
    change x.val ∈ e ⁻¹' W
    rw [hUW]
    exact hKU x.property
  choose F u hu using hb
  let O : K → Set X := fun x ↦ e ⁻¹' (F x : Set I).pi (u x)
  have hO : ∀ x, IsOpen (O x) := fun x ↦
    (isOpen_set_pi (F x).finite_toSet (fun i hi ↦ (hu x).1 i hi |>.1)).preimage he.continuous
  have hc : K ⊆ ⋃ x : K, O x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, fun i hi ↦ (hu ⟨x, hx⟩).1 i hi |>.2⟩
  obtain ⟨C, hC⟩ := hK.elim_finite_subcover O hO hc
  let J : Finset I := C.biUnion F
  have hF : ∀ x ∈ C, ∀ i ∈ F x, i ∈ J := by
    intro x hx i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, hi⟩
  let lift : (J → ℝ) → I → ℝ := fun v i ↦ if hi : i ∈ J then v ⟨i, hi⟩ else 0
  have hlift : Continuous lift := by
    apply continuous_pi
    intro i
    dsimp [lift]
    split_ifs with hi
    · exact continuous_apply (⟨i, hi⟩ : J)
    · exact continuous_const
  let B : Set (I → ℝ) := ⋃ x ∈ C, (F x : Set I).pi (u x)
  have hB : IsOpen B := isOpen_iUnion (fun x ↦ isOpen_iUnion (fun _ ↦
    isOpen_set_pi (F x).finite_toSet (fun i hi ↦ (hu x).1 i hi |>.1)))
  refine ⟨J, lift ⁻¹' B, hB.preimage hlift, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hC hx)
    refine Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
    intro i hi
    simpa only [lift, finiteProjection, dif_pos (hF j hj i hi)] using hxj i hi
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
    have hxe : e x ∈ (F j : Set I).pi (u j) := by
      intro i hi
      simpa only [lift, finiteProjection, dif_pos (hF j hj i hi)] using hxj i hi
    rw [← hUW]
    exact (hu j).2 hxe

/-- Genuine finite inner-regular Borel measures are determined by all
actual finite test-vector laws when those tests induce the topology. -/
theorem ext_of_finiteProjection_map [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (e : X → I → ℝ) (he : IsInducing e)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.InnerRegular] [ν.InnerRegular]
    (h : ∀ F : Finset I, μ.map (finiteProjection e F) = ν.map (finiteProjection e F)) :
    μ = ν := by
  have hle (ρ σ : Measure X) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
      [ρ.InnerRegular] [σ.InnerRegular]
      (hρσ : ∀ F : Finset I, ρ.map (finiteProjection e F) = σ.map (finiteProjection e F))
      {U : Set X} (hU : IsOpen U) : ρ U ≤ σ U := by
    rw [hU.measurableSet.measure_eq_iSup_isCompact ρ]
    refine iSup_le (fun K ↦ iSup_le (fun hKU ↦ iSup_le (fun hK ↦ ?_)))
    obtain ⟨F, V, hV, hKV, hVU⟩ := exists_finiteCylinder_of_compact_subset_open e he hK hU hKU
    have hp := (continuous_finiteProjection he.continuous F).measurable
    calc
      ρ K ≤ ρ (finiteProjection e F ⁻¹' V) := measure_mono hKV
      _ = (ρ.map (finiteProjection e F)) V := (Measure.map_apply hp hV.measurableSet).symm
      _ = (σ.map (finiteProjection e F)) V := by rw [hρσ F]
      _ = σ (finiteProjection e F ⁻¹' V) := Measure.map_apply hp hV.measurableSet
      _ ≤ σ U := measure_mono hVU
  let : μ.WeaklyRegular := Measure.InnerRegularWRT.weaklyRegular_of_finite μ
    Measure.InnerRegular.innerRegularWRT_isClosed_isOpen
  let : ν.WeaklyRegular := Measure.InnerRegularWRT.weaklyRegular_of_finite ν
    Measure.InnerRegular.innerRegularWRT_isClosed_isOpen
  exact Measure.OuterRegular.ext_isOpen (fun U hU ↦
    le_antisymm (hle μ ν h hU) (hle ν μ (fun F ↦ (h F).symm) hU))

/-- Literal finite-coordinate open cylinders, not a postulated
generating family. -/
def cylinders (e : X → I → ℝ) : Set (Set X) :=
  {A | ∃ F : Finset I, ∃ V : Set (F → ℝ), IsOpen V ∧ A = finiteProjection e F ⁻¹' V}

omit [TopologicalSpace X] in
theorem univ_mem_cylinders (e : X → I → ℝ) : Set.univ ∈ cylinders e :=
  ⟨∅, Set.univ, isOpen_univ, rfl⟩

omit [TopologicalSpace X] in
theorem isPiSystem_cylinders (e : X → I → ℝ) : IsPiSystem (cylinders e) := by
  rintro A ⟨F, V, hV, rfl⟩ B ⟨G, W, hW, rfl⟩ _
  let H := F ∪ G
  let p : (H → ℝ) → F → ℝ := fun v i ↦ v ⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩
  let q : (H → ℝ) → G → ℝ := fun v i ↦ v ⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩
  have hp : Continuous p := continuous_pi (fun _ ↦ continuous_apply _)
  have hq : Continuous q := continuous_pi (fun _ ↦ continuous_apply _)
  refine ⟨H, p ⁻¹' V ∩ q ⁻¹' W, (hV.preimage hp).inter (hW.preimage hq), ?_⟩
  rfl

/-- The actual Borel sigma algebra is generated by finite test
cylinders if every open set is genuinely Lindelöf. -/
theorem borel_eq_generateFrom_cylinders [MeasurableSpace X] [BorelSpace X]
    [HereditarilyLindelofSpace X] (e : X → I → ℝ) (he : IsInducing e) :
    ‹MeasurableSpace X› = MeasurableSpace.generateFrom (cylinders e) := by
  have hB : ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq
  rw [hB]
  apply le_antisymm
  · change MeasurableSpace.generateFrom {U : Set X | IsOpen U} ≤ _
    apply MeasurableSpace.generateFrom_le
    intro U hU
    have hx : ∀ x : U, ∃ F : Finset I, ∃ V : Set (F → ℝ), IsOpen V ∧
        x.val ∈ finiteProjection e F ⁻¹' V ∧ finiteProjection e F ⁻¹' V ⊆ U := by
      intro x
      obtain ⟨F, V, hV, hxV, hVU⟩ := exists_finiteCylinder_of_compact_subset_open e he
        isCompact_singleton hU (Set.singleton_subset_iff.mpr x.property)
      exact ⟨F, V, hV, hxV (Set.mem_singleton _), hVU⟩
    choose F V hV hxV hVU using hx
    let A : U → Set X := fun x ↦ finiteProjection e (F x) ⁻¹' V x
    have hA : ∀ x, IsOpen (A x) := fun x ↦
      (hV x).preimage (continuous_finiteProjection he.continuous (F x))
    have hUA : U ⊆ ⋃ x : U, A x := fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
    obtain ⟨C, hC, hCov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover A hA hUA
    have hEq : U = ⋃ x ∈ C, A x := Set.Subset.antisymm hCov
      (Set.iUnion₂_subset (fun x _ ↦ hVU x))
    rw [hEq]
    exact MeasurableSet.biUnion hC (fun x _ ↦
      MeasurableSpace.measurableSet_generateFrom ⟨F x, V x, hV x, rfl⟩)
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨F, V, hV, rfl⟩
    rw [← hB]
    exact (hV.preimage (continuous_finiteProjection he.continuous F)).measurableSet

/-- On a genuinely hereditarily Lindelöf test-induced space, actual
finite-vector pushforward equality determines all finite Borel laws,
without an inner-regularity assumption on a candidate target. -/
theorem ext_of_finiteProjection_map_of_hereditarilyLindelof
    [MeasurableSpace X] [BorelSpace X] [HereditarilyLindelofSpace X]
    (e : X → I → ℝ) (he : IsInducing e)
    (μ ν : Measure X) [IsFiniteMeasure μ]
    (h : ∀ F : Finset I, μ.map (finiteProjection e F) = ν.map (finiteProjection e F)) :
    μ = ν := by
  apply Measure.ext_of_generateFrom_of_iUnion (cylinders e) (fun _ ↦ Set.univ)
    (borel_eq_generateFrom_cylinders e he) (isPiSystem_cylinders e)
    (by exact Set.iUnion_const Set.univ) (fun _ ↦ univ_mem_cylinders e)
    (fun _ ↦ measure_ne_top μ _)
  rintro A ⟨F, V, hV, rfl⟩
  have hp := (continuous_finiteProjection he.continuous F).measurable
  rw [← Measure.map_apply hp hV.measurableSet, h F, Measure.map_apply hp hV.measurableSet]

end PerronWright.InitialTopologyLawDetermination
