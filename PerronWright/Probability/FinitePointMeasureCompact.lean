import PerronWright.Probability.FiniteAtomicPointMeasure
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Function.Floor

/-!
# Compactness and actual law tightness for finite point measures

The point-measure space is the literal subtype of finite measures that
are finite integer Dirac sums. It has the induced finite-measure weak
topology and its Borel sigma algebra. Bounded-count sets are compact by
finite unions of actual continuous atom-map images. First-mass moments
then give tightness of actual probability laws on this space.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FinitePointMeasureCompact

open FiniteAtomicPointMeasure

variable {E : Type*} [MeasurableSpace E]

/-- A finite integer atomic measure, including multiplicities. -/
def IsPointMeasure (μ : FiniteMeasure E) : Prop :=
  ∃ n : ℕ, ∃ x : Fin n → E, μ = ofAtoms x

/-- Actual point measures, rather than a presumed abstract point-process
space. The weak topology below is inherited from `FiniteMeasure`. -/
def PointMeasure (E : Type*) [MeasurableSpace E] :=
  {μ : FiniteMeasure E // IsPointMeasure μ}

instance : Coe (PointMeasure E) (FiniteMeasure E) := ⟨Subtype.val⟩

def ofAtomsPoint {n : ℕ} (x : Fin n → E) : PointMeasure E :=
  ⟨ofAtoms x, ⟨n, x, rfl⟩⟩

@[simp] theorem ofAtomsPoint_val {n : ℕ} (x : Fin n → E) :
    (ofAtomsPoint x : FiniteMeasure E) = ofAtoms x := rfl

/-- All integer atomic measures with at most `H` labelled atoms. -/
def boundedAtoms (H : ℕ) : Set (FiniteMeasure E) :=
  {μ | ∃ n ≤ H, ∃ x : Fin n → E, μ = ofAtoms x}

theorem boundedAtoms_eq_union (H : ℕ) :
    boundedAtoms (E := E) H =
      ⋃ n ∈ Finset.range (H + 1), Set.range (ofAtoms : (Fin n → E) → FiniteMeasure E) := by
  ext μ
  simp only [boundedAtoms, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_range]
  constructor
  · rintro ⟨n, hn, x, hx⟩
    exact ⟨n, Nat.lt_succ_iff.mpr hn, x, hx.symm⟩
  · rintro ⟨n, hn, x, hx⟩
    exact ⟨n, Nat.lt_succ_iff.mp hn, x, hx.symm⟩

variable [TopologicalSpace E] [OpensMeasurableSpace E]

instance : TopologicalSpace (PointMeasure E) :=
  inferInstanceAs (TopologicalSpace {μ : FiniteMeasure E // IsPointMeasure μ})

/-- The measurable structure of actual point-process laws is the Borel
structure of their weak topology. -/
instance : MeasurableSpace (PointMeasure E) := borel (PointMeasure E)

instance : BorelSpace (PointMeasure E) := ⟨rfl⟩

instance [HasOuterApproxClosed E] [BorelSpace E] : T2Space (PointMeasure E) :=
  inferInstanceAs (T2Space {μ : FiniteMeasure E // IsPointMeasure μ})

theorem continuous_val : Continuous (fun η : PointMeasure E ↦ (η : FiniteMeasure E)) :=
  continuous_subtype_val

theorem continuous_ofAtomsPoint (n : ℕ) :
    Continuous (ofAtomsPoint : (Fin n → E) → PointMeasure E) :=
  (continuous_ofAtoms n).subtype_mk _

theorem measurable_ofAtomsPoint [SecondCountableTopology E] (n : ℕ) :
    Measurable (ofAtomsPoint : (Fin n → E) → PointMeasure E) :=
  (continuous_ofAtomsPoint n).measurable

def mass (η : PointMeasure E) : ℝ≥0 := (η : FiniteMeasure E).mass

theorem continuous_mass : Continuous (mass : PointMeasure E → ℝ≥0) :=
  FiniteMeasure.continuous_mass.comp continuous_val

theorem measurable_mass : Measurable (mass : PointMeasure E → ℝ≥0) :=
  continuous_mass.measurable

omit [TopologicalSpace E] [OpensMeasurableSpace E] in
@[simp] theorem mass_ofAtomsPoint {n : ℕ} (x : Fin n → E) : mass (ofAtomsPoint x) = n :=
  ofAtoms_mass x

/-- The actual point count extracted from the integer mass. -/
def size (η : PointMeasure E) : ℕ := ⌊(mass η : ℝ)⌋₊

omit [TopologicalSpace E] [OpensMeasurableSpace E] in
@[simp] theorem size_ofAtomsPoint {n : ℕ} (x : Fin n → E) : size (ofAtomsPoint x) = n := by
  simp [size]

omit [TopologicalSpace E] [OpensMeasurableSpace E] in
theorem mass_eq_size (η : PointMeasure E) : mass η = (size η : ℝ≥0) := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  rw [he, mass_ofAtomsPoint, size_ofAtomsPoint]

theorem measurable_size : Measurable (size : PointMeasure E → ℕ) :=
  Nat.measurable_floor.comp (NNReal.continuous_coe.measurable.comp measurable_mass)

def count (η : PointMeasure E) (A : Set E) : ℕ :=
  ⌊(((η : FiniteMeasure E) A : ℝ))⌋₊

omit [TopologicalSpace E] [OpensMeasurableSpace E] in
theorem count_ofAtomsPoint {n : ℕ} (x : Fin n → E) {A : Set E} (hA : MeasurableSet A) :
    count (ofAtomsPoint x) A = atomCount x A := by
  unfold count
  have he : (((ofAtoms x) A : ℝ)) = (atomCount x A : ℝ) :=
    ofAtoms_apply_real x hA
  rw [ofAtomsPoint_val, he]
  simp

omit [TopologicalSpace E] [OpensMeasurableSpace E] in
/-- Literal cell evaluations agree with the integer point counts, not
merely a representation-dependent vector. -/
theorem measure_real_eq_count (η : PointMeasure E) {A : Set E} (hA : MeasurableSet A) :
    ((η : FiniteMeasure E) : Measure E).real A = (count η A : ℝ) := by
  obtain ⟨n, x, hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  rw [he, ofAtomsPoint_val, ofAtoms_apply_real x hA, count_ofAtomsPoint x hA]

omit [TopologicalSpace E] [OpensMeasurableSpace E] in
/-- Integrals of arbitrary real functions against an actual point
measure are finite literal sums. -/
theorem integral_of_rep [MeasurableSingletonClass E]
    (η : PointMeasure E) {n : ℕ} {x : Fin n → E}
    (hx : (η : FiniteMeasure E) = ofAtoms x) (f : E → ℝ) :
    (∫ z, f z ∂((η : FiniteMeasure E) : Measure E)) = ∑ i, f (x i) := by
  rw [hx, ofAtoms_integral]

variable [CompactSpace E]

/-- Integer atomic bounded-count sets are compact in the actual
finite-measure weak topology. -/
theorem isCompact_boundedAtoms (H : ℕ) : IsCompact (boundedAtoms (E := E) H) := by
  rw [boundedAtoms_eq_union]
  exact (Finset.range (H + 1)).isCompact_biUnion (fun n _ ↦
    isCompact_range (continuous_ofAtoms n))

omit [TopologicalSpace E] [OpensMeasurableSpace E] [CompactSpace E] in
theorem boundedAtoms_eq_mass_bound (H : ℕ) :
    boundedAtoms (E := E) H = {μ | IsPointMeasure μ ∧ μ.mass ≤ (H : ℝ≥0)} := by
  ext μ
  constructor
  · rintro ⟨n, hn, x, hx⟩
    refine ⟨⟨n, x, hx⟩, ?_⟩
    rw [hx, ofAtoms_mass]
    exact_mod_cast hn
  · rintro ⟨⟨n, x, hx⟩, hmass⟩
    refine ⟨n, ?_, x, hx⟩
    rw [hx, ofAtoms_mass] at hmass
    exact_mod_cast hmass

/-- The compact bounded-mass set belongs to the actual point-measure
space, not just its ambient finite-measure space. -/
theorem isCompact_mass_le (H : ℕ) :
    IsCompact {η : PointMeasure E | mass η ≤ (H : ℝ≥0)} := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : (fun η : PointMeasure E ↦ (η : FiniteMeasure E)) ''
      {η | mass η ≤ (H : ℝ≥0)} = boundedAtoms (E := E) H := by
    rw [boundedAtoms_eq_mass_bound]
    ext μ
    constructor
    · rintro ⟨η, hη, rfl⟩
      exact ⟨η.property, hη⟩
    · rintro ⟨hμ, hm⟩
      exact ⟨⟨μ, hμ⟩, hm, rfl⟩
  change IsCompact ((fun η : PointMeasure E ↦ (η : FiniteMeasure E)) ''
    {η | mass η ≤ (H : ℝ≥0)})
  rw [he]
  exact isCompact_boundedAtoms H

omit [CompactSpace E] in
/-- An actual first-mass moment gives the probability of escaping the
explicit compact integer-point cutoff. -/
theorem probability_mass_cutoff_compl_le (ν : ProbabilityMeasure (PointMeasure E))
    (hint : Integrable (fun η ↦ (mass η : ℝ)) (ν : Measure (PointMeasure E)))
    (H : ℕ) (hH : 0 < H) :
    (ν : Measure (PointMeasure E)) {η | mass η ≤ (H : ℝ≥0)}ᶜ ≤
      ENNReal.ofReal ((∫ η, (mass η : ℝ) ∂(ν : Measure (PointMeasure E))) / (H : ℝ)) := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hb := (hint.div_const (H : ℝ)).measure_le_integral
    (Eventually.of_forall (fun η ↦ div_nonneg (NNReal.coe_nonneg _) hHp.le))
    (s := {η | mass η ≤ (H : ℝ≥0)}ᶜ) (fun η hη ↦ by
      apply (le_div_iff₀ hHp).mpr
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hη
      simpa only [one_mul] using (show (H : ℝ) ≤ mass η by exact_mod_cast hη.le))
  simpa only [integral_div] using hb

/-- Uniform actual first-mass moments yield genuine tightness of actual
laws on the weak-topological point-measure space. -/
theorem isTightMeasureSet_of_mass_moment_bound {J : Type*}
    (ν : J → ProbabilityMeasure (PointMeasure E))
    (hint : ∀ j, Integrable (fun η ↦ (mass η : ℝ)) (ν j : Measure (PointMeasure E)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ η, (mass η : ℝ) ∂(ν j : Measure (PointMeasure E))) ≤ M) :
    IsTightMeasureSet (Set.range (fun j ↦ (ν j : Measure (PointMeasure E)))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ ↦ by simp [hεtop]⟩
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨H, hHlarge⟩ := exists_nat_gt (M / ε.toReal + 1)
  have hHp : (0 : ℝ) < H := by
    have hp : 0 ≤ M / ε.toReal := div_nonneg hM hεreal.le
    linarith
  have hH : 0 < H := by exact_mod_cast hHp
  have hcut : M / (H : ℝ) < ε.toReal := by
    apply (div_lt_iff₀ hHp).mpr
    have hm := (div_lt_iff₀ hεreal).mp (show M / ε.toReal < (H : ℝ) by linarith)
    nlinarith
  refine ⟨{η : PointMeasure E | mass η ≤ (H : ℝ≥0)}, isCompact_mass_le H, ?_⟩
  intro ζ hζ
  obtain ⟨j, rfl⟩ := hζ
  apply (probability_mass_cutoff_compl_le (ν j) (hint j) H hH).trans
  apply (ENNReal.ofReal_le_ofReal
    ((div_le_div_of_nonneg_right (hbound j) hHp.le).trans hcut.le)).trans
  exact ENNReal.ofReal_toReal_le

/-- The preceding actual law tightness also gives compact closure of
the family of weak point-process laws. The required Hausdorff property
is derived from the genuine finite-measure weak topology. -/
theorem isCompact_closure_of_mass_moment_bound [HasOuterApproxClosed E] [BorelSpace E]
    {J : Type*} (ν : J → ProbabilityMeasure (PointMeasure E))
    (hint : ∀ j, Integrable (fun η ↦ (mass η : ℝ)) (ν j : Measure (PointMeasure E)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ η, (mass η : ℝ) ∂(ν j : Measure (PointMeasure E))) ≤ M) :
    IsCompact (closure (Set.range ν)) := by
  apply isCompact_closure_of_isTightMeasureSet
  have hrange : {ζ : Measure (PointMeasure E) | ∃ p ∈ Set.range ν,
        (p : Measure (PointMeasure E)) = ζ} =
      Set.range (fun j ↦ (ν j : Measure (PointMeasure E))) := by
    ext ζ
    simp only [Set.mem_ofPred_eq, Set.mem_range, exists_exists_eq_and]
  rw [hrange]
  exact isTightMeasureSet_of_mass_moment_bound ν hint M hM hbound

/-- The literal compact size-and-bounded-surplus window of the paper. -/
abbrev SurplusWindow (a b : ℝ) (R : ℕ) := (Set.Icc a b) × Fin (R + 1)

/-- No compactness assumption on a putative point-process space is
needed for the paper's actual compact window. -/
theorem isCompact_window_mass_le (a b : ℝ) (R H : ℕ) :
    IsCompact {η : PointMeasure (SurplusWindow a b R) | mass η ≤ (H : ℝ≥0)} :=
  isCompact_mass_le H

theorem isTightMeasureSet_window_of_mass_moment_bound
    (a b : ℝ) (R : ℕ) {J : Type*}
    (ν : J → ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hint : ∀ j, Integrable (fun η ↦ (mass η : ℝ))
      (ν j : Measure (PointMeasure (SurplusWindow a b R))))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, (∫ η, (mass η : ℝ)
      ∂(ν j : Measure (PointMeasure (SurplusWindow a b R)))) ≤ M) :
    IsTightMeasureSet (Set.range (fun j ↦
      (ν j : Measure (PointMeasure (SurplusWindow a b R))))) :=
  isTightMeasureSet_of_mass_moment_bound ν hint M hM hbound

end PerronWright.FinitePointMeasureCompact
