import PerronWright.Probability.CountableFixedSupportLocalMain

/-! # Actual fixed-support local estimates for varying input parameters

The input parameter belongs to the literal empirical-normalized source.
The reference finite parameter absorbs the proved rounding spectral error,
including the convergent varying input. The resulting estimates concern
the source density at its own actual parameter, not a limit-law continuity
substitute for control of the graph measures.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

def fixedSupportLocalExpectation (M : CountableKernel) (m : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {q : ℕ} (n : ℕ) (y : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
    ∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) (n + 1)) r : ℝ)
      ∂M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n

def fixedSupportReferenceDensity (M : CountableKernel) (m : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {q : ℕ} (y : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  FactorialDensity.density
    ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
    ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
    lambda y r

/-- Index `N` is the number of vertices; the original source parameter
sequence is indexed by `N-1`, matching the actual graph-law convention. -/
def fixedSupportVaryingEffectiveParameter (M : CountableKernel) (m : ℕ)
    (ell : ℕ → ℝ) (N : ℕ) : ℝ :=
  CriticalParameterDrift.effectiveParameter (ell (N - 1)) (M.fixedSupportRootRatio m) N

theorem fixedSupportVaryingEffectiveParameter_tendsto (M : CountableKernel) (m : ℕ)
    (ell : ℕ → ℝ) (lambda : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) :
    Tendsto (M.fixedSupportVaryingEffectiveParameter m ell) atTop (𝓝 lambda) := by
  have hp : Tendsto (fun N : ℕ ↦ N - 1) atTop atTop := tendsto_atTop.mpr (fun b ↦ by
    filter_upwards [eventually_ge_atTop (b + 1)] with N hN
    omega)
  have he := hl.comp hp
  have hd := M.fixedSupportRootRatio_scaled_drift m hlower hlo
  have hr := (CriticalParameterDrift.sigma_tendsto_one hd).sub_const 1
  simp only [sub_self] at hr
  have h := (he.add hd).add (he.mul hr)
  simp only [add_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (CriticalParameterDrift.effectiveParameter_eq (by omega : 0 < N)
    (ell (N - 1)) (M.fixedSupportRootRatio m)).symm

theorem fixedSupport_varying_local_error_limit_parameter
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |M.fixedSupportLocalExpectation m (ell n) hlower hlo n y r -
        M.fixedSupportReferenceDensity m lambda hlower hlo y r| < ε := by
  let F := M.fixedSupportModel m hlower hlo
  let hF : F.IsCritical := M.fixedSupportModel_isCritical m hlower hlo
  let c : ℕ → (Finset.range (m + 1)) → ℕ := fun N ↦
    FiniteIrreducibleTypePlacementMultiplicity.fiberCount (M.fixedSupportVertexTypes m N)
  have hround : ∀ᶠ N in atTop, ∀ s, |(c N s : ℝ) - (N : ℝ) * F.weight s| ≤ 2 * (m + 1 : ℝ) :=
    Eventually.of_forall (fun N s ↦ M.fixedSupportVertexTypes_rounding_bound m N hlower hlo s)
  have h := FiniteIrreducibleVaryingMarkedLocalMain.eventually_uniform_floor_marked_factorial_density
    F hF q R hq (M.fixedSupportVaryingEffectiveParameter m ell) lambda a b
    (M.fixedSupportVaryingEffectiveParameter_tendsto m ell lambda hl hlower hlo) ha hb c
    (2 * (m + 1 : ℝ)) (by positivity) hround (fun _ ↦ 1) continuous_const hε
  filter_upwards [(tendsto_add_atTop_nat 1).eventually h] with n hn
  intro y r hya hyb hr
  have he := hn (M.fixedSupportVertexTypes m (n + 1)) (fun _ ↦ rfl) y r hya hyb hr
  unfold FiniteIrreducibleMarkedLocalMain.scaledMarkedFactorialExpectation at he
  simp only [AnnealedMarkedFactorialCounting.markedCount_one, mul_one] at he
  change |((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
    (∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) (n + 1)) r : ℝ)
      ∂FiniteIrreducibleComponentProcess.graphLaw F
        (M.fixedSupportVaryingEffectiveParameter m ell (n + 1)) (n + 1)
        (M.fixedSupportVertexTypes m (n + 1))) - _| < ε at he
  have hp : M.fixedSupportVaryingEffectiveParameter m ell (n + 1) =
      M.fixedSupportEffectiveParameter m (ell n) (n + 1) := by
    simp only [fixedSupportVaryingEffectiveParameter, Nat.add_sub_cancel,
      fixedSupportEffectiveParameter]
  rw [hp, M.fixedSupportModel_graphLaw_eq_actual m n (ell n) hlower hlo] at he
  exact he

/-- The graph error is small compared with the reference density at
the actual varying parameter, uniformly for all size/surplus tuples. -/
theorem fixedSupport_varying_local_error
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (ell : ℕ → ℝ) (lambda a b : ℝ) (hl : Tendsto ell atTop (𝓝 lambda))
    (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |M.fixedSupportLocalExpectation m (ell n) hlower hlo n y r -
        M.fixedSupportReferenceDensity m (ell n) hlower hlo y r| < ε := by
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [M.fixedSupport_varying_local_error_limit_parameter
    m q R hq ell lambda a b hl ha hb hlower hlo hε2,
    FiniteIrreducibleVaryingDensity.eventually_uniform_parameter_density
      ((M.fixedSupportModel m hlower hlo).alpha (M.fixedSupportModel_isCritical m hlower hlo))
      ((M.fixedSupportModel m hlower hlo).beta (M.fixedSupportModel_isCritical m hlower hlo))
      ell lambda hl q R a b ha hε2] with n hn hd
  intro y r hya hyb hr
  have he1 := hn y r hya hyb hr
  have he2 := hd y r hya hyb hr
  change |M.fixedSupportReferenceDensity m (ell n) hlower hlo y r -
    M.fixedSupportReferenceDensity m lambda hlower hlo y r| < ε / 2 at he2
  have he := abs_sub_le (M.fixedSupportLocalExpectation m (ell n) hlower hlo n y r)
    (M.fixedSupportReferenceDensity m lambda hlower hlo y r)
    (M.fixedSupportReferenceDensity m (ell n) hlower hlo y r)
  rw [abs_sub_comm (M.fixedSupportReferenceDensity m lambda hlower hlo y r)] at he
  exact he.trans_lt (by linarith)

end PerronWright.CountableKernel
