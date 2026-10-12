import PerronWright.Enumeration.CoreAttachmentFieldWeightFactor
import PerronWright.Enumeration.DegreeTwoWeight
import PerronWright.Enumeration.LeafIterate
import PerronWright.Enumeration.PathKernelFullWeight
import PerronWright.Enumeration.JointSimpleCycleEGF
import PerronWright.Enumeration.UnicyclicCycleRange

/-!
# Exact finite-cycle weight / profile-trace bridge

The bridge is obtained by an explicit product-law Fubini recursion along the
path left after deleting one vertex of the cycle.
-/

open MeasureTheory
open scoped Classical BigOperators

noncomputable section

namespace PerronWright
namespace GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def complexEdgeFactor (M : CompactBJRModel S)
    {V : Type*} (x : V → S) (e : Sym2 V) : ℂ :=
  Sym2.lift ⟨fun i j ↦ (M.kernel (x i) (x j) : ℂ), by
    intro i j
    exact congrArg (fun r : ℝ ↦ (r : ℂ))
      (M.kernel.symmetric (x i) (x j))⟩ e

@[simp] private theorem complexEdgeFactor_mk
    (M : CompactBJRModel S) {V : Type*} (x : V → S) (i j : V) :
    complexEdgeFactor M x s(i,j) = (M.kernel (x i) (x j) : ℂ) := rfl

private theorem finiteComplexGraphIntegrand_eq
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → S) :
    finiteComplexGraphIntegrand M tau H x =
      (∏ v : V, tau (x v)) *
        ∏ e ∈ H.edgeFinset, complexEdgeFactor M x e := rfl

/-- The finite graph integrand is independent of the computational choices
of decidable equality and adjacency.  This small bridge lets the analytic
integral use `Classical` instances while the graph lemmas retain their
canonical finite-graph instances. -/
private theorem finiteComplexGraphIntegrand_decidable_instances
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {V : Type*} [Fintype V] (H : SimpleGraph V)
    (dV₁ dV₂ : DecidableEq V)
    (dH₁ dH₂ : DecidableRel H.Adj) (x : V → S) :
    @finiteComplexGraphIntegrand S _ _ _ _ M tau V _ dV₁ H dH₁ x =
      @finiteComplexGraphIntegrand S _ _ _ _ M tau V _ dV₂ H dH₂ x := by
  have hV : dV₁ = dV₂ := Subsingleton.elim _ _
  subst dV₂
  have hH : dH₁ = dH₂ := Subsingleton.elim _ _
  subst dH₂
  rfl

/-! ## Complex product-law Fubini and literal profile paths -/

/-- Product-law Fubini at coordinate zero, in the complex-valued form used
by the cycle weight. -/
private theorem integral_piFinSuccAbove_zero_continuous_complex
    (M : CompactBJRModel S) (n : ℕ)
    (F : (Fin (n + 1) → S) → ℂ) (hF : Continuous F) :
    (∫ x : Fin (n + 1) → S, F x
      ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) =
      ∫ y : S, ∫ z : Fin n → S,
        F (Fin.insertNth 0 y z)
        ∂Measure.pi (fun _ : Fin n ↦ M.mu) ∂M.mu := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ S) 0
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ M.mu) 0
  have hf : Integrable (fun x : Fin (n + 1) → S ↦ F x)
      (Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)) :=
    hF.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hprod : Integrable
      (fun p : S × (Fin n → S) ↦ F (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    _ = ∫ p : S × (Fin n → S), F (e.symm p)
        ∂M.mu.prod (Measure.pi (fun _ : Fin n ↦ M.mu)) := by
      exact (hmp.symm.integral_comp'
        (fun x : Fin (n + 1) → S ↦ F x)).symm
    _ = _ := by
      rw [integral_prod _ hprod]
      simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk]

/-- Reindex the products left after deleting one coordinate into the exact
finite complex graph integrand on the surviving labels. -/
private theorem finiteComplexGraphIntegrand_residual
    (M : CompactBJRModel S) (tau : C(S, ℂ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) [DecidableRel H.Adj]
    (v : Fin (n + 1))
    (y₀ : S) (z : Fin n → S) :
    ((∏ i ∈ Finset.univ.erase v,
        tau ((Fin.insertNth v y₀ z : Fin (n + 1) → S) i)) *
      (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
        complexEdgeFactor M (Fin.insertNth v y₀ z) e)) =
      finiteComplexGraphIntegrand M tau (H.comap v.succAbove) z := by
  unfold finiteComplexGraphIntegrand
  congr 1
  · rw [Fin.univ_succAbove n v]
    simp [Finset.prod_map, Fin.succAboveEmb]
  · have heq : (H.deleteIncidenceSet v).edgeFinset =
        ((H.comap v.succAbove).map v.succAboveEmb).edgeFinset := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [map_survivor_graph_eq_delete H v]
    rw [heq]
    have hmap :
        ((H.comap v.succAbove).map v.succAboveEmb).edgeFinset =
          (H.comap v.succAbove).edgeFinset.map v.succAboveEmb.sym2Map := by
      have hmap₀ := SimpleGraph.edgeFinset_map v.succAboveEmb
        (H.comap v.succAbove)
      ext e
      rw [← hmap₀]
      simp only [SimpleGraph.mem_edgeFinset]
    rw [hmap, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro e _
    induction e using Sym2.inductionOn with
    | _ i j =>
        change complexEdgeFactor M (Fin.insertNth v y₀ z)
            s(v.succAbove i, v.succAbove j) = _
        simp only [complexEdgeFactor_mk, Fin.insertNth_apply_succAbove]
        rfl

/-- Exact complex-profile factorization when the first vertex of a
nontrivial path is peeled off. -/
private theorem finiteComplexGraphIntegrand_path_first_split
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (m : ℕ)
    (y : S) (z : Fin (m + 1) → S) :
    finiteComplexGraphIntegrand M tau (SimpleGraph.pathGraph (m + 2))
        (Fin.insertNth 0 y z) =
      (tau y * (M.kernel y (z 0) : ℂ)) *
        finiteComplexGraphIntegrand M tau
          (SimpleGraph.pathGraph (m + 1)) z := by
  let G := SimpleGraph.pathGraph (m + 2)
  have hdeg : G.degree 0 = 1 := pathGraph_degree_zero m
  have hadj : G.Adj 0 ((0 : Fin (m + 2)).succAbove 0) := by
    simp [G, SimpleGraph.pathGraph_adj, Fin.zero_succAbove]
  rw [show finiteComplexGraphIntegrand M tau G (Fin.insertNth 0 y z) =
      (tau y * (M.kernel y (z 0) : ℂ)) *
        ((∏ i ∈ Finset.univ.erase (0 : Fin (m + 2)),
            tau ((Fin.insertNth 0 y z : Fin (m + 2) → S) i)) *
          (∏ e ∈ (G.deleteIncidenceSet 0).edgeFinset,
            complexEdgeFactor M (Fin.insertNth 0 y z) e)) by
    rw [finiteComplexGraphIntegrand_eq]
    simpa only [Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, complexEdgeFactor_mk] using
      (leaf_weight_product_split_at_neighbor G hdeg hadj
        (fun i ↦ tau ((Fin.insertNth 0 y z : Fin (m + 2) → S) i))
        (complexEdgeFactor M (Fin.insertNth 0 y z)))]
  rw [finiteComplexGraphIntegrand_residual M tau G 0 y z]
  simp only [G, pathGraph_comap_succAbove_zero]

private theorem finiteComplexGraphIntegrand_pathGraph_one
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (y : S) :
    finiteComplexGraphIntegrand M tau (SimpleGraph.pathGraph 1) ![y] =
      tau y := by
  have hgraph : SimpleGraph.pathGraph 1 = ⊥ := by
    ext u v
    fin_cases u
    fin_cases v
    simp
  rw [hgraph]
  unfold finiteComplexGraphIntegrand
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero,
    SimpleGraph.edgeFinset, SimpleGraph.edgeSet_bot,
    Set.toFinset_empty, Finset.prod_empty, mul_one]

/-- Literal finite-dimensional path observable with fixed endpoint types and
an arbitrary common complex profile on the internal vertices. -/
def complexProfilePathObservable
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (a b : S) : C((Fin (n + 1) → S), ℂ) := by
  refine ⟨fun x ↦
    (M.kernel a (x 0) : ℂ) *
      finiteComplexGraphIntegrand M tau
        (SimpleGraph.pathGraph (n + 1)) x *
      (M.kernel (x (Fin.last n)) b : ℂ), ?_⟩
  have hleft : Continuous
      (fun x : Fin (n + 1) → S ↦ (M.kernel a (x 0) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (M.kernel.toContinuousMap.continuous.comp
        (continuous_const.prodMk (continuous_apply 0)))
  have hright : Continuous
      (fun x : Fin (n + 1) → S ↦
        (M.kernel (x (Fin.last n)) b : ℂ)) :=
    Complex.continuous_ofReal.comp
      (M.kernel.toContinuousMap.continuous.comp
        ((continuous_apply (Fin.last n)).prodMk continuous_const))
  exact (hleft.mul (continuous_finiteComplexGraphIntegrand M tau
    (SimpleGraph.pathGraph (n + 1)))).mul hright

/-- The literal integrated weight of a path with `n` internal vertices,
where every internal vertex carries the common complex profile `tau`.
The case `n = 0` is the direct kernel edge. -/
def complexProfilePathWeight
    (M : CompactBJRModel S) (tau : C(S, ℂ)) : ℕ → S → S → ℂ
  | 0, a, b => (M.kernel a b : ℂ)
  | n + 1, a, b =>
      ∫ x : Fin (n + 1) → S,
        complexProfilePathObservable M tau n a b x
        ∂Measure.pi (fun _ : Fin (n + 1) ↦ M.mu)

private theorem complexProfilePathWeight_one
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (a b : S) :
    complexProfilePathWeight M tau 1 a b =
      ∫ y : S, (M.kernel a y : ℂ) * tau y *
        (M.kernel y b : ℂ) ∂M.mu := by
  change (∫ x : Fin 1 → S,
    complexProfilePathObservable M tau 0 a b x
      ∂Measure.pi (fun _ : Fin 1 ↦ M.mu)) = _
  rw [integral_piFinSuccAbove_zero_continuous_complex M 0
    (complexProfilePathObservable M tau 0 a b)
    (complexProfilePathObservable M tau 0 a b).continuous]
  apply integral_congr_ae
  filter_upwards [] with y
  have hx (z : Fin 0 → S) :
      (Fin.insertNth (0 : Fin 1) y z : Fin 1 → S) = ![y] := by
    funext i
    fin_cases i
    simp
  simp_rw [hx]
  change (∫ _z : Fin 0 → S,
      (M.kernel a y : ℂ) *
        finiteComplexGraphIntegrand M tau
          (SimpleGraph.pathGraph 1) ![y] *
        (M.kernel y b : ℂ)
      ∂Measure.pi (fun _ : Fin 0 ↦ M.mu)) = _
  rw [finiteComplexGraphIntegrand_pathGraph_one]
  simp only [integral_const, probReal_univ, one_smul]

private theorem complexProfilePathWeight_succ_succ
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (m : ℕ) (a b : S) :
    complexProfilePathWeight M tau (m + 2) a b =
      ∫ y : S, (M.kernel a y : ℂ) * tau y *
        complexProfilePathWeight M tau (m + 1) y b ∂M.mu := by
  change (∫ x : Fin (m + 2) → S,
    complexProfilePathObservable M tau (m + 1) a b x
      ∂Measure.pi (fun _ : Fin (m + 2) ↦ M.mu)) = _
  rw [integral_piFinSuccAbove_zero_continuous_complex M (m + 1)
    (complexProfilePathObservable M tau (m + 1) a b)
    (complexProfilePathObservable M tau (m + 1) a b).continuous]
  apply integral_congr_ae
  filter_upwards [] with y
  have hpoint (z : Fin (m + 1) → S) :
      complexProfilePathObservable M tau (m + 1) a b
          (Fin.insertNth 0 y z) =
        ((M.kernel a y : ℂ) * tau y) *
          complexProfilePathObservable M tau m y b z := by
    change
      (M.kernel a
          ((Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S) 0) : ℂ) *
          finiteComplexGraphIntegrand M tau
            (SimpleGraph.pathGraph (m + 2)) (Fin.insertNth 0 y z) *
          (M.kernel
            ((Fin.insertNth (0 : Fin (m + 2)) y z : Fin (m + 2) → S)
              (Fin.last (m + 1))) b : ℂ) = _
    rw [finiteComplexGraphIntegrand_path_first_split]
    simp only [Fin.insertNth_apply_same, insertNth_zero_last]
    change
      (M.kernel a y : ℂ) *
          (tau y * (M.kernel y (z 0) : ℂ) *
            finiteComplexGraphIntegrand M tau
              (SimpleGraph.pathGraph (m + 1)) z) *
          (M.kernel (z (Fin.last m)) b : ℂ) =
        ((M.kernel a y : ℂ) * tau y) *
          ((M.kernel y (z 0) : ℂ) *
            finiteComplexGraphIntegrand M tau
              (SimpleGraph.pathGraph (m + 1)) z *
            (M.kernel (z (Fin.last m)) b : ℂ))
    ring
  calc
    (∫ z : Fin (m + 1) → S,
        complexProfilePathObservable M tau (m + 1) a b
          (Fin.insertNth 0 y z)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ M.mu)) =
      ∫ z : Fin (m + 1) → S,
        ((M.kernel a y : ℂ) * tau y) *
          complexProfilePathObservable M tau m y b z
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ M.mu) := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact hpoint z
    _ = _ := by
      rw [integral_const_mul]
      rfl

private theorem complexProfilePathWeight_succ
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (a b : S) :
    complexProfilePathWeight M tau (n + 1) a b =
      ∫ y : S, (M.kernel a y : ℂ) * tau y *
        complexProfilePathWeight M tau n y b ∂M.mu := by
  cases n with
  | zero => exact complexProfilePathWeight_one M tau a b
  | succ m => exact complexProfilePathWeight_succ_succ M tau m a b

/-- A literal complex-profile path is exactly the appropriate power of the
path operator applied to the terminal kernel column. -/
theorem complexProfilePathWeight_eq_operatorPower
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (a b : S) :
    complexProfilePathWeight M tau n a b =
      (((JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau) ^ n)
        (M.kernel.complexColumns b)) a := by
  induction n generalizing a with
  | zero =>
      change (M.kernel a b : ℂ) =
        (((JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau) ^ 0)
          (M.kernel.complexColumns b)) a
      rw [pow_zero, one_apply_eq_self]
      rfl
  | succ n ih =>
      rw [complexProfilePathWeight_succ]
      rw [show (((JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau) ^
          (n + 1)) (M.kernel.complexColumns b)) a =
          JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau
            (((JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau) ^ n)
              (M.kernel.complexColumns b)) a by
            rw [pow_succ', mul_apply_eq_comp]]
      rw [JointSimpleCycleEGF.pathOperatorParameterCLM_apply,
        ContinuousKernel.complexAction_apply]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [ContinuousMap.mul_apply]
      rw [← ih y]
      ring

/-! ## Delete one cycle vertex and close the resulting path -/

/-- Deleting vertex zero from the standard cycle leaves the standard path on
the surviving labels. -/
private theorem cycleGraph_comap_succAbove_zero (n : ℕ) :
    (SimpleGraph.cycleGraph (n + 3)).comap
        (fun i : Fin (n + 2) ↦ (0 : Fin (n + 3)).succAbove i) =
      SimpleGraph.pathGraph (n + 2) := by
  ext i j
  rw [SimpleGraph.comap_adj, SimpleGraph.cycleGraph_adj',
    SimpleGraph.pathGraph_adj]
  simp only [Fin.zero_succAbove]
  change
    ((i.succ - j.succ).val = 1 ∨ (j.succ - i.succ).val = 1) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val)
  constructor
  · rintro (h | h)
    · by_cases hji : j.val ≤ i.val
      · right
        rw [Fin.sub_val_of_le (by simpa using hji)] at h
        simp only [Fin.val_succ] at h
        omega
      · rw [Fin.val_sub] at h
        simp only [Fin.val_succ] at h
        have hlt : n + 2 + 1 - (j.val + 1) + (i.val + 1) <
            n + 2 + 1 := by
          omega
        rw [Nat.mod_eq_of_lt hlt] at h
        omega
    · by_cases hij : i.val ≤ j.val
      · left
        rw [Fin.sub_val_of_le (by simpa using hij)] at h
        simp only [Fin.val_succ] at h
        omega
      · rw [Fin.val_sub] at h
        simp only [Fin.val_succ] at h
        have hlt : n + 2 + 1 - (i.val + 1) + (j.val + 1) <
            n + 2 + 1 := by
          omega
        rw [Nat.mod_eq_of_lt hlt] at h
        omega
  · rintro (h | h)
    · right
      have hij : i.val ≤ j.val := by omega
      rw [Fin.sub_val_of_le (by simpa using hij : i.succ ≤ j.succ)]
      simp only [Fin.val_succ]
      omega
    · left
      have hji : j.val ≤ i.val := by omega
      rw [Fin.sub_val_of_le (by simpa using hji : j.succ ≤ i.succ)]
      simp only [Fin.val_succ]
      omega

/-- Pointwise factorization of the standard cycle after its zero coordinate
is exposed. -/
private theorem finiteComplexGraphIntegrand_cycleGraph_insert_zero
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    (n : ℕ) (y : S) (z : Fin (n + 2) → S) :
    finiteComplexGraphIntegrand M tau (SimpleGraph.cycleGraph (n + 3))
        (Fin.insertNth 0 y z) =
      tau y * complexProfilePathObservable M tau (n + 1) y y z := by
  let a : Fin (n + 3) := 1
  let b : Fin (n + 3) := Fin.last (n + 2)
  have hdeg : (SimpleGraph.cycleGraph (n + 3)).degree 0 = 2 :=
    SimpleGraph.cycleGraph_degree_three_le
  have h₀a : (SimpleGraph.cycleGraph (n + 3)).Adj 0 a := by
    simp [a, SimpleGraph.cycleGraph_adj]
  have h₀b : (SimpleGraph.cycleGraph (n + 3)).Adj 0 b := by
    simp [b, SimpleGraph.cycleGraph_adj]
  have hab : a ≠ b := by
    intro h
    have hval : 1 = n + 2 := by
      simpa [a, b] using congrArg Fin.val h
    omega
  have hsplit := degreeTwo_weight_product_split
    (SimpleGraph.cycleGraph (n + 3)) hdeg h₀a h₀b hab
      (fun i ↦ tau ((Fin.insertNth 0 y z : Fin (n + 3) → S) i))
      (complexEdgeFactor M (Fin.insertNth 0 y z))
  rw [finiteComplexGraphIntegrand_eq]
  rw [hsplit]
  simp only [Fin.insertNth_apply_same, complexEdgeFactor_mk, a, b]
  change
    (tau y * (M.kernel y (z 0) : ℂ) *
        (M.kernel y (z (Fin.last (n + 1))) : ℂ)) *
      ((∏ x ∈ Finset.univ.erase (0 : Fin (n + 3)),
          tau ((Fin.insertNth 0 y z : Fin (n + 3) → S) x)) *
        ∏ e ∈ ((SimpleGraph.cycleGraph (n + 3)).deleteIncidenceSet 0).edgeFinset,
          complexEdgeFactor M (Fin.insertNth 0 y z) e) =
      tau y * ((M.kernel y (z 0) : ℂ) *
        finiteComplexGraphIntegrand M tau
          (SimpleGraph.pathGraph (n + 2)) z *
        (M.kernel (z (Fin.last (n + 1))) y : ℂ))
  calc
    _ = (tau y * (M.kernel y (z 0) : ℂ) *
          (M.kernel y (z (Fin.last (n + 1))) : ℂ)) *
        finiteComplexGraphIntegrand M tau
          ((SimpleGraph.cycleGraph (n + 3)).comap
            (0 : Fin (n + 3)).succAbove) z := by
      congr 1
      exact finiteComplexGraphIntegrand_residual M tau
        (SimpleGraph.cycleGraph (n + 3)) 0 y z
    _ = (tau y * (M.kernel y (z 0) : ℂ) *
          (M.kernel y (z (Fin.last (n + 1))) : ℂ)) *
        finiteComplexGraphIntegrand M tau
          (SimpleGraph.pathGraph (n + 2)) z := by
      congr 1
      simp only [cycleGraph_comap_succAbove_zero]
    _ = _ := by
      rw [M.kernel.symmetric y (z (Fin.last (n + 1)))]
      ring
/-- Exact canonical-cycle bridge: the genuine finite graph weight is the
direct profile cycle trace. -/
private theorem finiteComplexGraphWeight_cycleGraph_add_three_eq_profileCycleTrace
    (M : CompactBJRModel S) (tau : C(S, ℂ)) (n : ℕ) :
    finiteComplexGraphWeight M tau (SimpleGraph.cycleGraph (n + 3)) =
      JointSimpleCycleEGF.profileCycleTrace M tau (n + 2) := by
  let f : (Fin (n + 3) → S) → ℂ :=
    @finiteComplexGraphIntegrand S _ _ _ _ M tau (Fin (n + 3)) _
      (Classical.decEq _) (SimpleGraph.cycleGraph (n + 3))
      (Classical.decRel _)
  have hf : Continuous f := by
    exact @continuous_finiteComplexGraphIntegrand S _ _ _ _ M tau
      (Fin (n + 3)) _ (Classical.decEq _)
      (SimpleGraph.cycleGraph (n + 3)) (Classical.decRel _)
  unfold finiteComplexGraphWeight
  change (∫ x : Fin (n + 3) → S, f x
    ∂Measure.pi (fun _ : Fin (n + 3) ↦ M.mu)) = _
  have hFub := integral_piFinSuccAbove_zero_continuous_complex M (n + 2)
    f hf
  calc
    (∫ x : Fin (n + 3) → S,
        f x
        ∂Measure.pi (fun _ : Fin (n + 3) ↦ M.mu)) =
      ∫ y : S, ∫ z : Fin (n + 2) → S,
        f (Fin.insertNth 0 y z)
        ∂Measure.pi (fun _ : Fin (n + 2) ↦ M.mu) ∂M.mu := by
          simpa only [Nat.add_assoc] using hFub
    _ =
      ∫ y : S, tau y * complexProfilePathWeight M tau (n + 2) y y
        ∂M.mu := by
          apply integral_congr_ae
          filter_upwards [] with y
          change
            (∫ z : Fin (n + 2) → S,
              f (Fin.insertNth 0 y z)
              ∂Measure.pi (fun _ : Fin (n + 2) ↦ M.mu)) =
            tau y *
              ∫ z : Fin (n + 2) → S,
                complexProfilePathObservable M tau (n + 1) y y z
                ∂Measure.pi (fun _ : Fin (n + 2) ↦ M.mu)
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          calc
            f (Fin.insertNth 0 y z) =
                finiteComplexGraphIntegrand M tau
                  (SimpleGraph.cycleGraph (n + 3))
                  (Fin.insertNth 0 y z) := by
              apply finiteComplexGraphIntegrand_decidable_instances
            _ = tau y * complexProfilePathObservable M tau (n + 1) y y z :=
              finiteComplexGraphIntegrand_cycleGraph_insert_zero M tau n y z
    _ = ∫ y : S,
        (((JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau) ^ (n + 2))
          (M.kernel.complexColumns y)) y * tau y ∂M.mu := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [complexProfilePathWeight_eq_operatorPower]
          ring
    _ = JointSimpleCycleEGF.operatorCyclePairing M
        ((JointSimpleCycleEGF.MPR.pathOperatorParameterCLM M tau) ^ (n + 2))
        tau := (JointSimpleCycleEGF.operatorCyclePairing_apply M _ _).symm
    _ = JointSimpleCycleEGF.profileCycleTrace M tau (n + 2) := rfl

theorem finiteComplexGraphWeight_cycleGraph_eq_profileCycleTrace
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    finiteComplexGraphWeight M tau (SimpleGraph.cycleGraph q) =
      JointSimpleCycleEGF.profileCycleTrace M tau (q - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hq
  have hindex : n + 3 - 1 = n + 2 := by omega
  rw [hindex]
  exact finiteComplexGraphWeight_cycleGraph_add_three_eq_profileCycleTrace
    M tau n

/-! ## Labelled-cycle sum and the exact `1/(2q)` term -/

private theorem sum_graphRange_finiteComplexGraphWeight_eq_card_mul_profileCycleTrace
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    (∑ H ∈ FullCyclePerm.graphRange q, finiteComplexGraphWeight M tau H) =
      (FullCyclePerm.graphRange q).card *
        JointSimpleCycleEGF.profileCycleTrace M tau (q - 1) := by
  calc
    (∑ H ∈ FullCyclePerm.graphRange q,
        finiteComplexGraphWeight M tau H) =
      ∑ _H ∈ FullCyclePerm.graphRange q,
        JointSimpleCycleEGF.profileCycleTrace M tau (q - 1) := by
          apply Finset.sum_congr rfl
          intro H hH
          rcases Finset.mem_image.mp hH with ⟨σ, -, rfl⟩
          obtain ⟨e⟩ := FullCyclePerm.nonempty_cycleGraph_iso_graph hq σ
          rw [← finiteComplexGraphWeight_iso M tau
            (SimpleGraph.cycleGraph q) (FullCyclePerm.graph σ) e]
          exact finiteComplexGraphWeight_cycleGraph_eq_profileCycleTrace M tau hq
    _ = (FullCyclePerm.graphRange q).card *
        JointSimpleCycleEGF.profileCycleTrace M tau (q - 1) := by simp

/-- Denominator-free labelled EGF identity for all unoriented labelled
`q`-cycles. -/
private theorem two_mul_q_mul_sum_graphRange_finiteComplexGraphWeight
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    ((2 : ℂ) * q) *
        (∑ H ∈ FullCyclePerm.graphRange q,
          finiteComplexGraphWeight M tau H) =
      (q.factorial : ℂ) *
        JointSimpleCycleEGF.profileCycleTrace M tau (q - 1) := by
  rw [sum_graphRange_finiteComplexGraphWeight_eq_card_mul_profileCycleTrace
    M tau hq]
  have hcount := FullCyclePerm.card_graphRange_mul_two_mul_q_eq_factorial hq
  have hcountℂ :
      ((FullCyclePerm.graphRange q).card : ℂ) * ((2 : ℂ) * q) =
        (q.factorial : ℂ) := by
    exact_mod_cast hcount
  calc
    ((2 : ℂ) * q) *
        ((FullCyclePerm.graphRange q).card *
          JointSimpleCycleEGF.profileCycleTrace M tau (q - 1)) =
      (((FullCyclePerm.graphRange q).card : ℂ) * ((2 : ℂ) * q)) *
        JointSimpleCycleEGF.profileCycleTrace M tau (q - 1) := by ring
    _ = _ := by rw [hcountℂ]

/-- After the labelled `q!` normalization, the sum over all unoriented
labelled cycles is exactly the direct simple-cycle term indexed by `q-3`. -/
private theorem sum_graphRange_div_factorial_eq_profileSimpleCycleTerm
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    (∑ H ∈ FullCyclePerm.graphRange q,
        finiteComplexGraphWeight M tau H) / (q.factorial : ℂ) =
      JointSimpleCycleEGF.profileSimpleCycleTerm M tau (q - 3) := by
  rw [sum_graphRange_finiteComplexGraphWeight_eq_card_mul_profileCycleTrace
    M tau hq]
  rw [JointSimpleCycleEGF.profileSimpleCycleTerm]
  have hindex : q - 3 + 2 = q - 1 := by omega
  have hden : ((q - 3 : ℕ) : ℂ) + 3 = q := by
    exact_mod_cast (by omega : q - 3 + 3 = q)
  rw [hindex, hden]
  have hcard : (FullCyclePerm.graphRange q).card ≠ 0 := by
    intro hzero
    have hcount := FullCyclePerm.card_graphRange_mul_two_mul_q_eq_factorial hq
    rw [hzero, zero_mul] at hcount
    exact Nat.factorial_ne_zero q hcount.symm
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hcardℂ : ((FullCyclePerm.graphRange q).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard
  have hcount := FullCyclePerm.card_graphRange_mul_two_mul_q_eq_factorial hq
  have hcountℂ :
      ((FullCyclePerm.graphRange q).card : ℂ) * ((2 : ℂ) * q) =
        (q.factorial : ℂ) := by
    exact_mod_cast hcount
  rw [← hcountℂ]
  field_simp [hcardℂ, hq₀]

/-! ## Direct interface for the core-attachment sum -/

/-- The admissible surplus-zero core subtype sum is literally the finite
`graphRange` sum.  This is the shape consumed by the global core-attachment
formula. -/
private theorem sum_admissibleAttachmentCore_zero_eq_sum_graphRange
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
        finiteComplexGraphWeight M tau H.1) =
      ∑ H ∈ FullCyclePerm.graphRange q,
        finiteComplexGraphWeight M tau H := by
  rw [FullCyclePerm.graphRange_eq_admissibleAttachmentCores_zero hq]
  symm
  exact Finset.sum_subtype (admissibleAttachmentCores q 0)
    (fun _ ↦ mem_admissibleAttachmentCores) (fun H ↦
      finiteComplexGraphWeight M tau H)

/-- Direct `1/(2q)` simple-cycle interface in the exact subtype-sum form
appearing in the core-attachment expansion. -/
theorem sum_admissibleAttachmentCore_zero_div_factorial_eq_profileSimpleCycleTerm
    (M : CompactBJRModel S) (tau : C(S, ℂ))
    {q : ℕ} (hq : 3 ≤ q) :
    (∑ H : {H : SimpleGraph (Fin q) //
        IsAdmissibleAttachmentCore q 0 H},
        finiteComplexGraphWeight M tau H.1) / (q.factorial : ℂ) =
      JointSimpleCycleEGF.profileSimpleCycleTerm M tau (q - 3) := by
  rw [sum_admissibleAttachmentCore_zero_eq_sum_graphRange M tau hq]
  exact sum_graphRange_div_factorial_eq_profileSimpleCycleTerm M tau hq

end GraphCore
end PerronWright
