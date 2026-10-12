import PerronWright.Analysis.AnalyticVerticalDivision
import Mathlib.Analysis.Calculus.FDeriv.Analytic

open scoped NNReal ENNReal
open Topology

noncomputable section

/-!
Scratch implementation of the local analytic primitive in one distinguished
complex coordinate.  The construction is coefficientwise and therefore keeps
an arbitrary Banach parameter space; it does not use a parameter-dependent
choice of one-variable primitives.
-/

namespace PerronWright.AnalyticVerticalPrimitive

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

private abbrev V (E : Type*) := E × ℂ

private def horiz : V E →L[ℂ] V E :=
  (ContinuousLinearMap.fst ℂ E ℂ).prod 0

private def vert : V E →L[ℂ] V E :=
  (0 : V E →L[ℂ] E).prod (ContinuousLinearMap.snd ℂ E ℂ)

private def verticalVector : V E := (0, 1)

private def verticalCoordinate : V E →L[ℂ] ℂ :=
  ContinuousLinearMap.snd ℂ E ℂ

omit [CompleteSpace F] in
private theorem horiz_add_vert (x : V E) : horiz x + vert x = x := by
  ext <;> simp [horiz, vert]

omit [CompleteSpace F] in
private theorem vert_apply (x : V E) : vert x = x.2 • verticalVector := by
  ext <;> simp [vert, verticalVector]

omit [CompleteSpace F] in
private theorem horiz_norm_le_one : ‖(horiz : V E →L[ℂ] V E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  rintro ⟨x, z⟩
  simp [horiz, Prod.norm_def]

omit [CompleteSpace F] in
private theorem vert_norm_le_one : ‖(vert : V E →L[ℂ] V E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  rintro ⟨x, z⟩
  simp [vert, Prod.norm_def]

omit [CompleteSpace F] in
private theorem verticalCoordinate_norm_le_one :
    ‖(verticalCoordinate : V E →L[ℂ] ℂ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  rintro ⟨x, z⟩
  simp [verticalCoordinate, Prod.norm_def]

omit [NormedSpace ℂ E] [CompleteSpace F] in
private theorem norm_verticalVector : ‖(verticalVector : V E)‖ = 1 := by
  simp [verticalVector, Prod.norm_def]

private def selectedMap {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : V E →L[ℂ] V E :=
  if i ∈ s then vert else horiz

private def selectedCoeff {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F :=
  p.compContinuousLinearMap (selectedMap s)

private def primitiveTerm {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => V E) F :=
  (verticalCoordinate.smulRight
      ((((s.card + 1 : ℕ) : ℂ)⁻¹) • selectedCoeff p s)).uncurryLeft

private def primitiveCoeff (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => V E) F :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, primitiveTerm p s

private def primitiveSeries
    (p : FormalMultilinearSeries ℂ (V E) F) : FormalMultilinearSeries ℂ (V E) F
  | 0 => 0
  | n + 1 => primitiveCoeff n (p n)

omit [CompleteSpace F] in
private theorem weight_norm_le_one {n : ℕ} (s : Finset (Fin n)) :
    ‖(((s.card + 1 : ℕ) : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_natCast]
  apply inv_le_one_of_one_le₀
  norm_num

omit [CompleteSpace F] in
private theorem norm_selectedCoeff_le {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) : ‖selectedCoeff p s‖ ≤ ‖p‖ := by
  have hL (i : Fin n) : ‖(selectedMap s i : V E →L[ℂ] V E)‖ ≤ 1 := by
    simp only [selectedMap]
    split_ifs
    · exact vert_norm_le_one
    · exact horiz_norm_le_one
  have hprod : (∏ i : Fin n, ‖(selectedMap s i : V E →L[ℂ] V E)‖) ≤ 1 := by
    simpa using Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hL i)
  calc
    ‖selectedCoeff p s‖ ≤
        ‖p‖ * ∏ i : Fin n, ‖(selectedMap s i : V E →L[ℂ] V E)‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖p‖ := by nlinarith [norm_nonneg p]

omit [CompleteSpace F] in
private theorem norm_primitiveTerm_le {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) : ‖primitiveTerm p s‖ ≤ ‖p‖ := by
  rw [primitiveTerm, ContinuousLinearMap.uncurryLeft_norm,
    ContinuousLinearMap.norm_smulRight_apply, norm_smul]
  calc
    ‖(verticalCoordinate : V E →L[ℂ] ℂ)‖ *
          (‖(((s.card + 1 : ℕ) : ℂ)⁻¹)‖ * ‖selectedCoeff p s‖)
        ≤ 1 * (1 * ‖p‖) := by
          gcongr
          · exact verticalCoordinate_norm_le_one
          · exact weight_norm_le_one s
          · exact norm_selectedCoeff_le p s
    _ = ‖p‖ := by ring

omit [CompleteSpace F] in
private theorem norm_primitiveCoeff_le (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F) :
    ‖primitiveCoeff n p‖ ≤ (2 : ℝ) ^ n * ‖p‖ := by
  unfold primitiveCoeff
  calc
    ‖∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, primitiveTerm p s‖
        ≤ ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset, ‖primitiveTerm p s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _s ∈ (Finset.univ : Finset (Fin n)).powerset, ‖p‖ := by
      gcongr with s hs
      exact norm_primitiveTerm_le p s
    _ = (2 : ℝ) ^ n * ‖p‖ := by simp

private theorem primitive_geometric_identity (C R : ℝ) (hR : R ≠ 0) (n : ℕ) :
    (2 ^ n * (C * R ^ n)) * (1 / (2 * R)) ^ (n + 1) = C / (2 * R) := by
  rw [div_pow]
  norm_num only [one_pow]
  field_simp [hR, pow_succ, mul_pow]
  ring

omit [CompleteSpace F] in
private theorem primitiveSeries_radius_pos
    (p : FormalMultilinearSeries ℂ (V E) F) (hp : 0 < p.radius) :
    0 < (primitiveSeries p).radius := by
  obtain ⟨C, R, hC, hR, hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let r : ℝ≥0 := ⟨1 / (2 * R), le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) hR))⟩
  have hr : 0 < r := one_div_pos.mpr (mul_pos (by norm_num) hR)
  have hD : 0 ≤ C / (2 * R) := by positivity
  have hrad : (r : ℝ≥0∞) ≤ (primitiveSeries p).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ (C / (2 * R))
    intro m
    cases m with
    | zero => simp [primitiveSeries, hD]
    | succ n =>
        have hterm : ‖primitiveSeries p (n + 1)‖ ≤
            2 ^ n * (C * R ^ n) := by
          calc
            ‖primitiveSeries p (n + 1)‖ = ‖primitiveCoeff n (p n)‖ := rfl
            _ ≤ 2 ^ n * ‖p n‖ := norm_primitiveCoeff_le n (p n)
            _ ≤ 2 ^ n * (C * R ^ n) := by gcongr; exact hbound n
        calc
          ‖primitiveSeries p (n + 1)‖ * (r : ℝ) ^ (n + 1)
              ≤ (2 ^ n * (C * R ^ n)) * (r : ℝ) ^ (n + 1) := by gcongr
          _ = C / (2 * R) := by
            change (2 : ℝ) ^ n * (C * R ^ n) * (1 / (2 * R)) ^ (n + 1) = _
            exact primitive_geometric_identity C R (ne_of_gt hR) n
  exact lt_of_lt_of_le (by exact_mod_cast hr) hrad

omit [CompleteSpace F] in
private theorem primitiveTerm_apply {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) (m : Fin (n + 1) → V E) :
    primitiveTerm p s m =
      (m 0).2 • ((((s.card + 1 : ℕ) : ℂ)⁻¹) • selectedCoeff p s (Fin.tail m)) := by
  simp [primitiveTerm, verticalCoordinate]

omit [CompleteSpace F] in
private theorem selectedCoeff_update_of_mem {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) (x : V E) {i : Fin n} (hi : i ∈ s) :
    x.2 • selectedCoeff p s (Function.update (fun _ => x) i verticalVector) =
      selectedCoeff p s (fun _ => x) := by
  let m : Fin n → V E := fun j => if j = i then verticalVector else selectedMap s j x
  have hbase : (fun j : Fin n => selectedMap s j x) =
      Function.update m i (x.2 • verticalVector) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [m, selectedMap, hi, vert_apply]
    · simp [m, hji]
  have hupdate :
      (fun j : Fin n => selectedMap s j ((Function.update (fun _ => x) i verticalVector) j)) =
        Function.update m i verticalVector := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [m, selectedMap, hi, verticalVector, vert]
    · simp [m, hji]
  unfold selectedCoeff
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hbase, hupdate, p.map_update_smul]

omit [CompleteSpace F] in
private theorem selectedCoeff_update_of_not_mem {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) (x : V E) {i : Fin n} (hi : i ∉ s) :
    selectedCoeff p s (Function.update (fun _ => x) i verticalVector) = 0 := by
  let m : Fin n → V E := fun j => selectedMap s j x
  have hupdate :
      (fun j : Fin n => selectedMap s j ((Function.update (fun _ => x) i verticalVector) j)) =
        Function.update m i 0 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [m, selectedMap, hi, verticalVector, horiz]
    · simp [m, hji]
  unfold selectedCoeff
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hupdate]
  exact p.map_update_zero m i

omit [CompleteSpace F] in
private theorem selectedCoeff_vertical_sum {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) (x : V E) :
    ∑ i : Fin n,
        x.2 • selectedCoeff p s (Function.update (fun _ => x) i verticalVector) =
      s.card • selectedCoeff p s (fun _ => x) := by
  classical
  calc
    ∑ i : Fin n,
        x.2 • selectedCoeff p s (Function.update (fun _ => x) i verticalVector) =
        ∑ i ∈ s,
          x.2 • selectedCoeff p s (Function.update (fun _ => x) i verticalVector) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      rw [selectedCoeff_update_of_not_mem p s x hi, smul_zero]
    _ = ∑ _i ∈ s, selectedCoeff p s (fun _ => x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact selectedCoeff_update_of_mem p s x hi
    _ = s.card • selectedCoeff p s (fun _ => x) := by simp

omit [CompleteSpace F] in
private theorem primitiveTerm_diag_derivative {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F)
    (s : Finset (Fin n)) (x : V E) :
    ∑ i : Fin (n + 1),
        primitiveTerm p s (Function.update (fun _ => x) i verticalVector) =
      selectedCoeff p s (fun _ => x) := by
  classical
  let w : ℂ := (((s.card + 1 : ℕ) : ℂ)⁻¹)
  let c : F := selectedCoeff p s (fun _ => x)
  have hfirst :
      primitiveTerm p s (Function.update (fun _ => x) 0 verticalVector) = w • c := by
    rw [primitiveTerm_apply]
    have hhead :
        ((Function.update (fun _ : Fin (n + 1) => x) 0 verticalVector) 0).2 =
          (1 : ℂ) := by
      simp [verticalVector]
    have htail :
        Fin.tail (Function.update (fun _ : Fin (n + 1) => x) 0 verticalVector) =
          (fun _ : Fin n => x) := by
      rw [Fin.tail_update_zero]
      rfl
    rw [hhead, htail, one_smul]
  have hsucc (i : Fin n) :
      primitiveTerm p s (Function.update (fun _ => x) i.succ verticalVector) =
        x.2 • (w • selectedCoeff p s
          (Function.update (fun _ => x) i verticalVector)) := by
    rw [primitiveTerm_apply]
    have hhead :
        (Function.update (fun _ : Fin (n + 1) => x) i.succ verticalVector) 0 = x := by
      exact Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
    have htail :
        Fin.tail (Function.update (fun _ : Fin (n + 1) => x) i.succ verticalVector) =
          Function.update (fun _ : Fin n => x) i verticalVector := by
      rw [Fin.tail_update_succ]
      rfl
    rw [hhead, htail]
  rw [Fin.sum_univ_succ]
  rw [hfirst]
  simp_rw [hsucc]
  have hs := selectedCoeff_vertical_sum p s x
  change w • c + ∑ i : Fin n,
      x.2 • (w • selectedCoeff p s (Function.update (fun _ => x) i verticalVector)) = c
  have hswap (z : F) : x.2 • (w • z) = w • (x.2 • z) := by
    simp only [smul_smul]
    rw [mul_comm]
  simp_rw [hswap]
  rw [← Finset.smul_sum]
  rw [← Nat.cast_smul_eq_nsmul ℂ] at hs
  rw [hs]
  rw [smul_smul, ← add_smul]
  have hne : ((s.card + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s.card
  have hw : w + w * (s.card : ℂ) = 1 := by
    dsimp [w]
    field_simp [hne]
    push_cast
    ring
  rw [hw, one_smul]

omit [CompleteSpace F] in
private theorem selectedMap_diag_eq_piecewise {n : ℕ}
    (s : Finset (Fin n)) (x : V E) :
    (fun i : Fin n => selectedMap s i x) =
      s.piecewise (fun _ => vert x) (fun _ => horiz x) := by
  classical
  funext i
  by_cases hi : i ∈ s <;> simp [selectedMap, hi]

omit [CompleteSpace F] in
private theorem selectedCoeff_sum {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F) (x : V E) :
    ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
        selectedCoeff p s (fun _ => x) = p (fun _ => x) := by
  classical
  have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
    ext s
    simp
  rw [hpow]
  have h := p.map_add_univ (fun _ : Fin n => vert x) (fun _ => horiz x)
  rw [show (fun _ : Fin n => vert x) + (fun _ => horiz x) = (fun _ => x) by
    funext i
    simp only [Pi.add_apply]
    rw [add_comm, horiz_add_vert]] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro s hs
  unfold selectedCoeff
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [selectedMap_diag_eq_piecewise]

omit [CompleteSpace F] in
private theorem primitiveCoeff_diag_derivative (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F) (x : V E) :
    ∑ i : Fin (n + 1),
        primitiveCoeff n p (Function.update (fun _ => x) i verticalVector) =
      p (fun _ => x) := by
  classical
  unfold primitiveCoeff
  simp_rw [sum_apply]
  rw [Finset.sum_comm]
  simp_rw [primitiveTerm_diag_derivative p]
  exact selectedCoeff_sum p x

private def omittedIndexEquiv (n : ℕ) :
    Fin (1 + n) ≃ {s : Finset (Fin (1 + n)) // s.card = n} := by
  classical
  refine Equiv.ofBijective
    (fun i : Fin (1 + n) =>
      ⟨(Finset.univ : Finset (Fin (1 + n))).erase i, by simp⟩) ?_
  constructor
  · intro i j hij
    by_contra hne
    have himem : i ∈ (Finset.univ : Finset (Fin (1 + n))).erase j := by simp [hne]
    have hval : (Finset.univ : Finset (Fin (1 + n))).erase i =
        (Finset.univ : Finset (Fin (1 + n))).erase j := congrArg Subtype.val hij
    rw [← hval] at himem
    simp at himem
  · intro s
    have hsne : s.1 ≠ (Finset.univ : Finset (Fin (1 + n))) := by
      intro hs
      have hc := congrArg Finset.card hs
      simp [s.2] at hc
    have hss : s.1 ⊂ (Finset.univ : Finset (Fin (1 + n))) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hsne⟩
    obtain ⟨i, _hi, hsub⟩ := Finset.ssubset_iff_exists_subset_erase.mp hss
    have heq : s.1 = (Finset.univ : Finset (Fin (1 + n))).erase i :=
      Finset.eq_of_subset_of_card_le hsub (by simp [s.2])
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact heq.symm

@[simp] private theorem omittedIndexEquiv_apply_val (n : ℕ) (i : Fin (1 + n)) :
    (omittedIndexEquiv n i).1 = (Finset.univ : Finset (Fin (1 + n))).erase i :=
  rfl

omit [CompleteSpace F] in
private theorem derivSeries_apply_vertical
    (q : FormalMultilinearSeries ℂ (V E) F) (n : ℕ) (x : V E) :
    q.derivSeries n (fun _ => x) verticalVector =
      ∑ i : Fin (n + 1),
        q (n + 1) (Function.update (fun _ => x) i verticalVector) := by
  classical
  have hnative :
      q.derivSeries n (fun _ => x) verticalVector =
        ∑ i : Fin (1 + n),
          q (1 + n) (Function.update (fun _ => x) i verticalVector) := by
    simp only [FormalMultilinearSeries.derivSeries,
      ContinuousLinearMap.compFormalMultilinearSeries_apply,
      FormalMultilinearSeries.changeOriginSeries,
      ContinuousLinearMap.compContinuousMultilinearMap_coe,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_coe,
      Function.comp_apply, map_sum, _root_.sum_apply,
      continuousMultilinearCurryFin1_apply, Matrix.zero_empty]
    refine (Fintype.sum_equiv (omittedIndexEquiv n)
      (fun i : Fin (1 + n) =>
        q (1 + n) (Function.update (fun _ => x) i verticalVector))
      (fun s : {s : Finset (Fin (1 + n)) // s.card = n} =>
        q.changeOriginSeriesTerm 1 n s.1 s.2
          (fun _ => x) (fun _ => verticalVector)) ?_).symm
    intro i
    rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
    rw [omittedIndexEquiv_apply_val, Finset.piecewise_erase_univ]
  rw [Nat.add_comm 1 n] at hnative
  exact hnative

omit [CompleteSpace F] in
private theorem primitiveSeries_deriv_coeff
    (p : FormalMultilinearSeries ℂ (V E) F) (n : ℕ) (x : V E) :
    (primitiveSeries p).derivSeries n (fun _ => x) verticalVector =
      p n (fun _ => x) := by
  rw [derivSeries_apply_vertical]
  change (∑ i : Fin (n + 1),
      primitiveCoeff n (p n) (Function.update (fun _ => x) i verticalVector)) = _
  exact primitiveCoeff_diag_derivative n (p n) x

private theorem primitiveSeries_deriv_sum
    (p : FormalMultilinearSeries ℂ (V E) F) (x : V E)
    (hqx : x ∈ Metric.eball (0 : V E) (primitiveSeries p).radius) :
    ((primitiveSeries p).derivSeries.sum x) verticalVector = p.sum x := by
  have hderivRadius : (primitiveSeries p).radius ≤
      (primitiveSeries p).derivSeries.radius :=
    FormalMultilinearSeries.radius_le_radius_derivSeries _
  have hqdx : x ∈ Metric.eball (0 : V E) (primitiveSeries p).derivSeries.radius :=
    lt_of_lt_of_le hqx hderivRadius
  have hsum : Summable (fun n : ℕ =>
      (primitiveSeries p).derivSeries n (fun _ => x)) :=
    (primitiveSeries p).derivSeries.summable hqdx
  change (ContinuousLinearMap.apply ℂ F verticalVector)
      ((primitiveSeries p).derivSeries.sum x) = p.sum x
  unfold FormalMultilinearSeries.sum
  rw [(ContinuousLinearMap.apply ℂ _ verticalVector).map_tsum hsum]
  apply tsum_congr
  intro n
  exact primitiveSeries_deriv_coeff p n x

omit [CompleteSpace F] in
private theorem primitiveCoeff_horizontal (n : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => V E) F) (g : E) :
    primitiveCoeff n p (fun _ => (g, 0)) = 0 := by
  classical
  unfold primitiveCoeff
  simp_rw [sum_apply, primitiveTerm_apply]
  simp

omit [CompleteSpace F] in
private theorem primitiveSeries_horizontal_sum
    (p : FormalMultilinearSeries ℂ (V E) F) (g : E) :
    (primitiveSeries p).sum (g, 0) = 0 := by
  unfold FormalMultilinearSeries.sum
  have hzero (n : ℕ) : primitiveSeries p n (fun _ => (g, 0)) = 0 := by
    cases n with
    | zero => rfl
    | succ n => exact primitiveCoeff_horizontal n (p n) g
  simp_rw [hzero]
  exact tsum_zero

/-- A jointly analytic Banach-valued germ has a jointly analytic primitive in
the distinguished complex coordinate.  The primitive is normalized to vanish
on the horizontal slice. -/
theorem analytic_vertical_primitive {A : E × ℂ → F}
    (hA : AnalyticAt ℂ A (0, 0)) :
    ∃ H : E × ℂ → F,
      AnalyticAt ℂ H (0, 0) ∧
      (∀ g : E, H (g, 0) = 0) ∧
      ∀ᶠ x : E × ℂ in 𝓝 (0, 0),
        (fderiv ℂ H x) (0, 1) = A x := by
  obtain ⟨p, r, hAp⟩ := hA
  let q := primitiveSeries p
  have hqpos : 0 < q.radius :=
    primitiveSeries_radius_pos p (lt_of_lt_of_le hAp.r_pos hAp.r_le)
  let H : E × ℂ → F := q.sum
  have hHa : AnalyticAt ℂ H (0, 0) := (q.hasFPowerSeriesOnBall hqpos).analyticAt
  refine ⟨H, hHa, ?_, ?_⟩
  · intro g
    exact primitiveSeries_horizontal_sum p g
  · have hpball : Metric.eball (0 : E × ℂ) r ∈ 𝓝 (0, 0) :=
      Metric.eball_mem_nhds _ hAp.r_pos
    have hqball : Metric.eball (0 : E × ℂ) q.radius ∈ 𝓝 (0, 0) :=
      Metric.eball_mem_nhds _ hqpos
    filter_upwards [hpball, hqball] with x hpx hqx
    have hpx' : x ∈ Metric.eball (0 : E × ℂ) p.radius :=
      lt_of_lt_of_le hpx hAp.r_le
    have hfd : fderiv ℂ H x = q.derivSeries.sum x := by
      exact FormalMultilinearSeries.fderiv_sum
        (p := q) (x := x) (by simpa [Metric.mem_eball, edist_eq_enorm_sub] using hqx)
    rw [hfd]
    change q.derivSeries.sum x verticalVector = A x
    rw [primitiveSeries_deriv_sum p x hqx]
    symm
    simpa only [show ((0 : E), (0 : ℂ)) = (0 : E × ℂ) by rfl, zero_add] using hAp.sum hpx

end PerronWright.AnalyticVerticalPrimitive
