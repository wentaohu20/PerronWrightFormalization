import PerronWright.Probability.BrownianFirstPassagePastFibers

/-! # Actual whole-path future independence at first-passage grid times

Each actual selected-time fiber depends only on the stopped past.
The genuine deterministic past/future product law can therefore be
restricted on that fiber. Summing the actual finite partition proves a
product law for the whole selected future and the time-tagged past.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFirstPassageGridStrongMarkov

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFiniteReflectionLaw
open BrownianFirstPassageGridReflection BrownianFirstPassageReflection
open BrownianFirstPassagePastFibers

theorem fixed_past_future_restrict_jointLaw (T : ℝ≥0) (A : Set Path)
    (hA : MeasurableSet A) :
    (pathLaw.restrict ((pastPath T) ⁻¹' A)).map (fun f ↦ (pastPath T f,futurePath T f)) =
      ((pastLaw T).restrict A).prod pathLaw := by
  have hr := Measure.restrict_map (μ := pathLaw)
    ((measurable_pastPath T).prodMk (measurable_futurePath T)) (hA.prod MeasurableSet.univ)
  rw [past_future_jointLaw,← Measure.restrict_prod_eq_prod_univ] at hr
  have he : (fun f ↦ (pastPath T f,futurePath T f)) ⁻¹' (A ×ˢ univ) =
      (pastPath T) ⁻¹' A := by ext f; simp
  rw [he] at hr
  exact hr.symm

theorem selected_restrict_jointLaw (level : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (m : ℕ) (i : Fin (m+1)) :
    (pathLaw.restrict {f | gridIndex level t m f = i}).map
      (fun f ↦ (selectedPast level t m f,selectedFuture level t m f)) =
      ((pathLaw.restrict {f | gridIndex level t m f = i}).map
        (selectedPast level t m)).prod pathLaw := by
  let A : Set Path := {f | gridIndex level t m f = i}
  have hA : MeasurableSet A := (measurable_gridIndex level t m) (measurableSet_singleton i)
  have hp : (pastPath (t i)) ⁻¹' A = A := by
    ext f
    exact gridIndex_pastPath_stable level t ht m i f
  have hj := fixed_past_future_restrict_jointLaw (t i) A hA
  rw [hp] at hj
  let tag : Path → ℝ≥0 × Path := fun g ↦ (t i,g)
  have htag : Measurable tag := measurable_const.prodMk measurable_id
  have hsp : selectedPast level t m =ᵐ[pathLaw.restrict A] tag ∘ pastPath (t i) := by
    filter_upwards [ae_restrict_mem hA] with f hf
    change (t (gridIndex level t m f),pastPath (t (gridIndex level t m f)) f) = _
    rw [show gridIndex level t m f = i from hf]
    rfl
  have hsf : selectedFuture level t m =ᵐ[pathLaw.restrict A] futurePath (t i) := by
    filter_upwards [ae_restrict_mem hA] with f hf
    change futurePath (t (gridIndex level t m f)) f = _
    rw [show gridIndex level t m f = i from hf]
  have hpast := Measure.restrict_map (μ := pathLaw) (measurable_pastPath (t i)) hA
  change (pastLaw (t i)).restrict A = _ at hpast
  rw [hp] at hpast
  change (pathLaw.restrict A).map _ = ((pathLaw.restrict A).map _).prod pathLaw
  rw [Measure.map_congr (hsp.prodMk hsf),Measure.map_congr hsp]
  rw [← Measure.map_map htag (measurable_pastPath (t i)),← hpast]
  have he := congrArg (Measure.map (Prod.map tag (id : Path → Path))) hj
  rw [Measure.map_map (htag.prodMap measurable_id)
    ((measurable_pastPath (t i)).prodMk (measurable_futurePath (t i))),
    ← Measure.map_prod_map _ _ htag measurable_id,Measure.map_id] at he
  exact he

theorem selected_jointLaw (level : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (m : ℕ) :
    pathLaw.map (fun f ↦ (selectedPast level t m f,selectedFuture level t m f)) =
      (pathLaw.map (selectedPast level t m)).prod pathLaw := by
  have hκ := measurable_gridIndex level t m
  have hj := (measurable_selectedPast level t m).prodMk (measurable_selectedFuture level t m)
  have hμ := law_eq_sum_fibers hκ
  calc
    _ = (Measure.sum (fun i : Fin (m+1) ↦
        pathLaw.restrict {f | gridIndex level t m f = i})).map
        (fun f ↦ (selectedPast level t m f,selectedFuture level t m f)) := by rw [← hμ]
    _ = Measure.sum (fun i : Fin (m+1) ↦
        ((pathLaw.restrict {f | gridIndex level t m f = i}).map
          (selectedPast level t m)).prod pathLaw) := by
      rw [Measure.map_sum hj.aemeasurable]
      congr 1
      funext i
      exact selected_restrict_jointLaw level t ht m i
    _ = (pathLaw.map (selectedPast level t m)).prod pathLaw := by
      rw [← Measure.prod_sum_left,← Measure.map_sum (measurable_selectedPast level t m).aemeasurable,
        ← hμ]

end PerronWright.BrownianFirstPassageGridStrongMarkov
