import Mathlib.Probability.Independence.InfinitePi

/-!
# Exact transposition of actual independent product arrays

The row product law becomes the column product law under the literal
transpose map. This is proved by actual curry and reindexing pushforwards,
and yields independence of all column observables, without an interface.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.CountableProductTranspose

variable {I J E : Type*} [MeasurableSpace E]

theorem infinitePi_map_transpose (μ : I → J → Measure E)
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.infinitePi (fun i ↦ Measure.infinitePi (μ i))).map
      (fun x : I → J → E ↦ fun j i ↦ x i j) =
      Measure.infinitePi (fun j ↦ Measure.infinitePi (fun i ↦ μ i j)) := by
  let u : (I → J → E) → (I × J → E) := fun x p ↦ x p.1 p.2
  let v : (I × J → E) → (J × I → E) := fun x p ↦ x (p.2,p.1)
  let w : (J × I → E) → (J → I → E) := fun x j i ↦ x (j,i)
  have hu : (Measure.infinitePi (fun i ↦ Measure.infinitePi (μ i))).map u =
      Measure.infinitePi (fun p : I × J ↦ μ p.1 p.2) :=
    Measure.infinitePi_map_curry_symm μ
  have hv : (Measure.infinitePi (fun p : I × J ↦ μ p.1 p.2)).map v =
      Measure.infinitePi (fun p : J × I ↦ μ p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft (fun p : J × I ↦ μ p.2 p.1) (Equiv.prodComm I J)
  have hw : (Measure.infinitePi (fun p : J × I ↦ μ p.2 p.1)).map w =
      Measure.infinitePi (fun j ↦ Measure.infinitePi (fun i ↦ μ i j)) :=
    Measure.infinitePi_map_curry (fun j i ↦ μ i j)
  have hum : Measurable u := by fun_prop
  have hvm : Measurable v := by fun_prop
  have hwm : Measurable w := by fun_prop
  calc
    _ = (((Measure.infinitePi (fun i ↦ Measure.infinitePi (μ i))).map u).map v).map w := by
      rw [Measure.map_map hwm hvm,Measure.map_map (hwm.comp hvm) hum]
      rfl
    _ = _ := by rw [hu,hv,hw]

theorem columns_independent (μ : I → J → Measure E)
    [∀ i j, IsProbabilityMeasure (μ i j)] :
    iIndepFun (fun j (x : I → J → E) ↦ fun i ↦ x i j)
      (Measure.infinitePi (fun i ↦ Measure.infinitePi (μ i))) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).mpr
  rw [infinitePi_map_transpose]
  congr 1
  funext j
  have ht := infinitePi_map_transpose μ
  have hm : Measurable (fun x : I → J → E ↦ fun j i ↦ x i j) := by fun_prop
  have hev : Measurable (fun x : J → I → E ↦ x j) := measurable_pi_apply j
  rw [← Measure.infinitePi_map_eval (fun j ↦ Measure.infinitePi (fun i ↦ μ i j)) j,
    ← ht,Measure.map_map hev hm]
  rfl

end PerronWright.CountableProductTranspose
