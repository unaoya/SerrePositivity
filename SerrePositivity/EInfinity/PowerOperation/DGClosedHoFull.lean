module

public import SerrePositivity.EInfinity.PowerOperation.DGClosedHoComparison
public import Mathlib.CategoryTheory.EssentialImage

/-!
# 閉零圏から native dg nerve のホモトピー圏への充満・本質的全射性

DAG XIII §2.2 の π/H 自然同型の降下の補助。同じ H⁰ 商と証明済みの同値で検出する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma dgClosedHoFunctor_full : (dgClosedHoFunctor A D).Full := by
  let Q := dgClosedHoFunctor A D
  let e := dgNativeHoH0Equivalence A D
  have : (Q ⋙ e.functor).Full := by
    change (dgClosedHoFunctor A D ⋙ (dgNativeHoH0Equivalence A D).functor).Full
    rw [dgClosedHoFunctor_comp_H0]
    infer_instance
  constructor
  intro X Y φ
  obtain ⟨f, hf⟩ := (Q ⋙ e.functor).map_surjective (e.functor.map φ)
  exact ⟨f, e.functor.map_injective hf⟩

lemma dgClosedHoFunctor_essSurj : (dgClosedHoFunctor A D).EssSurj := by
  let Q := dgClosedHoFunctor A D
  let e := dgNativeHoH0Equivalence A D
  have : (Q ⋙ e.functor).EssSurj := by
    change (dgClosedHoFunctor A D ⋙ (dgNativeHoH0Equivalence A D).functor).EssSurj
    rw [dgClosedHoFunctor_comp_H0]
    infer_instance
  exact Functor.essSurj_of_comp_fully_faithful Q e.functor

end SerrePositivity.EInfinity.PowerOperation
