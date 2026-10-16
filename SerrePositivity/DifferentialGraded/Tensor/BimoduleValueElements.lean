module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueMaps
public import SerrePositivity.DifferentialGraded.Tensor.Elements

/-! # bimodule射による相対tensorの斉次生成元の評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 閉零bimodule射の作用には純tensor上で追加のKoszul符号が生じない。 -/
lemma composeValueMap_element {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E) {r s n : ℤ}
    (m : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (t : ((BimoduleCategory.underlying A B C P).value b c).X s) (hn : r + s = n) :
    (composeValueMap A B C E f g b e).f n
      (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
        ((BimoduleCategory.underlying A B C P).leftAt b) c m t hn) =
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r m)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s t) hn := by
  have h := BalancedTensor.map_element A C
    (M := (BimoduleCategory.evaluation A C E e).obj Q)
    (M' := (BimoduleCategory.evaluation A C E e).obj Q')
    (N := (BimoduleCategory.leftEvaluation A B C b).obj P)
    (N' := (BimoduleCategory.leftEvaluation A B C b).obj P')
    ((BimoduleCategory.evaluation A C E e).map g)
    ((BimoduleCategory.leftEvaluation A B C b).map f) c m t hn
  have he := congrArg (fun k : (BimoduleCategory.underlying A B C P).value b c ⟶
      (BimoduleCategory.underlying A B C P').value b c => k.f s t)
    (BimoduleCategory.leftEvaluation_map_eval A B C f b c)
  exact h.trans (congrArg (fun v : ((BimoduleCategory.underlying A B C P').value b c).X s =>
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r m) v hn) he)

end SerrePositivity.DifferentialGraded.BimoduleTensor
