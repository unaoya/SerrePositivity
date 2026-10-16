module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapComponent

/-! # 成分の指定した値を使うtensor mapの生成元評価 -/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMapComponent_element_of_values {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E)
    {r s n : ℤ} (m : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X s)
    (m' : ((BimoduleCategory.underlying A C E Q').value c e).X r)
    (v' : ((BimoduleCategory.underlying A B C P').value b c).X s)
    (hn : r + s = n)
    (hg : ((BimoduleCategory.valueEvaluation A C E c e).map g).f r m = m')
    (hf : ((BimoduleCategory.valueEvaluation A B C b c).map f).f s v = v') :
    composeMapComponent A B C E f g b e n
      (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
        ((BimoduleCategory.underlying A B C P).leftAt b) c m v hn) =
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c m' v' hn :=
  (composeMapComponent_element A B C E f g b c e m v hn).trans
    (congrArg₂ (fun x y => BalancedTensor.element A C
      ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c x y hn) hg hf)

end SerrePositivity.DifferentialGraded.BimoduleTensor
