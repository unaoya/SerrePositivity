module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapComponent
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleElements
public import SerrePositivity.DifferentialGraded.Bimodule.ValueActions

/-! # 相対tensorの値のmapと外側の左作用の可換式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMapComponent_leftAction_element {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q')
    (b : B) (c : C) (e e' : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : k + p = j) (hn : i + p = n) (u : GradedHom A e e' p)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X k)
    (v : ((BimoduleCategory.underlying A B C P).value b c).X r) :
    composeMapComponent A B C E f g b e' n
      (SerrePositivity.DifferentialGraded.leftAction A
        ((compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)).leftAt b) u
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b) c q v ha) hn) =
    SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).leftAt b) u
      (composeMapComponent A B C E f g b e i
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b) c q v ha)) hn := by
  have hS := compose_leftAction_element A B C E
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)
    b c e e' ha hj hn u q v
  have hC := composeMapComponent_element A B C E f g b c e q v ha
  have hM := composeMapComponent_element A B C E f g b c e' (r := j) (s := r) (n := n)
    (SerrePositivity.DifferentialGraded.leftAction A
      ((BimoduleCategory.underlying A C E Q).leftAt c) u q hj) v (by omega)
  have hQ := BimoduleCategory.valueMap_leftAction A C E g c e e' hj u q
  have hT := compose_leftAction_element A B C E
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q')
    b c e e' ha hj hn u
    (((BimoduleCategory.valueEvaluation A C E c e).map g).f k q)
    (((BimoduleCategory.valueEvaluation A B C b c).map f).f r v)
  have hR := hT.trans (congrArg (fun z :
      ((BimoduleCategory.underlying A C E Q').value c e').X j =>
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e')
      ((BimoduleCategory.underlying A B C P').leftAt b) c z
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f r v) (by omega)) hQ).symm
  exact element_square
    (composeMapComponent A B C E f g b e i) (composeMapComponent A B C E f g b e' n)
    (fun z => SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C E (BimoduleCategory.underlying A B C P)
        (BimoduleCategory.underlying A C E Q)).leftAt b) u z hn)
    (fun z => SerrePositivity.DifferentialGraded.leftAction A
      ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).leftAt b) u z hn)
    _ _ _ _ hS hC hM hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
