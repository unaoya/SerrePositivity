module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapComponent
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements
public import SerrePositivity.DifferentialGraded.Bimodule.ValueActions

/-! # 相対tensorの値のmapと外側の右作用のKoszul可換式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMapComponent_rightAction_element {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q')
    (b b' : Bᵒᵖ) (c : C) (e : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : r + p = j) (hn : i + p = n) (u : GradedHom A b b' p)
    (q : ((BimoduleCategory.underlying A C E Q).value c e).X k)
    (v : ((BimoduleCategory.underlying A B C P).value b.unop c).X r) :
    composeMapComponent A B C E f g b'.unop e n
      (moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)).rightAt e) u
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b.unop) c q v ha) hn) =
    moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q')).rightAt e) u
      (composeMapComponent A B C E f g b.unop e i
        (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
          ((BimoduleCategory.underlying A B C P).leftAt b.unop) c q v ha)) hn := by
  let σ : ℤˣ := (p * k).negOnePow
  have hS := compose_rightAction_element A B C E
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)
    b b' c e ha hj hn u q v
  have hC := composeMapComponent_element A B C E f g b.unop c e q v ha
  have hM := composeMapComponent_element A B C E f g b'.unop c e
    (r := k) (s := j) (n := n) q
    (moduleAction A ((BimoduleCategory.underlying A B C P).rightAt c) u v hj) (by omega)
  have hσ := composeMapComponent_units_smul A B C E f g b'.unop e n σ
    (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
      ((BimoduleCategory.underlying A B C P).leftAt b'.unop) c q
      (moduleAction A ((BimoduleCategory.underlying A B C P).rightAt c) u v hj) (by omega))
  have hMσ := hσ.trans (congrArg (fun z => σ • z) hM)
  have hP := BimoduleCategory.valueMap_rightAction A B C f b b' c hj u v
  have hT := compose_rightAction_element A B C E
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q')
    b b' c e ha hj hn u
    (((BimoduleCategory.valueEvaluation A C E c e).map g).f k q)
    (((BimoduleCategory.valueEvaluation A B C b.unop c).map f).f r v)
  have hR := hT.trans (congrArg (fun z :
      ((BimoduleCategory.underlying A B C P').value b'.unop c).X j =>
    σ • BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b'.unop) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f k q) z (by omega)) hP).symm
  exact element_square
    (composeMapComponent A B C E f g b.unop e i)
    (composeMapComponent A B C E f g b'.unop e n)
    (fun z => moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e) u z hn)
    (fun z => moduleAction A ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e) u z hn)
    _ _ _ _ hS hC hMσ hR

end SerrePositivity.DifferentialGraded.BimoduleTensor
