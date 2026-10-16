module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueHom
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapLeftAction
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapRightAction
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # 相対tensorの値のmapの左右全Hom自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeValueHom_right_naturality {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b b' : Bᵒᵖ) (e : E) :
    ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).rightAt e).map b b' ≫
      homPostcompose _ (composeValueHom A B C E f g b'.unop e) =
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).rightAt e).map b b' ≫
      homPrecompose (composeValueHom A B C E f g b.unop e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A C
    ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((BimoduleCategory.underlying A B C P).leftAt b.unop)
  intro p u c k r i n ha hn q v
  exact composeMapComponent_rightAction_element A B C E f g b b' c e
    (j := r + p) ha rfl hn u q v

lemma composeValueHom_left_naturality {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e e' : E) :
    ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).leftAt b).map e e' ≫
      homPostcompose _ (composeValueHom A B C E f g b e') =
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).leftAt b).map e e' ≫
      homPrecompose (composeValueHom A B C E f g b e) _ := by
  apply BalancedTensor.homMap_post_pre_eq A C
    ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((BimoduleCategory.underlying A B C P).leftAt b)
  intro p u c k r i n ha hn q v
  exact composeMapComponent_leftAction_element A B C E f g b c e e'
    (j := k + p) ha rfl hn u q v

end SerrePositivity.DifferentialGraded.BimoduleTensor
