module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMapComponent
public import SerrePositivity.DifferentialGraded.Complexes.MapComponentFunctions

/-! # 相対tensorの値のmapを固定した成分関数で表示する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 値のmapを、固定した成分関数を持つchain mapとして再表示する。 -/
def composeValueHom {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    (compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).value b e ⟶
    (compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).value b e :=
  chainMapOfComponentFunctions (composeValueMap A B C E f g b e)
    (composeMapComponent A B C E f g b e) (composeMapComponent_eq A B C E f g b e)

@[simp]
lemma composeValueHom_apply {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) (n : ℤ) (x) :
    (composeValueHom A B C E f g b e).f n x =
      composeMapComponent A B C E f g b e n x := rfl

lemma composeValueHom_eq {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) :
    composeValueHom A B C E f g b e = composeValueMap A B C E f g b e :=
  chainMapOfComponentFunctions_eq _ _ _

end SerrePositivity.DifferentialGraded.BimoduleTensor
