module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleValueElements
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation

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

/-- 外側の作用との比較で値のchain mapの構成を展開しないための成分表示。 -/
@[irreducible]
def composeMapComponent {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) (n : ℤ) :
    ((compose A B C E (BimoduleCategory.underlying A B C P)
      (BimoduleCategory.underlying A C E Q)).value b e).X n →
    ((compose A B C E (BimoduleCategory.underlying A B C P')
      (BimoduleCategory.underlying A C E Q')).value b e).X n :=
  fun x => (composeValueMap A B C E f g b e).f n x

lemma composeMapComponent_eq {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E) (n : ℤ) (x) :
    composeMapComponent A B C E f g b e n x = (composeValueMap A B C E f g b e).f n x := by
  unfold composeMapComponent
  rfl

lemma composeMapComponent_element {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (c : C) (e : E)
    {r s n : ℤ} (m : ((BimoduleCategory.underlying A C E Q).value c e).X r)
    (t : ((BimoduleCategory.underlying A B C P).value b c).X s) (hn : r + s = n) :
    composeMapComponent A B C E f g b e n
      (BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q).rightAt e)
        ((BimoduleCategory.underlying A B C P).leftAt b) c m t hn) =
    BalancedTensor.element A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt b) c
      (((BimoduleCategory.valueEvaluation A C E c e).map g).f r m)
      (((BimoduleCategory.valueEvaluation A B C b c).map f).f s t) hn :=
  (composeMapComponent_eq A B C E f g b e n _).trans
    (composeValueMap_element A B C E f g b c e m t hn)

lemma composeMapComponent_units_smul {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E} (f : P ⟶ P') (g : Q ⟶ Q') (b : B) (e : E)
    (n : ℤ) (u : ℤˣ) (x) :
    composeMapComponent A B C E f g b e n (u • x) =
      u • composeMapComponent A B C E f g b e n x :=
  (composeMapComponent_eq A B C E f g b e n (u • x)).trans
    ((chain_units_smul (composeValueMap A B C E f g b e) n u x).trans
      (congrArg (fun z => u • z) (composeMapComponent_eq A B C E f g b e n x).symm))

end SerrePositivity.DifferentialGraded.BimoduleTensor
