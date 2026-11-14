module
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchange

/-!
概要：複体値図式と図式圏の複体の指定交換を圏同値としてまとめる。
方針：構成済みの全関手と単位・余単位同型を使い、成分で三角則を確認する。
規約：対象・微分・射の全成分は元の指定値を使う。
使われ方：HA 1.2.4、G10 の延長・切断随伴の図式圏への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [HasZeroMorphisms C]
variable {ι : Type*} (c : ComplexShape ι)

/-- 元の指定成分交換を両方向の関手とする圏同値。 -/
def functorComplexExchangeEquivalence :
    (J ⥤ HomologicalComplex C c) ≌ HomologicalComplex (J ⥤ C) c where
  functor := functorToComplexOfFunctors J C c
  inverse := complexOfFunctorsToFunctorToComplex
  unitIso := functorComplexExchangeUnitIso J C c
  counitIso := functorComplexExchangeCounitIso J C c
  functor_unitIso_comp X := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply NatTrans.ext
    funext j
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

end SerrePositivity.HomologicalAlgebra
