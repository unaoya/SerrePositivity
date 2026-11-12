module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace

/-!
概要：内部 Hom の宇宙同型の逆は、元の射による前後合成と厳密に可換する。
方針：全パラメータで持ち上げと評価の往復を直接計算する。
規約：充填性は不要。使われ方：指定関手同型の宇宙下降と前後合成の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 宇宙同型の逆は元の射の後合成と全単体で可換する。 -/
lemma uliftFunctorSpaceInv_post {A X Y : SSet.{u}} (q : X ⟶ Y) :
    (uliftFunctorSpaceIso.{u, v} A X).inv ≫
      (SSet.uliftFunctor.{v, u}).map ((ihom A).map q) =
    (ihom ((SSet.uliftFunctor.{v, u}).obj A)).map ((SSet.uliftFunctor.{v, u}).map q) ≫
      (uliftFunctorSpaceIso.{u, v} A Y).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 宇宙同型の逆は元の射の前合成と全単体で可換する。 -/
lemma uliftFunctorSpaceInv_pre {A X Y : SSet.{u}} (q : A ⟶ X) :
    (uliftFunctorSpaceIso.{u, v} X Y).inv ≫
      (SSet.uliftFunctor.{v, u}).map ((pre q).app Y) =
    (pre ((SSet.uliftFunctor.{v, u}).map q)).app ((SSet.uliftFunctor.{v, u}).obj Y) ≫
      (uliftFunctorSpaceIso.{u, v} A Y).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply ULift.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

end SerrePositivity.InfinityCategories.F2
