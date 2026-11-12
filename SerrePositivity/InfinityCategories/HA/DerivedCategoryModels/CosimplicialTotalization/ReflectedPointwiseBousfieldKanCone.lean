module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.PointwiseBousfieldKanSetCone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBousfieldKanSetCone

/-!
概要：元の BK 重みから反転した点ごとの Hom 空間への指定錐入力。
方針：反転重みの錐を点ごとに移し、再反転の指定同型で元の重みに戻す。
規約：全単体作用素と添字射を保持する。native 錐への比較は別工程。
使われ方：HA 1.2.4、G10 の反転 Hom による錐切断比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 反転重みの錐入力を各点の Dold–Kan Hom 空間へ移す。 -/
def reversedWeightPointwiseBousfieldKanCone (X : CosimplicialObject (Complex A)) :
    ((SimplicialObject.opFunctor.obj bousfieldKanSetWeight) ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (Type 0) (Type u)).obj
        uliftFunctor.{u,0}).flip ⟶ pointwiseBousfieldKanHomSpaces X :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖᵒᵖ (Type u)).map
    (reflectedBousfieldKanSetCone X) ≫
    Functor.whiskerRight
      ((pointwiseTruncationGammaIso SimplexCategoryᵒᵖᵒᵖ (ModuleCat.{u} A)).hom.app
        (bousfieldKanConeHomDiagram X))
      ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat.{u} A) (Type u)).obj
        (forget (ModuleCat.{u} A)))

/-- 元の BK 重みから反転 Hom 図式へ向かう指定自然変換。 -/
def reflectedPointwiseBousfieldKanCone (X : CosimplicialObject (Complex A)) :
    (bousfieldKanSetWeight ⋙
      (Functor.whiskeringRight SimplexCategoryᵒᵖᵒᵖ (Type 0) (Type u)).obj
        uliftFunctor.{u,0}).flip ⟶
      pointwiseBousfieldKanHomSpaces X ⋙ SimplicialObject.opFunctor :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ SimplicialObject.opFunctorCompOpFunctorIso.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (reversedWeightPointwiseBousfieldKanCone X)
      SimplicialObject.opFunctor

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
