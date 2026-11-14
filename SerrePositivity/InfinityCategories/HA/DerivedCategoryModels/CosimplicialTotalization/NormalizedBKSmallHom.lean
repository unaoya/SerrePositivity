module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKFreeWeight
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearHomSourceIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AsSmallLinearHom
/-!
概要：元の正規化BK Homを同じAsSmall添字の自由重みHomへ移す。
方針：指定係数重み同型の前合成と同じdown制限のHom同型を合成する。
規約：IS-W2 A12のΓ Hom照合の証明分割。元の二重反対圏の全射を保持する。
使われ方：HA 1.2.4、元のBK HomからA09の指定自由重み比較への入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]
/-- 元の二重反対圏のBK重みを同じdownで持ち上げる。 -/
def normalizedBKSmallWeight (_A : Type u) : AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ SSet.{u} :=
  AsSmall.down ⋙ bousfieldKanSetWeight.flip ⋙ SSet.uliftFunctor.{u,0}
/-- 元の全余単体図式を同じdownで持ち上げる。 -/
def normalizedBKSmallDiagram (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ) ⥤ Complex A :=
  AsSmall.down ⋙ doubleOppositeDiagram X
/-- 元の正規化BK Homから同じ持ち上げ自由重みHomへの指定同型。 -/
def normalizedBKSmallHomIso (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanHom X ≅
      linearHomComplex A
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (freeNegativeChainsDiagram (A := A) (normalizedBKSmallWeight A)))
        ((functorToComplexOfFunctors (AsSmall.{u} (SimplexCategoryᵒᵖᵒᵖ)) (ModuleCat A) (.up ℤ)).obj
          (normalizedBKSmallDiagram A X)) := by
  refine linearHomSourceIso A (normalizedBousfieldKanWeightFreeDiagramIso A)
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram X)) ≪≫ ?_
  exact asSmallLinearHomIso A (SimplexCategoryᵒᵖᵒᵖ)
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (bousfieldKanSetWeight.flip ⋙ SSet.uliftFunctor.{u,0})))
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj (doubleOppositeDiagram X))
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
