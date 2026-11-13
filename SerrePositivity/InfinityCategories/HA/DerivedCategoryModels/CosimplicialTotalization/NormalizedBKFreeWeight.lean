module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanSetCone
/-!
概要：元のBK係数重みを同じ二重反対圏の自由鎖図式へ移す。
方針：既存の集合的BK重みとの等式と指定生成元・Moore比較を使う。
規約：IS-W2 A12の係数重み照合の特殊化。正規化・係数・添字を保持する。
使われ方：HA 1.2.4、元のBK Homから指定正規化重み比較への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
/-- 元の正規化BK係数重みを順射を保って自由鎖図式へ送る指定同型。 -/
def normalizedBousfieldKanWeightFreeDiagramIso (A : Type u) [CommRing A] :
    (normalizedBousfieldKanWeight (A := A)).extend ComplexShape.embeddingDownNat ≅
      (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) (bousfieldKanSetWeight.flip ⋙ SSet.uliftFunctor.{u,0})) :=
  normalizedLinearWeightDiagramIso A bousfieldKanSetWeight.flip
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
