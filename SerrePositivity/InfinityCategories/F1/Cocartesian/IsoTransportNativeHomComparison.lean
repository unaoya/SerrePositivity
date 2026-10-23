module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativePath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomComparison
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostcompositionVertices

/-!
概要：元の二重引き戻し間の全 Hom の core を、既存の結合比較の同じ Hom 空間へ写す。
方針：全局所比較の coherent な Hom 作用を使い、端点を既存の path 頂点へ正規化する。
規約：大域 Hom の底変換像への制限を置かず、元の全局所 Hom を使う。
使われ方：結合共役と既存の結合 Hom 輸送の関手同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二重引き戻し間の全 Hom の core に対する、既存の結合比較空間への作用。 -/
def cocartesianIsoTransportNativeHomComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ⟶
    cocartesianBaseChangeAssociativityHomComparisonSpace l k p q :=
  coherentHomIntervalComparison
    (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k p)
    (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k q) ≫
  intervalMappingPostOfEq (cocartesianIsoTransportHomPath A)
    (coherentNerveVertex (show CocartesianIsoTransportCategory A from
      cocartesianBaseChangeIsoTransportObject l k p))
    (coherentNerveVertex (show CocartesianIsoTransportCategory A from
      cocartesianBaseChangeIsoTransportObject l k q))
    (cocartesianIsoTransportHomPath_native_vertex l k p)
    (cocartesianIsoTransportHomPath_native_vertex l k q)

end SerrePositivity.InfinityCategories
