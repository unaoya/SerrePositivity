module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportFamily
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedComparisonArrowValue
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityDiagram

/-!
概要：全局所 Hom の同型比較を元の二重底変換に固定すると、既存の結合図式全体となる。
方針：比較の全成分を既存の結合自然変換と照合し、同じ実現の頂点を回収する。
規約：底全体の元の図式を保持する。
使われ方：全局所比較の区間族と既存の結合辺の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p : CocartesianFibrationCategory (nerve C))

/-- 全局所比較を元の fibration に固定した自然変換は、既存の結合自然変換。 -/
lemma cocartesianIsoTransportComparison_native_transformation :
    quasicategoryDiagramQCatTransformation
      (F := ((cocartesianStrictTransportEnrichedDiagram A).precompose
        (isoTransportSourceEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))).toCoreEnrichedFunctor.obj
          (cocartesianBaseChangeIsoTransportObject l k p))
      (G := ((cocartesianStrictTransportEnrichedDiagram A).precompose
        (isoTransportTargetEnriched SSet.{u} (CocartesianFibrationObject (nerve A)))).toCoreEnrichedFunctor.obj
          (cocartesianBaseChangeIsoTransportObject l k p))
      (Functor.whiskerRight ((cocartesianIsoTransportDiagramComparison A).evaluate
        (cocartesianBaseChangeIsoTransportObject l k p)) quasicategoryObjectForget) =
    cocartesianBaseChangeAssociativityQCat p.val.hom l k := by
  ext a
  exact cocartesianIsoTransportDiagramComparison_native_component l k p a

/-- 同じ全局所比較の族の元の fibration での値は、既存の結合図式全体の頂点。 -/
lemma cocartesianIsoTransportFamily_native_vertex :
    (cocartesianIsoTransportFamily A).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (show CocartesianIsoTransportCategory A from
        cocartesianBaseChangeIsoTransportObject l k p)) =
    functorVertex (qCatDiagramCoherentNerve
      (qCatDiagramArrow (cocartesianBaseChangeAssociativityQCat p.val.hom l k))) := by
  exact ((cocartesianIsoTransportDiagramComparison A).realization_vertex
    (cocartesianBaseChangeIsoTransportObject l k p)).trans
    (congrArg (fun η ↦ functorVertex (qCatDiagramCoherentNerve (qCatDiagramArrow η)))
      (cocartesianIsoTransportComparison_native_transformation l k p))

end SerrePositivity.InfinityCategories
