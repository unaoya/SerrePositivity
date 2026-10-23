module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexSharedNaturalityTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCorrectedCoherence
public import SerrePositivity.InfinityCategories.F1.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellOverHomRestrictionMap

/-!
概要：元の全 Hom 上で補正成分と元の大域自然性を合成し、共有頂点の両端を回収する。
方針：持ち上げた同じ補正 path と既存の大域自然性を使う。
規約：元の二成分・全 Hom・共有頂点を保持する。
使われ方：補正 pullback 比較と元の分類 Hom 作用の成分同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom 上で、最初の補正成分から元の分類作用の同じ辺への指定同型。 -/
def cocartesianTwoSimplexCorrectedFirstGlobalIso :
    FunctorIso
      (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q ≫
        (cocartesianTwoSimplexCorrectedFirstSquare k p q).map)
      (cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexFirstCell k)))
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  (cocartesianTwoSimplexCorrectedFirstSquare k p q).exactComponentIso.precomp
    (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q) ≪≫
      cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexFirstCell k) p q

/-- 元の全 Hom 上で、次の補正成分から元の分類作用の同じ辺への指定同型。 -/
def cocartesianTwoSimplexCorrectedSecondGlobalIso :
    FunctorIso
      (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q ≫
        (cocartesianTwoSimplexCorrectedSecondSquare k p q).map)
      (cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexSecondCell k)))
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)) :=
  (cocartesianTwoSimplexCorrectedSecondSquare k p q).exactComponentIso.precomp
    (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q) ≪≫
      cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSecondCell k) p q

end SerrePositivity.InfinityCategories
