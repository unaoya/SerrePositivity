module

public import SerrePositivity.InfinityCategories.F1.CocartesianCellOverHomRestrictionMap
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexGlobalPullbackMaps

/-!
概要：元の分類図式の二辺への制限は、同じ共有頂点への直接制限に厳密に整合する。
方針：底上の制限写像の二脚を先に照合し、その合成則を使う。
規約：元の分類図式と元の制限写像を保持する。
使われ方：元の分類側の target Segal 射の構成。
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

/-- 元の分類図式の最初の辺への同じ制限。 -/
def cocartesianTwoSimplexTargetFirstRestriction :=
  intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexFirstCell k)))
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 元の分類図式の次の辺への同じ制限。 -/
def cocartesianTwoSimplexTargetSecondRestriction :=
  intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexSecondCell k)))
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 元の最初の辺の制限は、同じ共有頂点への直接制限に一致する。 -/
lemma cocartesianTwoSimplexTargetFirstRestriction_shared :
    cocartesianTwoSimplexTargetFirstRestriction k p q ≫
      (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl =
    intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexSharedCell k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  exact (congrArg (fun m ↦ cocartesianTwoSimplexTargetFirstRestriction k p q ≫ m)
    (cocartesianTwoSimplexLocalTarget_firstMap k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianTwoSimplexSharedToFirst k)))

/-- 元の次の辺の制限も、同じ共有頂点への直接制限に一致する。 -/
lemma cocartesianTwoSimplexTargetSecondRestriction_shared :
    cocartesianTwoSimplexTargetSecondRestriction k p q ≫
      (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr =
    intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexSharedCell k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  exact (congrArg (fun m ↦ cocartesianTwoSimplexTargetSecondRestriction k p q ≫ m)
    (cocartesianTwoSimplexLocalTarget_secondMap k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianTwoSimplexSharedToSecond k)))

end SerrePositivity.InfinityCategories
