module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldCellOverHomRestrictionMap
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldGlobalPullbackMaps

/-!
概要：元の分類図式の最初の辺と尾部への制限は、同じ共有頂点への直接制限に厳密に整合する。
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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の分類図式の最初の辺への同じ制限。 -/
def cocartesianScaffoldTargetFirstRestriction :=
  intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldFirstCell n k)))
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 元の分類図式の次の辺への同じ制限。 -/
def cocartesianScaffoldTargetSecondRestriction :=
  intervalDiagramRestriction
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldTailCell n k)))
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 元の最初の辺の制限は、同じ共有頂点への直接制限に一致する。 -/
lemma cocartesianScaffoldTargetFirstRestriction_shared :
    cocartesianScaffoldTargetFirstRestriction n k p q ≫
      (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl =
    intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldSharedCell n k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  exact (congrArg (fun m ↦ cocartesianScaffoldTargetFirstRestriction n k p q ≫ m)
    (cocartesianScaffoldLocalTarget_firstMap n k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianScaffoldSharedToFirst n k)))

/-- 元の次の辺の制限も、同じ共有頂点への直接制限に一致する。 -/
lemma cocartesianScaffoldTargetSecondRestriction_shared :
    cocartesianScaffoldTargetSecondRestriction n k p q ≫
      (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr =
    intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldSharedCell n k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  exact (congrArg (fun m ↦ cocartesianScaffoldTargetSecondRestriction n k p q ≫ m)
    (cocartesianScaffoldLocalTarget_secondMap n k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianScaffoldSharedToTail n k)))

end SerrePositivity.InfinityCategories
