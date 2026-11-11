module

public import SerrePositivity.KST.Spectra.CofiberMappingFiberIso
public import SerrePositivity.KST.Spectra.LoopPathFiber

/-!
概要：cofiber からの写像空間の fiber 表示を点つき同型にする。
方針：底の基点と全空間の基点の像の一致で fiber を移し、包含射で基点を検査する。
規約：同型は Kan 性なしでも成立する。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の fiber の点つきホモトピー群。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：cofiber からの点つき Hom は制限の点つき fiber と同型。
方針：既存の基礎同型の後で fiber の基点を移し、fiber の包含の単射性を使う。
規約：右辺の pointedFiber は全空間の基点の像を底の基点にする模型。
使われ方：Goerss–Jardine I §7、VIII §1。fiber の群の計算への点つき比較。 -/
def pointedCofiberMappingFiberIso {X Y : PointedSimplicialSet.{u}} (i : X ⟶ Y)
    (Z : PointedSimplicialSet.{u}) :
    PointedObject.basedHom (pointedCofiber i) Z ≅
      pointedFiber (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z) := by
  let p := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z
  let e := cofiberMappingFiberIso i Z ≪≫
    fiberIsoOfEq p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p).symm
  refine Under.isoMk e ?_
  let : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right (p.right.app _
      (PointedSimplicialSet.basepoint (PointedObject.basedHom Y Z)))) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι]
    infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right (p.right.app _
    (PointedSimplicialSet.basepoint (PointedObject.basedHom Y Z))))).mp
  change (_ ≫ e.hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p.right _ =
    (pointedFiber p).hom ≫ (pointedFiberι p).right
  dsimp only [e, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, fiberIsoOfEq_hom_ι]
  erw [cofiberMappingFiberIso_hom_ι]
  exact (Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection i) Z)).trans
    (Under.w (pointedFiberι p)).symm

end

end SerrePositivity.KST.Spectra
