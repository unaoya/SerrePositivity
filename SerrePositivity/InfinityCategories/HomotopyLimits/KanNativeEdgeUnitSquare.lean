module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeActionUnitSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeActionReflectsEdgeClass

/-!
概要：元の標準単位の正方形から、元の指定頂点辺と同じ全空間 Kan 辺の類を同定する。
方針：指定辺の全余錐作用の合成式を供給し、単位三角形の比較と余極限同値で反映する。
規約：指定辺・変換・全 Kan 像を保持し、底の quasicategory 性を要求しない。
使われ方：実際の前層余極限の共役された各脚を、標準評価 Kan 脚へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory

/-- 元の二つの標準単位との可換式を満たす指定頂点辺は、同じ Kan 辺と同じ類。 -/
lemma totalKanNativeEdge_homMk_of_unit_square {B : SSet.{u}}
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (e : SSet.Edge (F2.coherentDiagramTotalCocone F).vertex (F2.coherentDiagramTotalVertex G))
    (h : homMk (intervalMappingEdgeOfVertex t).toTruncated ≫
      homMk (intervalMappingEdgeOfVertex (coconeTransformationPointAt
        (F2.coherentDiagramTotalCocone G) (F2.coherentDiagramTotalCocone_vertex G))).toTruncated =
      homMk (intervalMappingEdgeOfVertex
        (F2.coconeTransformationVertex (F2.coherentDiagramTotalCocone F))).toTruncated ≫
          homMk (constantFunctorEdge (A := (SSet.uliftFunctor.{u + 1, u}).obj B) e.toTruncated)) :
    homMk (totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)).toTruncated =
      homMk e.toTruncated := by
  apply totalKanNativeEdge_homMk_of_coconeIso F G (coherentTransformationTotalKanMap F G t) e
  have H := kanNativeCoconeIsoOfNativeUnitHomClass F G t
    (coconeEdgeAction (F2.coherentDiagramTotalCocone F) e)
    (coconeEdgeAction_vertex (F2.coherentDiagramTotalCocone F) e)
    (h.trans (coconeEdgeAction_unit_square (F2.coherentDiagramTotalCocone F) e).symm)
  exact H

end SerrePositivity.InfinityCategories.HomotopyLimits
