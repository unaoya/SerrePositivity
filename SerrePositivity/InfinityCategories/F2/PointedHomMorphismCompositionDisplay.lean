module

public import SerrePositivity.InfinityCategories.F2.PointedHomMorphismValueComparison
public import SerrePositivity.InfinityCategories.F2.OppositeKanPostcomposition

/-!
概要：元の二射の合成の固定比較を、元の二段の全反転 Hom 作用の間で表示する。
方針：同じ豊穣後合成の厳密な合成則で始点だけを表示変更する。
規約：元の二射と指定比較を保持。使われ方：二辺評価比較の固定射への統一。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K M L : KanObject.{u}} (f : K ⟶ M) (g : M ⟶ L)
local notation "C" => pointedCoherentFiberComparison K ≫
  eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (Eq.symm (spaceInfinityVertex_eq_coherent K)))
local notation "V" => eqToHom (congrArg (vertexFiber pointedSpaceProjection)
  (Eq.symm (spaceInfinityVertex_eq_coherent L))) ≫
    QCatEquivalence.hom (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))
local notation "P" => NatTrans.app (pre C)
  (CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj L))

/-- 合成の固定比較の始点を、元の同じ二段作用の値へ厳密に表示変更する。 -/
def pointedHomCompositeMorphismValueComparison :=
  vertexIsoOfEq (pointedHomMorphismValueComparison (f ≫ g))
    (congrArg functorVertex (congrArg
      (fun t => (t ≫ pointedCoherentFiberComparison L) ≫ V)
      (uliftOppositeKanPostcomposition_comp f g))) rfl

/-- 二段作用の表示で保持した同じ合成の固定評価比較。 -/
def pointedHomCompositeMorphismEvaluationComparison :=
  pointedHomCompositeMorphismValueComparison f g ≪≫
    (VertexIso.map (pointedValueHomActionAt (f ≫ g)) P).symm

end SerrePositivity.InfinityCategories.F2
