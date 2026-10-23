module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedValueHomAction

/-!
概要：全区間写像空間を、同じ pointed fiber の輸送と指定された終点値で読む。
方針：右 Hom の係数を入れる前の輸送作用を保持する。
規約：始点 fiber と終点値の選択は既存のもの。使われ方：左右区間比較の値の像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ普遍区間輸送を指定された終点値で読む全係数作用。 -/
def pointedIntervalValueAction (K L : KanObject.{u}) :
    intervalMappingSpace (spaceInfinityVertex K) (spaceInfinityVertex L) ⟶
      (ihom (vertexFiber pointedSpaceProjection (spaceInfinityVertex K))).obj
        ((SSet.uliftFunctor.{u + 1, u}).obj L.obj) :=
  parametrizedFiberTransport pointedSpaceProjection (spaceInfinityVertex K)
    (spaceInfinityVertex L) ≫
      (ihom (vertexFiber pointedSpaceProjection (spaceInfinityVertex K))).map
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom

end SerrePositivity.InfinityCategories.F2
