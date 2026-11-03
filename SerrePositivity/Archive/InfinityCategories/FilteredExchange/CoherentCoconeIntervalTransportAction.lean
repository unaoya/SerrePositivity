module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCoconeTransportActionNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportUniversal

/-!
概要：元の全 Hom 比較を、同じ区間写像空間上の普遍輸送作用へ比較する。
方針：元の全 Hom 比較と全族の普遍輸送比較を合成する。
規約：全パラメータと指定成分を保持。使われ方：完成済み比較の同じ像での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌)

/-- 元の余錐 fiber 写像による前合成と、同じ標的の値への後合成の全作用。 -/
def coherentCoconeFiberValueAction :=
  (pre (coconeFiberMap c)).app (vertexFiber pointedSpaceProjection z) ≫
    (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom

/-- 元の区間写像空間の普遍輸送を、同じ余錐 fiber 写像と値へ写す全作用。 -/
def coherentCoconeIntervalTransportAction : intervalMappingSpace c.vertex z ⟶
    (ihom (leftUnstraightening F)).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj) :=
  parametrizedFiberTransport pointedSpaceProjection c.vertex z ≫
    coherentCoconeFiberValueAction F c z

/-- 元の全 Hom の作用と、同じ全区間族の普遍輸送作用を結ぶ指定比較。 -/
def coherentCoconeUniversalTransportIso : FunctorIso (coherentCoconeTransportAction F c z)
    (pinchedHomLeftToIntervalMappingSpace c.vertex z ≫
      coherentCoconeIntervalTransportAction F c z) := by
  have e := (pointedIntervalTransport_mapIso
    (pinchedHomLeftToIntervalMappingSpace c.vertex z)).postcomp
      (coherentCoconeFiberValueAction F c z)
  simpa only [coherentCoconeTransportAction, coherentCoconeIntervalTransportAction,
    coherentCoconeFiberValueAction, Category.assoc] using e

/-- 元の全 Hom 比較と同じ区間族の普遍作用を結ぶ、元の二比較の合成。 -/
def coherentCoconeIntervalTransportActionIso : FunctorIso
    ((coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv)
    (pinchedHomLeftToIntervalMappingSpace c.vertex z ≫
      coherentCoconeIntervalTransportAction F c z) :=
  coherentCoconeTransportActionIso F c z ≪≫ coherentCoconeUniversalTransportIso F c z

/-- 同じ全 Hom 上の指定同型の像は、普遍作用の元の両端成分と可換になる。 -/
lemma coherentCoconeIntervalTransportActionIso_naturality
    {x y : (pinchedHomLeft c.vertex z) _⦋0⦌} (n : VertexIso x y) :
    VertexIso.map n ((coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv) ≪≫
        (coherentCoconeIntervalTransportActionIso F c z).app y =
      (coherentCoconeIntervalTransportActionIso F c z).app x ≪≫
        VertexIso.map n (pinchedHomLeftToIntervalMappingSpace c.vertex z ≫
          coherentCoconeIntervalTransportAction F c z) := by
  exact functorIso_app_vertexIso_naturality (coherentCoconeIntervalTransportActionIso F c z) n

end SerrePositivity.InfinityCategories.F2
