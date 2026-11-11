module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentCoconeTransportAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoComponentNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoFiveFactorCancellation

/-!
概要：元の全 Hom の輸送作用比較の指定成分を、同じ Hom 上の任意の指定同型と交換する。
方針：元の全係数の関手同型そのものの自然性を適用する。
規約：元の余錐・全比較・指定同型を保持。使われ方：上側 native 因子の整合。
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

/-- 同じ全 Hom の指定同型の像は、元の輸送作用比較の同じ二成分と厳密に整合する。 -/
lemma coherentCoconeTransportActionIso_naturality {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌)
    {x y : (pinchedHomLeft c.vertex z) _⦋0⦌} (n : VertexIso x y) :
    VertexIso.map n ((coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) ≫
      (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv) ≪≫
        (coherentCoconeTransportActionIso F c z).app y =
      (coherentCoconeTransportActionIso F c z).app x ≪≫
        VertexIso.map n (coherentCoconeTransportAction F c z) := by
  exact functorIso_app_vertexIso_naturality (coherentCoconeTransportActionIso F c z) n

/-- 元の二成分を逆合成しても、同じ全 Hom 上の指定同型の輸送作用の像に等しい。 -/
lemma coherentCoconeTransportActionIso_conjugation {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌)
    {x y : (pinchedHomLeft c.vertex z) _⦋0⦌} (n : VertexIso x y) :
    ((coherentCoconeTransportActionIso F c z).app x).symm ≪≫
      VertexIso.map n ((coconePointHomFamily c z ≫ coherentCoconeTotalComparison F z) ≫
        (smallUnstraighteningHomIso F (spaceInfinityObject z).obj).inv) ≪≫
          (coherentCoconeTransportActionIso F c z).app y =
      VertexIso.map n (coherentCoconeTransportAction F c z) := by
  exact functorIso_app_vertexIso_conjugation (coherentCoconeTransportActionIso F c z) n

end SerrePositivity.InfinityCategories.F2
