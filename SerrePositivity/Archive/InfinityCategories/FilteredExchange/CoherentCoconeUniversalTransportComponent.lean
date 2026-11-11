module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCoconeIntervalTransportAction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPost

/-!
概要：全 Hom の普遍作用比較の成分は、元の普遍輸送成分の同じ像。
方針：指定関手同型の後合成と各点評価の整合を適用する。
規約：全族の指定成分を保持。使われ方：native 因子と a6 の指定正方形の共有成分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (c : JoinCocone F) (z : SpaceInfinity.{u} _⦋0⦌)

/-- 同じ全 Hom 成分は、元の普遍輸送成分を同じ fiber・値の作用で写したもの。 -/
lemma coherentCoconeUniversalTransportIso_app_heq (n : (pinchedHomLeft c.vertex z) _⦋0⦌) :
    HEq ((coherentCoconeUniversalTransportIso F c z).app n)
      (VertexIso.map ((pointedIntervalTransport_mapIso
        (pinchedHomLeftToIntervalMappingSpace c.vertex z)).app n)
          (coherentCoconeFiberValueAction F c z)) := by
  exact functorIso_app_postcomp_heq
    (pointedIntervalTransport_mapIso (pinchedHomLeftToIntervalMappingSpace c.vertex z))
    (coherentCoconeFiberValueAction F c z) n

end SerrePositivity.InfinityCategories.F2
