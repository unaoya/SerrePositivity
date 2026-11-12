module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TwoSidedHomLeftEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.KanRightCompositionTransport

/-!
概要：元の Kan Hom の共通解像上の左右区間族を同じ標準頂点で比較する。
方針：F1 の実二側 Hom 円柱の同型を同じ端点表示変更で後合成する。
規約：元の共通 Hom と両射影を保持し、反転 Hom と元の Hom を同一視しない。
使われ方：反転精密化の作用と元の右 Hom の値比較を同じ区間輸送へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 同じ全共通解像上の左右 Hom 区間族は元の実二側円柱の指定同型で比較できる。 -/
def coherentKanTwoSidedIntervalIso (K L : KanObject.{u}) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (SimplicialCategory.sHom K L)) ≫
        coherentCosliceFiberComparison K L ≫
        cosliceFiberToIntervalMappingSpace (coherentNerveVertex K) (coherentNerveVertex L) ≫
        intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
          (coherentNerveVertex K) (coherentNerveVertex L)
          (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm)
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom K L)) ≫
        coherentKanRightHomInterval K L) := by
  let p := intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
    (coherentNerveVertex K) (coherentNerveVertex L)
    (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm
  exact (functorIsoOfSimplicialHomotopy
    (coherentTwoSidedHomIntervalHomotopy K L)).postcomp p

end SerrePositivity.InfinityCategories.F2
