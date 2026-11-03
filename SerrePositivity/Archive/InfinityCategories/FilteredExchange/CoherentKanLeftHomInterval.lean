module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanTwoSidedIntervalIso

/-!
概要：元の全反転 Kan Hom の左区間族を同じ標準頂点で保持する。
方針：既存の標準 coslice 比較と区間比較の両端だけを正規化する。
規約：元の全反転 Hom と実際の区間を保持する。
使われ方：共通解像上の二自然性正方形を同じ元の左右区間へ適用する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の全反転 Kan Hom を同じ元の標準頂点間の実左区間族へ写す。 -/
def coherentKanLeftHomInterval (K L : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op ⟶
      intervalMappingSpace (spaceInfinityVertex K) (spaceInfinityVertex L) :=
  coherentCosliceFiberComparison K L ≫
    cosliceFiberToIntervalMappingSpace (coherentNerveVertex K) (coherentNerveVertex L) ≫
      intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
        (coherentNerveVertex K) (coherentNerveVertex L)
        (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm

end SerrePositivity.InfinityCategories.F2
