module

public import SerrePositivity.InfinityCategories.F2.CoherentKanTwoSidedIntervalIso
public import SerrePositivity.InfinityCategories.F2.HomotopyIsoWhiskering

/-!
概要：元の標準頂点上の二側区間比較を、同じ実補間ホモトピーとして保持する。
方針：F1 の同じ実二側円柱に、同じ端点表示の移送を後合成する。
規約：指定同型と実円柱の一致を保持。使われ方：固定射での比較の類の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ標準頂点上で左右区間を結ぶ元の実二側円柱。 -/
def coherentKanTwoSidedIntervalHomotopy (K L : KanObject.{u}) :=
  functorHomotopyPostcomp (coherentTwoSidedHomIntervalHomotopy K L)
    (intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
      (coherentNerveVertex K) (coherentNerveVertex L)
      (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm)

/-- 既存の指定二側比較は、同じ実円柱の類の同型そのものである。 -/
lemma coherentKanTwoSidedIntervalIso_eq_homotopy (K L : KanObject.{u}) :
    coherentKanTwoSidedIntervalIso K L =
      functorIsoOfSimplicialHomotopy (coherentKanTwoSidedIntervalHomotopy K L) := by
  rw [coherentKanTwoSidedIntervalHomotopy, homotopyIso_postcomp]
  rfl

end SerrePositivity.InfinityCategories.F2
