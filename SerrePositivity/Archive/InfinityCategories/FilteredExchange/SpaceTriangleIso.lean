module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceTriangleHomotopy

/-!
概要：𝒮 の元の二単体を Kan 射間の指定関手同型として読む。
方針：元の精密化の辺のホモトピー類を使い、Kan 性で可逆性を得る。
規約：代表を選び直さない。使われ方：全錐円柱の三つの四面体の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：長辺から二辺の合成への指定ホモトピー類の同型。
方針：元の辺の類の可逆性。規約：元の三角形。使われ方：四面の合成則。 -/
def spaceInfinityTriangleIso (s : SpaceInfinity.{u} _⦋2⦌) :
    FunctorIso (coherentEdgeHom (SpaceInfinity.δ 1 s))
      (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s)) := by
  have : IsInvertibleEdge (spaceInfinityTriangleEdge s).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTriangleEdge s).toTruncated)

/-- 概要：指定同型の順方向の射は元の精密化の辺の類。
方針：asIso の定義。規約：代表を変更しない。使われ方：元の四面の比較。 -/
lemma spaceInfinityTriangleIso_hom (s : SpaceInfinity.{u} _⦋2⦌) :
    (spaceInfinityTriangleIso s).hom =
      SSet.Truncated.HomotopyCategory.homMk (spaceInfinityTriangleEdge s).toTruncated := rfl

/-- 概要：指定同型の順方向の射は元の指定円柱のホモトピー類。
方針：円柱と辺の往復。規約：同じ代表。使われ方：実際の path との整合。 -/
lemma spaceInfinityTriangleIso_homotopy (s : SpaceInfinity.{u} _⦋2⦌) :
    (spaceInfinityTriangleIso s).hom = SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (spaceInfinityTriangleHomotopy s)) := by
  rw [spaceInfinityTriangleHomotopy_edge, spaceInfinityTriangleIso_hom]

end SerrePositivity.InfinityCategories.F2
