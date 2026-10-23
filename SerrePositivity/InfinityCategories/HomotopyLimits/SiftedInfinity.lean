module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredBinaryDiagonal

/-!
概要：sifted な単体集合を非空性と二項対角の right cofinality で定義する。
方針：HTT 5.5.8.1 の二条件をそのまま保持し、filtered ∞ 圏からの入口を与える。
規約：sifted 性自体に quasicategory 性を要求しない。使われ方：P_Σ と有限積の交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- HTT 5.5.8.1 の sifted 単体集合。余極限に対する向きは right cofinal。 -/
class IsSiftedInfinity (K : SSet.{u}) : Prop where
  nonempty_vertices : Nonempty (K _⦋0⦌)
  diagonal_rightCofinal : IsRightCofinal (lift (𝟙 K) (𝟙 K))

/-- filtered ∞ 圏は sifted。元の二項対角の cofinality を使う。 -/
instance isSiftedInfinity_of_filtered (K : SSet.{u}) [Quasicategory K]
    [F2.IsFilteredInfinity K] : IsSiftedInfinity K where
  nonempty_vertices := F2.nonempty_vertices_of_isFilteredInfinity K
  diagonal_rightCofinal := F2.isRightCofinal_binaryDiagonal K

end SerrePositivity.InfinityCategories.HomotopyLimits
