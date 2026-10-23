module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeCoordinates
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle

/-!
概要：二重余錐の折り畳みは、最初と最後の因子を保持する。
方針：既存の結合同型の中央因子除去を用い、二つの右点を潰す。
規約：全次数の射の等式。使われ方：元の全余錐の標準 slice 持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 折り畳みは、最初の底と最後の余錐点からなる同じ全余錐を保つ。 -/
lemma arrowInterpolationConeFold_outerPair (A : SSet.{u}) :
    joinMap (joinInl A (Δ[0] : SSet.{u})) (𝟙 Δ[0]) ≫ arrowInterpolationConeFold A =
      𝟙 (join A Δ[0]) := by
  rw [arrowInterpolationConeFold, ← Category.assoc, stableJoinAssociator_middle,
    ← joinMap_comp, Category.id_comp]
  have he : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ stableLastJoinEvaluation 0 = 𝟙 Δ[0] :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [he, joinMap_id]

end SerrePositivity.InfinityCategories.F2.Ind
