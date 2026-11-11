module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceCurry
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonalLiftFaces

/-!
概要：指定対角と終域辺を持つ元の三角形を、同じ合成三角形空間へ持ち上げる。
方針：第一辺を固定端点 Hom へ戻し、元の三角形のまま pullback に入れる。
規約：元の三角形と指定対角を厳密に回収する。
使われ方：合成三角形の対角評価の外ホーン pullback の普遍性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ (ihom (Δ[2] : SSet.{u})).obj X) (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x z)
variable (h : a ≫ (pre (horn 2 2).ι).app X = b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap x g)

/-- 同じ指定外ホーンの延長の第一辺を、元の固定端点の Hom へ戻す。 -/
def compositionCorrespondenceDiagonalLiftFirst : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfVertexFaces ((stdSimplex.δ (2 : Fin 3) ▷ T) ≫ uncurry a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift_first_source x g a b h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift_first_target x g a b h)

/-- 回収した第一辺を展開すると、元の三角形の第一辺そのもの。 -/
lemma compositionCorrespondenceDiagonalLiftFirst_uncurry :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (compositionCorrespondenceDiagonalLiftFirst x g a b h) =
      (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ uncurry a := by
  unfold compositionCorrespondenceDiagonalLiftFirst
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfVertexFaces_uncurry]

/-- 同じ指定外ホーンの延長を、元の三角形のまま合成三角形空間へ持ち上げる。 -/
def compositionCorrespondenceDiagonalLift : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceCurry x g (compositionCorrespondenceDiagonalLiftFirst x g a b h)
    (uncurry a) (compositionCorrespondenceDiagonalLiftFirst_uncurry x g a b h).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift_target x g a b h)

/-- 同じ持ち上げの三角形への射は、元の三角形の射そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_triangle :
    compositionCorrespondenceDiagonalLift x g a b h ≫
        pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) = a := by
  unfold compositionCorrespondenceDiagonalLift
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceCurry_triangle, curry_uncurry]

/-- 同じ持ち上げの三角形を評価すると、元の全パラメーターの三角形そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_evaluation :
    (Δ[2] ◁ compositionCorrespondenceDiagonalLift x g a b h) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g = uncurry a := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation
  rw [← uncurry_natural_left, compositionCorrespondenceDiagonalLift_triangle]

/-- 同じ持ち上げの対角は、元の指定対角の族そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_diagonalMap :
    compositionCorrespondenceDiagonalLift x g a b h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective x z
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry,
    ← Category.assoc, whisker_exchange, Category.assoc,
    compositionCorrespondenceDiagonalLift_evaluation,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonalLift_diagonal x g a b h]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
