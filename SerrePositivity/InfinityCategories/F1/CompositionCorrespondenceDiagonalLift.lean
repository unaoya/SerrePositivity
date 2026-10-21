module

public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceCurry
public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceDiagonalLiftFaces

/-!
概要：指定対角と終域辺を持つ元の三角形を、同じ合成三角形空間へ持ち上げる。
方針：第一辺を固定端点 Hom へ戻し、元の三角形のまま pullback に入れる。
規約：元の三角形と指定対角を厳密に回収する。
使われ方：合成三角形の対角評価の外ホーン pullback の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ (ihom (Δ[2] : SSet.{u})).obj X) (b : T ⟶ intervalMappingSpace x z)
variable (h : a ≫ (pre (horn 2 2).ι).app X = b ≫ cospanHomHornMap x g)

/-- 同じ指定外ホーンの延長の第一辺を、元の固定端点の Hom へ戻す。 -/
def compositionCorrespondenceDiagonalLiftFirst : T ⟶ intervalMappingSpace x y :=
  intervalMappingCurryOfVertexFaces ((stdSimplex.δ (2 : Fin 3) ▷ T) ≫ uncurry a)
    (compositionCorrespondenceDiagonalLift_first_source x g a b h)
    (compositionCorrespondenceDiagonalLift_first_target x g a b h)

/-- 回収した第一辺を展開すると、元の三角形の第一辺そのもの。 -/
lemma compositionCorrespondenceDiagonalLiftFirst_uncurry :
    intervalMappingUncurry (compositionCorrespondenceDiagonalLiftFirst x g a b h) =
      (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ uncurry a := by
  unfold compositionCorrespondenceDiagonalLiftFirst
  rw [intervalMappingCurryOfVertexFaces_uncurry]

/-- 同じ指定外ホーンの延長を、元の三角形のまま合成三角形空間へ持ち上げる。 -/
def compositionCorrespondenceDiagonalLift : T ⟶ compositionCorrespondence x g :=
  compositionCorrespondenceCurry x g (compositionCorrespondenceDiagonalLiftFirst x g a b h)
    (uncurry a) (compositionCorrespondenceDiagonalLiftFirst_uncurry x g a b h).symm
    (compositionCorrespondenceDiagonalLift_target x g a b h)

/-- 同じ持ち上げの三角形への射は、元の三角形の射そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_triangle :
    compositionCorrespondenceDiagonalLift x g a b h ≫
        pullback.fst ((pre (horn 2 1).ι).app X) (composableHomHornMap x g) = a := by
  unfold compositionCorrespondenceDiagonalLift
  rw [compositionCorrespondenceCurry_triangle, curry_uncurry]

/-- 同じ持ち上げの三角形を評価すると、元の全パラメーターの三角形そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_evaluation :
    (Δ[2] ◁ compositionCorrespondenceDiagonalLift x g a b h) ≫
        compositionCorrespondenceEvaluation x g = uncurry a := by
  unfold compositionCorrespondenceEvaluation
  rw [← uncurry_natural_left, compositionCorrespondenceDiagonalLift_triangle]

/-- 同じ持ち上げの対角は、元の指定対角の族そのもの。 -/
lemma compositionCorrespondenceDiagonalLift_diagonalMap :
    compositionCorrespondenceDiagonalLift x g a b h ≫ compositionCorrespondenceDiagonal x g = b := by
  apply intervalMappingUncurry_injective x z
  rw [intervalMappingUncurry_precomp, compositionCorrespondenceDiagonal_uncurry,
    ← Category.assoc, whisker_exchange, Category.assoc,
    compositionCorrespondenceDiagonalLift_evaluation,
    compositionCorrespondenceDiagonalLift_diagonal x g a b h]

end SerrePositivity.InfinityCategories
