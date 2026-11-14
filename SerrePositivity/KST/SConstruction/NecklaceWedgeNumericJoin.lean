module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeCoordinates
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeBooleanJoin
public import SerrePositivity.KST.SConstruction.CubeVertexBlockCoordinates

/-! # 元の necklace の数値 cube 頂点の連結
概要：元の非 joint Bool 座標の連結が、元の数値 cubeVertexJoin と一致すると示す。
方針：全左右数値座標の厳密な回収式と被覆を使う。
規約：次元移送でも元の番号を保つ。使われ方：具体的 cube tensor の比較。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction.NecklaceShape

/-- 元の非 joint 頂点で貼った Bool 関数を、元の右端数値座標で読む。 -/
def wedgeNumericJoin (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.dimension)
    (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.dimension) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (T.wedge U).dimension :=
  fun i => T.wedgeBooleanJoin U (fun v => x (T.nonjointCoordinate.symm v))
    (fun v => y (U.nonjointCoordinate.symm v)) ((T.wedge U).nonjointCoordinate i)

/-- 元の連結の左数値座標で、元の左の入力を回収する。 -/
lemma wedgeNumericJoin_left (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.dimension)
    (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.dimension) (i : Fin T.dimension) :
    (_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin T) U x y (T.wedgeCoordinateLeft U i) = x i := by
  rw [wedgeNumericJoin, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.nonjointCoordinate_wedge_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeBooleanJoin_left]
  exact congrArg x (T.nonjointCoordinate.symm_apply_apply i)

/-- 元の連結の右数値座標で、元の右の入力を回収する。 -/
lemma wedgeNumericJoin_right (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.dimension)
    (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.dimension) (i : Fin U.dimension) :
    (_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin T) U x y (T.wedgeCoordinateRight U i) = y i := by
  rw [wedgeNumericJoin, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.nonjointCoordinate_wedge_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.wedgeBooleanJoin_right]
  exact congrArg y (U.nonjointCoordinate.symm_apply_apply i)

/-- 元の全数値頂点で、necklace の連結は元の cubeVertexJoin の次元移送と一致する。 -/
lemma wedgeNumericJoin_cubeVertexJoin (T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.dimension)
    (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.dimension) :
    (_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin T) U x y =
      fun i => cubeVertexJoin x y (Fin.cast (T.wedge_dimension U) i) := by
  funext j
  rcases T.wedgeCoordinate_cases U j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [wedgeNumericJoin_left]
    exact (cubeVertexJoin_left_coordinate x y i).symm
  · rw [wedgeNumericJoin_right]
    exact (cubeVertexJoin_right_coordinate x y i).symm

end SerrePositivity.KST.SConstruction.NecklaceShape
