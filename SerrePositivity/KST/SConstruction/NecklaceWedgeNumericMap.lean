module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeNumericJoin
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeBooleanMap
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceNumericMap

/-! # 元の全 necklace 射の連結と数値 cube 作用
概要：元の全連結射の数値頂点作用が、左右の元の数値作用の連結に等しい。
方針：全 Bool 座標での連結保存と、元の右端座標の逆律を使う。
規約：元の joint 像も保持。使われ方：具体的 cube tensor の全射の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の全 necklace 射の数値作用は、元の左右の頂点の連結を厳密に保つ。 -/
lemma necklaceNumericMap_wedge_join {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.down.dimension) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.down.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) ((_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin T.down) U.down x y) =
      (_root_.SerrePositivity.KST.SConstruction.NecklaceShape.wedgeNumericJoin T'.down) U'.down (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f x) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap g y) := by
  funext j
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap, NecklaceShape.wedgeNumericJoin]
  simp only [Equiv.apply_symm_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_wedge_join]

end SerrePositivity.KST.SConstruction
