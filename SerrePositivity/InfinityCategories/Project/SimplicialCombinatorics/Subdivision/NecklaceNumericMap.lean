module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceNonjointCoordinates
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceBooleanMap

/-! # 元の necklace 写像の右端からの数値 cube 座標作用
概要：元の Bool 座標作用を、既存の dimension を持つ数値立方体の頂点写像へ移す。
方針：同じ右端列挙と逆列挙で入力と出力を移し、元の恒等・合成を回収する。
規約：元の頂点写像と全定数座標を保持。使われ方：実際の生成条件と具体的 cube 関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の necklace 射が同じ数値立方体の全頂点に作用する関数。 -/
def necklaceNumericMap {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.down.dimension → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex U.down.dimension :=
  fun x j => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f
    (fun v => x (T.down.nonjointCoordinate.symm v)) (U.down.nonjointCoordinate j)

/-- 元の数値頂点作用は恒等写像を保つ。 -/
lemma necklaceNumericMap_id (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (𝟙 T) = _root_.id := by
  funext x j
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (𝟙 T)
    (fun v => x (T.down.nonjointCoordinate.symm v)) (T.down.nonjointCoordinate j) = x j
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_id]
  exact congrArg x (T.down.nonjointCoordinate.symm_apply_apply j)

/-- 元の数値頂点作用は同じ necklace 射の合成を厳密に保つ。 -/
lemma necklaceNumericMap_comp {T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap (f ≫ g) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap g ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f := by
  funext x j
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap (f ≫ g)
      (fun v => x (T.down.nonjointCoordinate.symm v)) (V.down.nonjointCoordinate j) =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap g
      (fun v => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap f (fun a => x (T.down.nonjointCoordinate.symm a))
        (U.down.nonjointCoordinate (U.down.nonjointCoordinate.symm v)))
      (V.down.nonjointCoordinate j)
  simp only [Equiv.apply_symm_apply]
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_comp]
  rfl

/-- 元の数値出力座標の真偽を、同じ元の joint 像と数値ファイバーで回収する。 -/
lemma necklaceNumericMap_coordinate {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex T.down.dimension) (j : Fin U.down.dimension) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f x j = true ↔
      (∃ a : T.down.Vertex, a.val ∈ T.down.joints ∧
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f a = (U.down.nonjointCoordinate j).val) ∨
      ∃ i : Fin T.down.dimension, x i = true ∧
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (T.down.nonjointCoordinate i).val =
          (U.down.nonjointCoordinate j).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceBooleanMap_coordinate]
  apply or_congr_right
  constructor
  · rintro ⟨a, ha, hfa⟩
    refine ⟨T.down.nonjointCoordinate.symm a, ha, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hfa
  · rintro ⟨i, hi, hfi⟩
    refine ⟨T.down.nonjointCoordinate i, ?_, hfi⟩
    simpa only [Equiv.symm_apply_apply] using hi

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
