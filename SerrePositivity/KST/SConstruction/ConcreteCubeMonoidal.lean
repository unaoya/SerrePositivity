module
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensorCoherence
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # 元の連結積による具体的立方体のモノイダル圏
概要：元の生成射を保つ連結積・零次元単位・次元移送の結合同型を一つに束ねる。
方針：元の二変数関手、構造同型の自然性、五角と三角の証明を適用する。
規約：max connection のみで、対称性や座標反転を追加しない。使われ方：cubical 合成。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の具体的立方体の連結積と、その構造同型のデータ。 -/
instance concreteCubeMonoidalStruct : MonoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  tensorObj := concreteCubeTensorObj
  tensorHom := concreteCubeTensorMap
  whiskerLeft X {_ _} f := concreteCubeTensorMap (𝟙 X) f
  whiskerRight {_ _} f Y := concreteCubeTensorMap f (𝟙 Y)
  tensorUnit := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0
  associator := concreteCubeAssociator
  leftUnitor := concreteCubeLeftUnitor
  rightUnitor := concreteCubeRightUnitor

/-- 元の連結積を持つ具体的立方体圏のモノイダル構造。 -/
instance concreteCubeMonoidal : MonoidalCategory _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := concreteCubeTensorMap_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (concreteCubeTensorMap_comp f f' g g').symm)
    (associator_naturality := concreteCubeAssociator_naturality)
    (leftUnitor_naturality := concreteCubeLeftUnitor_naturality)
    (rightUnitor_naturality := concreteCubeRightUnitor_naturality)
    (pentagon := concreteCubeAssociator_pentagon)
    (triangle := concreteCubeAssociator_triangle)

/-- モノイダル圏の tensor 関手は元の連結積の二変数関手そのもの。 -/
lemma concreteCubeMonoidal_tensor : MonoidalCategory.tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube = concreteCubeTensor := rfl

end SerrePositivity.KST.SConstruction
