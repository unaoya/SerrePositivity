module
public import SerrePositivity.KST.SConstruction.CubeThreeNormalTensor
public import Mathlib.CategoryTheory.Products.Basic

/-! # 具体的立方体圏の元の連結積の二変数関手
概要：左右の二ブロック作用を、具体的な立方体圏上の二変数関手へ束ねる。
方針：三段標準表示の連結による生成性と、元の頂点関数の恒等・合成保存を使う。
規約：右ブロックを先に数え、因子順を保持する。使われ方：cubical rigidification の合成。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の具体的な左右の立方体の連結。 -/
def concreteCubeTensorObj (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube := ⟨X.dimension + Y.dimension⟩

/-- 元の具体的な左右の射の、同じ頂点関数を持つ二ブロック作用。 -/
def concreteCubeTensorMap {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ X') (g : Y ⟶ Y') :
    concreteCubeTensorObj X Y ⟶ concreteCubeTensorObj X' Y' :=
  ⟨cubeVertexTensor f.val g.val, cubeMapGenerated_tensor f.property g.property⟩

/-- 元の左右の恒等射の連結は、連結した立方体の恒等射。 -/
lemma concreteCubeTensorMap_id (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    concreteCubeTensorMap (𝟙 X) (𝟙 Y) = 𝟙 (concreteCubeTensorObj X Y) :=
  Subtype.ext (cubeVertexTensor_id X.dimension Y.dimension)

/-- 元の左右の合成の連結は、連結した射の元の合成。 -/
lemma concreteCubeTensorMap_comp {X X' X'' Y Y' Y'' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    concreteCubeTensorMap (f ≫ f') (g ≫ g') =
      concreteCubeTensorMap f g ≫ concreteCubeTensorMap f' g' :=
  Subtype.ext (cubeVertexTensor_comp f.val f'.val g.val g'.val)

/-- 元の射の順序を保つ、具体的立方体の連結積の二変数関手。 -/
def concreteCubeTensor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube × _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  obj P := concreteCubeTensorObj P.1 P.2
  map f := concreteCubeTensorMap f.1 f.2
  map_id P := concreteCubeTensorMap_id P.1 P.2
  map_comp f g := concreteCubeTensorMap_comp f.1 g.1 f.2 g.2

/-- 元の連結した頂点で、連結積の射は元の左右の射を回収する。 -/
lemma concreteCubeTensorMap_join {X X' Y Y' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ X') (g : Y ⟶ Y')
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Y.dimension) :
    (concreteCubeTensorMap f g).val (cubeVertexJoin x y) =
      cubeVertexJoin (f.val x) (g.val y) := cubeVertexTensor_join f.val g.val x y

end SerrePositivity.KST.SConstruction
