module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.CubeMapGenerated
public import Mathlib.CategoryTheory.Types.Basic

/-! # max connection を持つ具体的な立方体圏
概要：射を元の生成関数のなす部分集合とし、実際の関数の等号で同一視した圏を作る。
方針：合成は関数合成、生成条件は Prop として保持し、頂点集合への忠実な関手を作る。
規約：語の関係式による商を定義にしない。使われ方：Serre 鎖立方体の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 具体的な立方体圏の対象は、その有限次元。 -/
structure ConcreteCube where
  dimension : ℕ

/-- 元の生成関数だけを射に持つ具体的な立方体圏。 -/
instance concreteCubeCategory : Category _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  Hom X Y := {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Y.dimension // _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f}
  id X := ⟨_root_.id, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.id X.dimension⟩
  comp f g := ⟨g.val ∘ f.val, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.comp f.property g.property⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

/-- 元の二端点の挿入を持つ、具体的な立方体圏の面。 -/
def concreteCubeFace (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 1) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.face b n i⟩

/-- 元の座標削除を持つ、具体的な立方体圏の退化。 -/
def concreteCubeDegeneracy (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.degeneracy n i⟩

/-- 元の隣接 max を持つ、具体的な立方体圏の connection。 -/
def concreteCubeConnection (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (n + 1) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated.connection n i⟩

/-- 具体的な立方体圏を元の頂点集合と関数へ送る関手。 -/
def concreteCubeVertexFunctor : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ Type where
  obj X := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension
  map f := TypeCat.ofHom f.val

/-- 具体的な立方体圏の射の等号は、元の頂点関数の等号で検出される。 -/
instance concreteCubeVertexFunctor_faithful : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor.Faithful where
  map_injective h := Subtype.ext (congrArg TypeCat.homEquiv h)

/-- 全ての具体的な立方体の射は、元の頂点の順序を保つ。 -/
lemma concreteCubeMap_monotone {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    Monotone f.val :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeMapGenerated_monotone f.property

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
