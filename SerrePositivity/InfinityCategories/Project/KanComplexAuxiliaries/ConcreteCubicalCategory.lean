module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated
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

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeConnection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeDegeneracy := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeFace := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeMap_monotone := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeMap_monotone

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeVertexFunctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor_faithful (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeVertexFunctor_faithful := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor_faithful

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.casesOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.dimension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.dimension := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.dimension

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.mk := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.rec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.recOn := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeCategory._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeCategory._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeVertexFunctor._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeVertexFunctor._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeVertexFunctor._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.ConcreteCube.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk.sizeOf_spec
