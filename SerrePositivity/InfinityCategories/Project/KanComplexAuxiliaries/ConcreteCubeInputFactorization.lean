module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeUsedInputCompression
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeCoordinateInsertion

/-! # 具体的な cubical 射の入力削除による因数分解
概要：元の射を、使用入力の座標削除と、未使用入力を持たない実際の残余射に分解する。
方針：零面の切断で残余射を構成し、有限 max 表示の評価回収で合成を照合する。
規約：全て元の具体的立方体圏の射。使われ方：正規化の削除工程から隣接 max 工程へ渡す。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の表示の使用入力だけを選ぶ実際の立方体の射。 -/
def cubeNormalFormInputSelection {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).card :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s),
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_generated _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s).strictMono⟩

/-- 選択した入力を零面で元の座標へ戻す実際の切断。 -/
def cubeNormalFormInputSection {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).card ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s),
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert_generated _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s).strictMono⟩

/-- 零面の切断と入力選択の合成は、実際の立方体圏で恒等。 -/
lemma cubeNormalFormInputSection_selection {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSection s ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection s = 𝟙 _ := by
  apply Subtype.ext
  funext x
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_insert _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s).injective x

/-- 圧縮した表示の評価は、元の零埋め切断を通した元の表示の評価。 -/
lemma cubeNormalFormCompressed_eval_insert {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs s).card) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed s) x =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval s (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s) x) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_eval s
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateInsert (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s) x)
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_insert _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding s).injective] at h
  exact h

/-- 零面の切断から構成した、元の具体的な射の残余射。 -/
def concreteCubeInputCompressed {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)).card ⟶ Y :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSection (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) ≫ f

/-- 残余射の元の頂点関数は、同じ圧縮した有限 max 表示の評価。 -/
lemma concreteCubeInputCompressed_val {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)).card) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f).val x =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)) x := by
  exact ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_eval_insert (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) x).trans
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval f _)).symm

/-- 元の具体射は、入力選択と同じ残余射の合成として厳密に回収される。 -/
lemma concreteCubeInputSelection_compressed {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f =
      f := by
  apply Subtype.ext
  funext x
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f).val
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)) x) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_val]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_compressed_eval f x

/-- 元の残余射から回収する一意な表示は、元の表示を圧縮したデータそのもの。 -/
lemma concreteCubeInputCompressed_normalForm {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval_injective
  funext x
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm_eval, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_val]

/-- 元の残余射に未使用の入力が残らないことを、その実際の正規形で回収する。 -/
lemma concreteCubeInputCompressed_no_unused {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormUsedInputs (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)).card) :
    ∃ j, i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f))
      j := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_normalForm]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_no_unused _ i

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputCompressed := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputCompressed_no_unused := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_no_unused

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputCompressed_normalForm := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_normalForm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputCompressed_val := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed_val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.concreteCubeInputSelection_compressed := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputSelection_compressed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormCompressed_eval_insert := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormCompressed_eval_insert

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputSection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputSection_selection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSection_selection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputSelection := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputSection._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSection._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeNormalFormInputSelection._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection._proof_1
