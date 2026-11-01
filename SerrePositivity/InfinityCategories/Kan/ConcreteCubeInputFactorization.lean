module
public import SerrePositivity.InfinityCategories.Kan.CubeUsedInputCompression
public import SerrePositivity.InfinityCategories.Kan.CubeCoordinateInsertion

/-! # 具体的な cubical 射の入力削除による因数分解
概要：元の射を、使用入力の座標削除と、未使用入力を持たない実際の残余射に分解する。
方針：零面の切断で残余射を構成し、有限 max 表示の評価回収で合成を照合する。
規約：全て元の具体的立方体圏の射。使われ方：正規化の削除工程から隣接 max 工程へ渡す。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の表示の使用入力だけを選ぶ実際の立方体の射。 -/
def cubeNormalFormInputSelection {n m : ℕ} (s : CubeJoinNormalForm n m) :
    ConcreteCube.mk n ⟶ ConcreteCube.mk (cubeNormalFormUsedInputs s).card :=
  ⟨cubeCoordinateSelect (cubeNormalFormInputEmbedding s),
    cubeCoordinateSelect_generated _ (cubeNormalFormInputEmbedding s).strictMono⟩

/-- 選択した入力を零面で元の座標へ戻す実際の切断。 -/
def cubeNormalFormInputSection {n m : ℕ} (s : CubeJoinNormalForm n m) :
    ConcreteCube.mk (cubeNormalFormUsedInputs s).card ⟶ ConcreteCube.mk n :=
  ⟨cubeCoordinateInsert (cubeNormalFormInputEmbedding s),
    cubeCoordinateInsert_generated _ (cubeNormalFormInputEmbedding s).strictMono⟩

/-- 零面の切断と入力選択の合成は、実際の立方体圏で恒等。 -/
lemma cubeNormalFormInputSection_selection {n m : ℕ} (s : CubeJoinNormalForm n m) :
    cubeNormalFormInputSection s ≫ cubeNormalFormInputSelection s = 𝟙 _ := by
  apply Subtype.ext
  funext x
  exact cubeCoordinateSelect_insert _ (cubeNormalFormInputEmbedding s).injective x

/-- 圧縮した表示の評価は、元の零埋め切断を通した元の表示の評価。 -/
lemma cubeNormalFormCompressed_eval_insert {n m : ℕ} (s : CubeJoinNormalForm n m)
    (x : CubeVertex (cubeNormalFormUsedInputs s).card) :
    cubeJoinNormalFormEval (cubeNormalFormCompressed s) x =
      cubeJoinNormalFormEval s (cubeCoordinateInsert (cubeNormalFormInputEmbedding s) x) := by
  have h := cubeNormalFormCompressed_eval s
    (cubeCoordinateInsert (cubeNormalFormInputEmbedding s) x)
  rw [cubeCoordinateSelect_insert _ (cubeNormalFormInputEmbedding s).injective] at h
  exact h

/-- 零面の切断から構成した、元の具体的な射の残余射。 -/
def concreteCubeInputCompressed {X Y : ConcreteCube} (f : X ⟶ Y) :
    ConcreteCube.mk (cubeNormalFormUsedInputs (concreteCubeNormalForm f)).card ⟶ Y :=
  cubeNormalFormInputSection (concreteCubeNormalForm f) ≫ f

/-- 残余射の元の頂点関数は、同じ圧縮した有限 max 表示の評価。 -/
lemma concreteCubeInputCompressed_val {X Y : ConcreteCube} (f : X ⟶ Y)
    (x : CubeVertex (cubeNormalFormUsedInputs (concreteCubeNormalForm f)).card) :
    (concreteCubeInputCompressed f).val x =
      cubeJoinNormalFormEval (cubeNormalFormCompressed (concreteCubeNormalForm f)) x := by
  exact ((cubeNormalFormCompressed_eval_insert (concreteCubeNormalForm f) x).trans
    (concreteCubeNormalForm_eval f _)).symm

/-- 元の具体射は、入力選択と同じ残余射の合成として厳密に回収される。 -/
lemma concreteCubeInputSelection_compressed {X Y : ConcreteCube} (f : X ⟶ Y) :
    cubeNormalFormInputSelection (concreteCubeNormalForm f) ≫ concreteCubeInputCompressed f =
      f := by
  apply Subtype.ext
  funext x
  change (concreteCubeInputCompressed f).val
    (cubeCoordinateSelect (cubeNormalFormInputEmbedding (concreteCubeNormalForm f)) x) = _
  rw [concreteCubeInputCompressed_val]
  exact concreteCubeNormalForm_compressed_eval f x

/-- 元の残余射から回収する一意な表示は、元の表示を圧縮したデータそのもの。 -/
lemma concreteCubeInputCompressed_normalForm {X Y : ConcreteCube} (f : X ⟶ Y) :
    concreteCubeNormalForm (concreteCubeInputCompressed f) =
      cubeNormalFormCompressed (concreteCubeNormalForm f) := by
  apply cubeJoinNormalFormEval_injective
  funext x
  rw [concreteCubeNormalForm_eval, concreteCubeInputCompressed_val]

/-- 元の残余射に未使用の入力が残らないことを、その実際の正規形で回収する。 -/
lemma concreteCubeInputCompressed_no_unused {X Y : ConcreteCube} (f : X ⟶ Y)
    (i : Fin (cubeNormalFormUsedInputs (concreteCubeNormalForm f)).card) :
    ∃ j, i ∈ cubeJoinNormalFormSupport (concreteCubeNormalForm (concreteCubeInputCompressed f))
      j := by
  rw [concreteCubeInputCompressed_normalForm]
  exact cubeNormalFormCompressed_no_unused _ i

end SerrePositivity.KST.SConstruction
