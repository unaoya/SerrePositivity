module
public import SerrePositivity.InfinityCategories.Kan.CubeSupportOutputCompletion

/-! # 具体的な cubical 射の削除・max・面の三段正規形
概要：元の全具体射を、削除だけ・connection だけ・面だけの三つの写像へ分解する。
方針：標準使用入力・support ブロック・定数補完の厳密な因数分解に生成条件を付ける。
規約：Serre 語評価の同値性は主張しない。使われ方：語の表示非依存性を証明する標準表示。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の空の support の出力補完は、面だけの合成で生成される。 -/
lemma cubeSupportOutputCompletion_faceGenerated {n m : ℕ} (s : CubeJoinNormalForm n m) :
    CubeFaceGenerated (cubeSupportOutputCompletion s).val :=
  cubeCoordinateComplete_faceGenerated _ (cubeSupportOutputEmbedding s).strictMono _
    (cubeSupportOutputEmbedding_zero s)

/-- 元の全具体射は、削除・隣接 max・定数面のみの三段階の元の関数合成で実現される。 -/
lemma concreteCube_exists_deletion_max_face {X Y : ConcreteCube} (f : X ⟶ Y) :
    ∃ (a b : ℕ) (d : CubeVertex X.dimension → CubeVertex a)
      (c : CubeVertex a → CubeVertex b) (δ : CubeVertex b → CubeVertex Y.dimension),
      CubeDeletionGenerated d ∧ CubeConnectionGenerated c ∧ CubeFaceGenerated δ ∧
        δ ∘ c ∘ d = f.val := by
  refine ⟨_, _, (cubeNormalFormInputSelection (concreteCubeNormalForm f)).val,
    (cubeSupportMax (concreteCubeInputCompressedSupportPartition f)).val,
    (cubeSupportOutputCompletion
      (concreteCubeNormalForm (concreteCubeInputCompressed f))).val, ?_, ?_, ?_, ?_⟩
  · exact cubeNormalFormInputEmbedding_deletionGenerated _
  · exact cubeSupportBlockMap_connectionGenerated _
  · exact cubeSupportOutputCompletion_faceGenerated _
  · exact congrArg Subtype.val (concreteCube_deletion_max_face_factorization f)

end SerrePositivity.KST.SConstruction
