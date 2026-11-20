module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeSupportOutputCompletion

/-! # 具体的な cubical 射の削除・max・面の三段正規形
概要：元の全具体射を、削除だけ・connection だけ・面だけの三つの写像へ分解する。
方針：標準使用入力・support ブロック・定数補完の厳密な因数分解に生成条件を付ける。
規約：Serre 語評価の同値性は主張しない。使われ方：語の表示非依存性を証明する標準表示。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の空の support の出力補完は、面だけの合成で生成される。 -/
lemma cubeSupportOutputCompletion_faceGenerated {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeFaceGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputCompletion s).val :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateComplete_faceGenerated _ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding s).strictMono _
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputEmbedding_zero s)

/-- 元の全具体射は、削除・隣接 max・定数面のみの三段階の元の関数合成で実現される。 -/
lemma concreteCube_exists_deletion_max_face {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    ∃ (a b : ℕ) (d : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex X.dimension → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex a)
      (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex a → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex b) (δ : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex b → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex Y.dimension),
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionGenerated d ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeConnectionGenerated c ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeFaceGenerated δ ∧
        δ ∘ c ∘ d = f.val := by
  refine ⟨_, _, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputSelection (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm f)).val,
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportMax (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressedSupportPartition f)).val,
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputCompletion
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeNormalForm (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeInputCompressed f))).val, ?_, ?_, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeNormalFormInputEmbedding_deletionGenerated _
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportBlockMap_connectionGenerated _
  · exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeSupportOutputCompletion_faceGenerated _
  · exact congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCube_deletion_max_face_factorization f)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
