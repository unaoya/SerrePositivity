module
public import SerrePositivity.KST.SConstruction.CubeNormalTensor
public import SerrePositivity.KST.SConstruction.CubeMixedPathNormalization

/-! # 元の三段標準表示の生成条件
概要：各標準表示が元の生成射で実現され、元の生成写像が三段表示を持つことを示す。
方針：標準表示を帰納し、全語の元の頂点評価を保つ正規化を適用する。
規約：係数環や Serre 評価は入力にしない。使われ方：連結した二ブロック作用の生成性。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の全削除標準表示は、具体的な cubical 生成射で実現される。 -/
lemma cubeDeletionNormalVertex_generated {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d) := by
  induction d with
  | nil =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId 0))
    rw [cubeDeletionNormalId_vertex]
    exact .id 0
  | drop d ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ 0)
    exact .comp (.degeneracy _ 0) ih
  | keep d ih =>
    have h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d.keep = cubeVertexRightKeep
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d) := funext (cubeDeletionNormalVertex_keep_eval d)
    rw [h]
    exact cubeMapGenerated_rightKeep ih

/-- 元の全 max ブロック標準表示は、具体的な cubical 生成射で実現される。 -/
lemma cubeConnectionNormalVertex_generated {n m : ℕ} (d : CubeConnectionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeConnectionNormalVertex d) := by
  induction d with
  | nil =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeConnectionNormalVertex (cubeConnectionNormalId 0))
    rw [cubeConnectionNormalId_vertex]
    exact .id 0
  | keep d ih =>
    have h : cubeConnectionNormalVertex d.keep = cubeVertexRightKeep
        (cubeConnectionNormalVertex d) := funext (cubeConnectionNormalVertex_keep d)
    rw [h]
    exact cubeMapGenerated_rightKeep ih
  | merge d ih =>
    have h : cubeConnectionNormalVertex d.merge = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ 0 ∘
        cubeVertexRightKeep (cubeConnectionNormalVertex d) :=
      funext (cubeConnectionNormalVertex_merge d)
    rw [h]
    exact .comp (cubeMapGenerated_rightKeep ih) (.connection _ 0)

/-- 元の全定数・保持標準表示は、具体的な cubical 生成射で実現される。 -/
lemma cubeFaceNormalVertex_generated {n m : ℕ} (d : CubeFaceNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeFaceNormalVertex d) := by
  induction d with
  | nil => exact .id 0
  | point b d ih =>
    have h : cubeFaceNormalVertex (.point b d) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ 0 ∘
        cubeFaceNormalVertex d := by
      funext x
      simp only [cubeFaceNormalVertex, Function.comp_apply, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace,
        Fin.insertNth_zero']
    rw [h]
    exact .comp ih (.face b _ 0)
  | keep d ih => exact cubeMapGenerated_rightKeep ih

/-- 元の三段標準表示は、具体的な cubical 生成射で実現される。 -/
lemma cubeThreeNormalVertex_generated {n m : ℕ} (r : CubeThreeNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeThreeNormalVertex r) :=
  .comp (.comp (cubeDeletionNormalVertex_generated r.deletion)
    (cubeConnectionNormalVertex_generated r.connection)) (cubeFaceNormalVertex_generated r.face)

/-- 元の全生成写像は、同じ頂点関数を持つ三段標準表示を持つ。 -/
lemma cubeMapGenerated_exists_threeNormal {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : ∃ r : CubeThreeNormal n m, cubeThreeNormalVertex r = f := by
  obtain ⟨w, hw⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeMapGenerated_exists_word h
  obtain ⟨e, he⟩ := cubeWordPath_exists_mixedExpression w
  have hvertex := cubeMixedExpressionPath_concrete e
  erw [he] at hvertex
  exact ⟨cubeMixedExpressionNormal e,
    (cubeMixedExpressionNormal_vertex e).trans (hvertex.symm.trans hw)⟩

end SerrePositivity.KST.SConstruction
