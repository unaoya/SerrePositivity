module
public import SerrePositivity.KST.SConstruction.CubeNormalGenerated

/-! # 元の三段標準表示の連結と生成写像の二ブロック閉性
概要：三段表示を元の因子順で連結し、全生成写像の二ブロック作用が生成されることを示す。
方針：各標準表示の頂点評価を連結で回収し、元の生成条件へ戻す。
規約：左右の入力を交換しない。使われ方：具体的立方体圏の連結積の射。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の左右の三段表示を、元の全中間次元を保って連結する。 -/
def cubeThreeNormalTensor {n p m q : ℕ} (r : CubeThreeNormal n p) (s : CubeThreeNormal m q) :
    CubeThreeNormal (n + m) (p + q) where
  retained := r.retained + s.retained
  blocks := r.blocks + s.blocks
  deletion := cubeDeletionNormalTensor r.deletion s.deletion
  connection := cubeConnectionNormalTensor r.connection s.connection
  face := cubeFaceNormalTensor r.face s.face

/-- 連結した三段表示の元の評価は、元の左右の評価を回収する。 -/
lemma cubeThreeNormalTensor_vertex_join {n p m q : ℕ}
    (r : CubeThreeNormal n p) (s : CubeThreeNormal m q) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeThreeNormalVertex (cubeThreeNormalTensor r s) (cubeVertexJoin x y) =
      cubeVertexJoin (cubeThreeNormalVertex r x) (cubeThreeNormalVertex s y) := by
  dsimp only [cubeThreeNormalVertex, cubeThreeNormalTensor, Function.comp_apply]
  rw [cubeDeletionNormalTensor_vertex_join, cubeConnectionNormalTensor_vertex_join,
    cubeFaceNormalTensor_vertex_join]

/-- 連結した三段表示の元の評価は、元の二ブロック作用そのもの。 -/
lemma cubeThreeNormalTensor_vertex {n p m q : ℕ}
    (r : CubeThreeNormal n p) (s : CubeThreeNormal m q) :
    cubeThreeNormalVertex (cubeThreeNormalTensor r s) =
      cubeVertexTensor (cubeThreeNormalVertex r) (cubeThreeNormalVertex s) :=
  cubeVertexTensor_eq_of_join _ _ _ (cubeThreeNormalTensor_vertex_join r s)

/-- 元の二つの生成写像の二ブロック作用は、同じ元の生成射で実現される。 -/
lemma cubeMapGenerated_tensor {n p m q : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p}
    {g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex q} (hf : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) (hg : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated g) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeVertexTensor f g) := by
  obtain ⟨r, hr⟩ := cubeMapGenerated_exists_threeNormal hf
  obtain ⟨s, hs⟩ := cubeMapGenerated_exists_threeNormal hg
  have h := cubeThreeNormalVertex_generated (cubeThreeNormalTensor r s)
  rw [cubeThreeNormalTensor_vertex, hr, hs] at h
  exact h

end SerrePositivity.KST.SConstruction
