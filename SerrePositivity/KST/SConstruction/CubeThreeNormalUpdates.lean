module
public import SerrePositivity.KST.SConstruction.CubeThreeNormalResults

/-! # 三段標準表示の全生成射による更新
概要：恒等射と、面・削除・connection の任意座標での後合成を三段表示に戻す。
方針：面の残余を計算し、入力操作を削除・max の接頭部へ吸収する。
規約：元の二つの評価を保持する。使われ方：任意の混合語の正規化の帰納段階。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の恒等射の三段表示。 -/
def cubeThreeNormalId (n : ℕ) : CubeThreeNormal n n :=
  cubeThreeNormalWithFace (cubeDeletionConnectionNormalId n) (cubeFaceNormalId n)

/-- 三段表示に元の任意座標の面を追加する。 -/
def cubeThreeNormalPoint {n m : ℕ} (r : CubeThreeNormal n m)
    (b : Bool) (i : Fin (m + 1)) : CubeThreeNormal n (m + 1) :=
  cubeThreeNormalWithFace (cubeThreeNormalPrefix r) (cubeFaceNormalInsert r.face b i)

/-- 三段表示に元の任意座標の削除を追加する。 -/
def cubeThreeNormalDelete {n m : ℕ} (r : CubeThreeNormal n (m + 1))
    (i : Fin (m + 1)) : CubeThreeNormal n m :=
  cubeThreeNormalAfterDeletion (cubeThreeNormalPrefix r) (cubeFaceNormalDelete r.face i)

/-- 三段表示に元の任意座標の connection を追加する。 -/
def cubeThreeNormalConnect {n m : ℕ} (r : CubeThreeNormal n (m + 2))
    (i : Fin (m + 1)) : CubeThreeNormal n (m + 1) :=
  cubeThreeNormalAfterConnection (cubeThreeNormalPrefix r) (cubeFaceNormalConnect r.face i)

/-- 恒等三段表示は元の恒等関数を回収する。 -/
lemma cubeThreeNormalId_vertex (n : ℕ) :
    cubeThreeNormalVertex (cubeThreeNormalId n) = _root_.id := by
  dsimp only [cubeThreeNormalId]
  rw [cubeThreeNormalWithFace_vertex, cubeDeletionConnectionNormalId_vertex,
    cubeFaceNormalId_vertex]
  rfl

/-- 面の追加は元の頂点関数の後合成を回収する。 -/
lemma cubeThreeNormalPoint_vertex {n m : ℕ} (r : CubeThreeNormal n m)
    (b : Bool) (i : Fin (m + 1)) :
    cubeThreeNormalVertex (cubeThreeNormalPoint r b i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b m i ∘ cubeThreeNormalVertex r := by
  dsimp only [cubeThreeNormalPoint]
  rw [cubeThreeNormalWithFace_vertex, cubeFaceNormalInsert_vertex]
  rfl

/-- 削除の追加は元の頂点関数の後合成を回収する。 -/
lemma cubeThreeNormalDelete_vertex {n m : ℕ} (r : CubeThreeNormal n (m + 1))
    (i : Fin (m + 1)) :
    cubeThreeNormalVertex (cubeThreeNormalDelete r i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i ∘ cubeThreeNormalVertex r := by
  dsimp only [cubeThreeNormalDelete]
  rw [cubeThreeNormalAfterDeletion_vertex, cubeFaceNormalDelete_vertex]
  rfl

/-- connection の追加は元の頂点関数の後合成を回収する。 -/
lemma cubeThreeNormalConnect_vertex {n m : ℕ} (r : CubeThreeNormal n (m + 2))
    (i : Fin (m + 1)) :
    cubeThreeNormalVertex (cubeThreeNormalConnect r i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i ∘ cubeThreeNormalVertex r := by
  dsimp only [cubeThreeNormalConnect]
  rw [cubeThreeNormalAfterConnection_vertex, cubeFaceNormalConnect_vertex]
  rfl

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 恒等三段表示は元の Serre 恒等射を回収する。 -/
lemma serreCubeThreeNormal_id (n : ℕ) :
    serreCubeThreeNormal A (cubeThreeNormalId n) = 𝟙 _ := by
  dsimp only [cubeThreeNormalId]
  rw [serreCubeThreeNormal_withFace, serreCubeDeletionConnectionNormal_id,
    serreCubeFaceNormal_id, Category.comp_id]

/-- 面の追加は元の Serre 面の後合成を回収する。 -/
lemma serreCubeThreeNormal_point {n m : ℕ} (r : CubeThreeNormal n m)
    (b : Bool) (i : Fin (m + 1)) :
    serreCubeThreeNormal A (cubeThreeNormalPoint r b i) =
      serreCubeThreeNormal A r ≫ serreCubeFace A b m i := by
  dsimp only [cubeThreeNormalPoint]
  rw [serreCubeThreeNormal_withFace, serreCubeFaceNormal_insert]
  exact (Category.assoc _ _ _).symm

/-- 削除の追加は元の Serre 削除の後合成を回収する。 -/
lemma serreCubeThreeNormal_delete {n m : ℕ} (r : CubeThreeNormal n (m + 1))
    (i : Fin (m + 1)) :
    serreCubeThreeNormal A (cubeThreeNormalDelete r i) =
      serreCubeThreeNormal A r ≫ serreCubeDegeneracy A m i := by
  dsimp only [cubeThreeNormalDelete]
  rw [serreCubeThreeNormal_afterDeletion, serreCubeFaceNormal_delete]
  exact (Category.assoc _ _ _).symm

/-- connection の追加は元の Serre connection の後合成を回収する。 -/
lemma serreCubeThreeNormal_connect {n m : ℕ} (r : CubeThreeNormal n (m + 2))
    (i : Fin (m + 1)) :
    serreCubeThreeNormal A (cubeThreeNormalConnect r i) =
      serreCubeThreeNormal A r ≫ serreCubeConnection A m i := by
  dsimp only [cubeThreeNormalConnect]
  rw [serreCubeThreeNormal_afterConnection, serreCubeFaceNormal_connect]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
