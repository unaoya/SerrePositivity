module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceNormalConnection

/-! # 削除・max・面の三段標準表示
概要：元の入力削除・空でないブロック max・定数面を、中間次元を保つデータへ束ねる。
方針：元の三つの標準表示と両評価を保持し、面の後の connection の計算結果を埋め込む。
規約：全混合語の正規化と一意性は別工程。使われ方：厳密な Serre 語評価の降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の削除・max・面の三段表示と二つの中間次元。 -/
structure CubeThreeNormal (n m : ℕ) where
  retained : ℕ
  blocks : ℕ
  deletion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n retained
  connection : CubeConnectionNormal retained blocks
  face : CubeFaceNormal blocks m

/-- 三段表示の元の全頂点での評価。 -/
def cubeThreeNormalVertex {n m : ℕ} (r : CubeThreeNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  cubeFaceNormalVertex r.face ∘ cubeConnectionNormalVertex r.connection ∘
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex r.deletion

/-- 元の恒等削除の標準表示は、全頂点で恒等。 -/
lemma cubeDeletionNormalId_vertex (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n) = _root_.id := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId_embedding]
  rfl

/-- 面の後の一 connection の計算結果を、元の三段表示へ埋め込む。 -/
def cubeFaceConnectionResultThree : {n m : ℕ} → CubeFaceConnectionResult n m →
    CubeThreeNormal n m
  | _, _, .pure d => ⟨_, _, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId _, cubeConnectionNormalId _, d⟩
  | _, _, .input i d =>
      ⟨_, _, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId _) i, cubeConnectionNormalId _, d⟩
  | _, _, .connect i d =>
      ⟨_, _, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId _, cubeConnectionNormalConnect (cubeConnectionNormalId _) i, d⟩

/-- 計算結果の三段表示への埋め込みは、元の全頂点での評価を保つ。 -/
lemma cubeFaceConnectionResultThree_vertex {n m : ℕ} (r : CubeFaceConnectionResult n m) :
    cubeThreeNormalVertex (cubeFaceConnectionResultThree r) = cubeFaceConnectionResultVertex r := by
  cases r with
  | pure d =>
    dsimp only [cubeFaceConnectionResultThree, cubeThreeNormalVertex,
      cubeFaceConnectionResultVertex]
    rw [cubeDeletionNormalId_vertex, cubeConnectionNormalId_vertex]
    rfl
  | input i d =>
    dsimp only [cubeFaceConnectionResultThree, cubeThreeNormalVertex,
      cubeFaceConnectionResultVertex]
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex_erase, cubeDeletionNormalId_vertex, cubeConnectionNormalId_vertex]
    rfl
  | connect i d =>
    dsimp only [cubeFaceConnectionResultThree, cubeThreeNormalVertex,
      cubeFaceConnectionResultVertex]
    rw [cubeConnectionNormalVertex_connect, cubeConnectionNormalId_vertex,
      cubeDeletionNormalId_vertex]
    rfl

variable (A : Type u) [CommRing A]

/-- 元の三段表示の Serre 余モノイド射としての評価。 -/
def serreCubeThreeNormal {n m : ℕ} (r : CubeThreeNormal n m) :
    serreCubeComonoid A n ⟶ serreCubeComonoid A m :=
  (serreCubeDeletionNormal A r.deletion ≫ serreCubeConnectionNormal A r.connection) ≫
    serreCubeFaceNormal A r.face

/-- 計算結果の三段表示への埋め込みは、元の Serre 評価そのものを保つ。 -/
lemma serreCubeFaceConnectionResultThree {n m : ℕ} (r : CubeFaceConnectionResult n m) :
    serreCubeThreeNormal A (cubeFaceConnectionResultThree r) =
      serreCubeFaceConnectionResult A r := by
  cases r with
  | pure d =>
    dsimp only [cubeFaceConnectionResultThree, serreCubeThreeNormal, serreCubeFaceConnectionResult]
    rw [serreCubeDeletionNormal_id, serreCubeConnectionNormal_id, Category.id_comp,
      Category.id_comp]
  | input i d =>
    dsimp only [cubeFaceConnectionResultThree, serreCubeThreeNormal, serreCubeFaceConnectionResult]
    rw [serreCubeDeletionNormal_erase, serreCubeDeletionNormal_id, serreCubeConnectionNormal_id]
    simp only [Category.id_comp, Category.comp_id]
  | connect i d =>
    dsimp only [cubeFaceConnectionResultThree, serreCubeThreeNormal, serreCubeFaceConnectionResult]
    rw [serreCubeDeletionNormal_id, serreCubeConnectionNormal_connect, serreCubeConnectionNormal_id]
    simp only [Category.id_comp]

/-- 面の後の任意の一 connection を、元の両評価を保った三段表示へ移す。 -/
lemma cubeFaceNormal_connection_three {n m : ℕ} (d : CubeFaceNormal n (m + 2)) (i : Fin (m + 1)) :
    ∃ r : CubeThreeNormal n (m + 1),
      cubeThreeNormalVertex r = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i ∘ cubeFaceNormalVertex d ∧
        serreCubeThreeNormal A r = serreCubeFaceNormal A d ≫ serreCubeConnection A m i := by
  exact ⟨cubeFaceConnectionResultThree (cubeFaceNormalConnect d i),
    (cubeFaceConnectionResultThree_vertex _).trans (cubeFaceNormalConnect_vertex d i),
    (serreCubeFaceConnectionResultThree A _).trans (serreCubeFaceNormal_connect A d i)⟩

end SerrePositivity.KST.SConstruction
