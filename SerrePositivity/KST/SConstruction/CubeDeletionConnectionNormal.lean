module
public import SerrePositivity.KST.SConstruction.CubeConnectionVertexRecursion

/-! # 削除・max の二段標準表示
概要：入力削除と残りのブロック max を束ね、右端入力の削除・保持・結合を作用させる。
方針：中間次元を明示した二つの標準表示と、その元の頂点関数を保持する。
規約：ブロック削除で複数の入力を削除できる。使われ方：max の後の出力削除の正規化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の入力削除とブロック max の二段標準表示。 -/
structure CubeDeletionConnectionNormal (n m : ℕ) where
  middle : ℕ
  deletion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n middle
  connection : CubeConnectionNormal middle m

/-- 二段標準表示の元の全頂点での評価。 -/
def cubeDeletionConnectionNormalVertex {n m : ℕ} (r : CubeDeletionConnectionNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  cubeConnectionNormalVertex r.connection ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex r.deletion

/-- 元の max の標準表示を、入力をまだ削除していない二段表示へ入れる。 -/
def cubeDeletionConnectionNormalFrom {n m : ℕ} (d : CubeConnectionNormal n m) :
    CubeDeletionConnectionNormal n m :=
  ⟨n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n, d⟩

/-- 入力を削除しない二段表示は、元の max の全評価を回収する。 -/
lemma cubeDeletionConnectionNormalFrom_vertex {n m : ℕ} (d : CubeConnectionNormal n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalFrom d) x =
      cubeConnectionNormalVertex d x := by
  dsimp only [cubeDeletionConnectionNormalVertex, cubeDeletionConnectionNormalFrom,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId_embedding]
  rfl

/-- 元の右端入力を削除して同じ残余ブロックへ渡す。 -/
def cubeDeletionConnectionNormalDrop {n m : ℕ} (r : CubeDeletionConnectionNormal n m) :
    CubeDeletionConnectionNormal (n + 1) m :=
  ⟨r.middle, .drop r.deletion, r.connection⟩

/-- 元の右端入力を新しいブロックとして保持する。 -/
def cubeDeletionConnectionNormalKeep {n m : ℕ} (r : CubeDeletionConnectionNormal n m) :
    CubeDeletionConnectionNormal (n + 1) (m + 1) :=
  ⟨r.middle + 1, .keep r.deletion, .keep r.connection⟩

/-- 元の右端入力を残余の最初のブロックへ結合する。 -/
def cubeDeletionConnectionNormalMerge {n m : ℕ} (r : CubeDeletionConnectionNormal n (m + 1)) :
    CubeDeletionConnectionNormal (n + 1) (m + 1) :=
  ⟨r.middle + 1, .keep r.deletion, .merge r.connection⟩

/-- 右端入力の削除は、元の頂点関数の同じ入力削除を回収する。 -/
lemma cubeDeletionConnectionNormalDrop_vertex {n m : ℕ} (r : CubeDeletionConnectionNormal n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalDrop r) x =
      cubeDeletionConnectionNormalVertex r (fun j => x j.succ) := rfl

/-- 新しいブロックの保持は、元の右端入力と残りの評価を回収する。 -/
lemma cubeDeletionConnectionNormalKeep_vertex {n m : ℕ} (r : CubeDeletionConnectionNormal n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalKeep r) x =
      Fin.cons (x 0) (cubeDeletionConnectionNormalVertex r (fun j => x j.succ)) := by
  change cubeConnectionNormalVertex r.connection.keep
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex r.deletion.keep x) = _
  rw [cubeConnectionNormalVertex_keep]
  rfl

/-- ブロックへの結合は、元の残余の評価と右端入力の connection を回収する。 -/
lemma cubeDeletionConnectionNormalMerge_vertex {n m : ℕ}
    (r : CubeDeletionConnectionNormal n (m + 1)) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeDeletionConnectionNormalVertex (cubeDeletionConnectionNormalMerge r) x =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0
        (Fin.cons (x 0) (cubeDeletionConnectionNormalVertex r (fun j => x j.succ))) := by
  change cubeConnectionNormalVertex r.connection.merge
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex r.deletion.keep x) = _
  rw [cubeConnectionNormalVertex_merge]
  rfl

end SerrePositivity.KST.SConstruction
