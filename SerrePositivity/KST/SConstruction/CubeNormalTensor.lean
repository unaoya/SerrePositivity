module
public import SerrePositivity.KST.SConstruction.CubeVertexBlocks

/-! # 三種類の標準表示の因子順を保つ連結
概要：削除・max・面の各標準表示を、それぞれ左右の二ブロックへ連結する。
方針：右側の表示の構文で帰納し、元の同じ保持・削除・結合・定数の構成子を使う。
規約：右側の座標を先に数える。使われ方：具体的な tensor 射の生成条件。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 左右の元の削除標準表示を、そのままの順序で連結する。 -/
def cubeDeletionNormalTensor {n p : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n p) :
    {m q : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal m q → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal (n + m) (p + q)
  | _, _, .nil => d
  | _, _, .drop e => .drop (cubeDeletionNormalTensor d e)
  | _, _, .keep e => .keep (cubeDeletionNormalTensor d e)

/-- 左右の元の非空 max ブロック標準表示を、そのままの順序で連結する。 -/
def cubeConnectionNormalTensor {n p : ℕ} (d : CubeConnectionNormal n p) :
    {m q : ℕ} → CubeConnectionNormal m q → CubeConnectionNormal (n + m) (p + q)
  | _, _, .nil => d
  | _, _, .keep e => .keep (cubeConnectionNormalTensor d e)
  | _, _, .merge e => .merge (cubeConnectionNormalTensor d e)

/-- 左右の元の定数・保持標準表示を、そのままの順序で連結する。 -/
def cubeFaceNormalTensor {n p : ℕ} (d : CubeFaceNormal n p) :
    {m q : ℕ} → CubeFaceNormal m q → CubeFaceNormal (n + m) (p + q)
  | _, _, .nil => d
  | _, _, .point b e => .point b (cubeFaceNormalTensor d e)
  | _, _, .keep e => .keep (cubeFaceNormalTensor d e)

/-- 元の削除標準表示の保持構成子の頂点評価。 -/
lemma cubeDeletionNormalVertex_keep_eval {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d.keep x =
      Fin.cons (x 0) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d (fun j => x j.succ)) := by
  funext j
  refine Fin.cases rfl (fun j => rfl) j

/-- 元の削除標準表示の削除構成子の頂点評価。 -/
lemma cubeDeletionNormalVertex_drop_eval {n m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d.drop x = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d (fun j => x j.succ) := rfl

/-- 連結の右ブロック内の最初の max は、その右ブロックだけに作用する。 -/
lemma cubeVertexJoin_connection_zero {n m : ℕ} (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n)
    (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (m + 1)) (b : Bool) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + m) 0
        (Fin.cons b (cubeVertexJoin (n := n) (m := m + 1) x y)) =
      cubeVertexJoin (n := n) (m := m + 1) x (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0 (Fin.cons b y)) := by
  simp only [cubeVertexConnection_zero, cubeVertexJoin, Fin.cons_zero, Fin.cons_succ]

/-- 連結した削除表示の元の評価は、元の左右の削除を回収する。 -/
lemma cubeDeletionNormalTensor_vertex_join {n p m q : ℕ}
    (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n p) (e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal m q)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (cubeDeletionNormalTensor d e) (cubeVertexJoin x y) =
      cubeVertexJoin (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d x) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex e y) := by
  induction e with
  | nil => rfl
  | drop e ih => exact ih (fun j => y j.succ)
  | keep e ih =>
    dsimp only [cubeDeletionNormalTensor]
    rw [cubeDeletionNormalVertex_keep_eval, cubeDeletionNormalVertex_keep_eval]
    exact congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _ => Fin.cons (α := fun _ => Bool) (y 0) v)
      (ih (fun j => y j.succ))

/-- 連結した max ブロック表示の元の評価は、元の左右の max を回収する。 -/
lemma cubeConnectionNormalTensor_vertex_join {n p m q : ℕ}
    (d : CubeConnectionNormal n p) (e : CubeConnectionNormal m q)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeConnectionNormalVertex (cubeConnectionNormalTensor d e) (cubeVertexJoin x y) =
      cubeVertexJoin (cubeConnectionNormalVertex d x) (cubeConnectionNormalVertex e y) := by
  induction e with
  | nil => rfl
  | keep e ih =>
    dsimp only [cubeConnectionNormalTensor]
    rw [cubeConnectionNormalVertex_keep, cubeConnectionNormalVertex_keep]
    exact congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _ => Fin.cons (α := fun _ => Bool) (y 0) v)
      (ih (fun j => y j.succ))
  | merge e ih =>
    dsimp only [cubeConnectionNormalTensor]
    rw [cubeConnectionNormalVertex_merge, cubeConnectionNormalVertex_merge]
    exact (congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _ => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ 0
      (Fin.cons (α := fun _ => Bool) (y 0) v)) (ih (fun j => y j.succ))).trans
        (cubeVertexJoin_connection_zero _ _ (y 0))

/-- 連結した面表示の元の評価は、元の左右の定数・保持を回収する。 -/
lemma cubeFaceNormalTensor_vertex_join {n p m q : ℕ}
    (d : CubeFaceNormal n p) (e : CubeFaceNormal m q)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeFaceNormalVertex (cubeFaceNormalTensor d e) (cubeVertexJoin x y) =
      cubeVertexJoin (cubeFaceNormalVertex d x) (cubeFaceNormalVertex e y) := by
  induction e with
  | nil => rfl
  | point b e ih =>
    exact congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _ => Fin.cons (α := fun _ => Bool) b v) (ih y)
  | keep e ih =>
    exact congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _ => Fin.cons (α := fun _ => Bool) (y 0) v)
      (ih (fun j => y j.succ))

end SerrePositivity.KST.SConstruction
