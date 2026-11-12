module
public import SerrePositivity.KST.SConstruction.CubeDeletionConnectionNormal

/-! # ブロック max の後の一出力削除の入力側への移動
概要：削除する出力ブロックの全入力を削除し、残りの max との二段表示を返す。
方針：入力次元で帰納し、右端ブロックの削除・保持・結合に分ける。
規約：元の頂点関数の合成を厳密に回収する。使われ方：一般の混合語の削除の左への移動。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の max の標準表示の後の一出力削除を、その全入力の削除へ移す。 -/
def cubeConnectionNormalDelete : {n m : ℕ} → CubeConnectionNormal n (m + 1) →
    Fin (m + 1) → CubeDeletionConnectionNormal n m
  | _, 0, .keep d, _ => cubeDeletionConnectionNormalDrop (cubeDeletionConnectionNormalFrom d)
  | _, _ + 1, .keep d, i => Fin.cases
      (cubeDeletionConnectionNormalDrop (cubeDeletionConnectionNormalFrom d))
      (fun j => cubeDeletionConnectionNormalKeep (cubeConnectionNormalDelete d j)) i
  | _, 0, .merge d, _ => cubeDeletionConnectionNormalDrop (cubeConnectionNormalDelete d 0)
  | _, _ + 1, .merge d, i => Fin.cases
      (cubeDeletionConnectionNormalDrop (cubeConnectionNormalDelete d 0))
      (fun j => cubeDeletionConnectionNormalMerge (cubeConnectionNormalDelete d j.succ)) i

/-- 一ブロックの出力削除の正規化は、元の全頂点の同じ関数合成を回収する。 -/
lemma cubeConnectionNormalDelete_vertex {n m : ℕ} (d : CubeConnectionNormal n (m + 1))
    (i : Fin (m + 1)) :
    cubeDeletionConnectionNormalVertex (cubeConnectionNormalDelete d i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i ∘ cubeConnectionNormalVertex d := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | keep d =>
      cases m with
      | zero => funext x j; exact Fin.elim0 j
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · funext x j
          simp [cubeConnectionNormalDelete, cubeDeletionConnectionNormalDrop_vertex,
            cubeDeletionConnectionNormalFrom_vertex, cubeConnectionNormalVertex_keep,
            _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
        · funext x
          change cubeDeletionConnectionNormalVertex
            (cubeDeletionConnectionNormalKeep (cubeConnectionNormalDelete d i)) x = _
          rw [cubeDeletionConnectionNormalKeep_vertex, ih d i]
          change Fin.cons (α := fun _ => Bool) (x 0) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i
            (cubeConnectionNormalVertex d (fun j => x j.succ))) = _
          simp only [Function.comp_apply]
          rw [cubeConnectionNormalVertex_keep, cubeVertexDegeneracy_cons]
    | merge d =>
      cases m with
      | zero => funext x j; exact Fin.elim0 j
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · funext x
          change cubeDeletionConnectionNormalVertex
            (cubeDeletionConnectionNormalDrop (cubeConnectionNormalDelete d 0)) x = _
          rw [cubeDeletionConnectionNormalDrop_vertex, ih d 0]
          change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (m + 1) 0
            (cubeConnectionNormalVertex d (fun j => x j.succ)) = _
          simp only [Function.comp_apply]
          rw [cubeConnectionNormalVertex_merge, cubeVertexConnection_delete_zero]
          rfl
        · funext x
          change cubeDeletionConnectionNormalVertex
            (cubeDeletionConnectionNormalMerge (cubeConnectionNormalDelete d i.succ)) x = _
          rw [cubeDeletionConnectionNormalMerge_vertex, ih d i.succ]
          change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0 (Fin.cons (α := fun _ => Bool) (x 0)
            (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (m + 1) i.succ
              (cubeConnectionNormalVertex d (fun j => x j.succ)))) = _
          simp only [Function.comp_apply]
          rw [cubeConnectionNormalVertex_merge, cubeVertexConnection_delete_succ,
            cubeVertexDegeneracy_cons]

end SerrePositivity.KST.SConstruction
