module
public import SerrePositivity.KST.SConstruction.CubeFaceDeletionResult

/-! # 面の標準表示の後の一出力削除の正規化
概要：削除する出力が定数か保持入力かを判定し、高々一つの入力削除と面へ分解する。
方針：出力次元で帰納し、定数追加・入力保持への作用を使う。
規約：元の具体的な頂点関数の等号を回収する。使われ方：混合語の削除の左への移動。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 面の標準表示の後の一出力削除を入力側へ移す。 -/
def cubeFaceNormalDelete : {n m : ℕ} → CubeFaceNormal n (m + 1) →
    Fin (m + 1) → CubeFaceDeletionResult n m
  | _, 0, .point _ d, _ => .pure d
  | _, _ + 1, .point b d, i =>
      Fin.cases (.pure d) (fun j => cubeFaceDeletionResultPoint b (cubeFaceNormalDelete d j)) i
  | _, 0, .keep d, _ => .input 0 d
  | _, _ + 1, .keep d, i =>
      Fin.cases (.input 0 d) (fun j => cubeFaceDeletionResultKeep (cubeFaceNormalDelete d j)) i

/-- 元の一出力削除の正規化は、同じ元の頂点関数の合成を回収する。 -/
lemma cubeFaceNormalDelete_vertex {n m : ℕ} (d : CubeFaceNormal n (m + 1))
    (i : Fin (m + 1)) :
    cubeFaceDeletionResultVertex (cubeFaceNormalDelete d i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i ∘ cubeFaceNormalVertex d := by
  induction m generalizing n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    cases d <;> funext x j <;> exact Fin.elim0 j
  | succ m ih =>
    cases d with
    | point b d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · funext x j
        simp [cubeFaceNormalDelete, cubeFaceDeletionResultVertex, cubeFaceNormalVertex,
          _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
      · funext x
        change cubeFaceDeletionResultVertex
          (cubeFaceDeletionResultPoint b (cubeFaceNormalDelete d i)) x = _
        rw [cubeFaceDeletionResultPoint_vertex]
        change Fin.cons b (cubeFaceDeletionResultVertex (cubeFaceNormalDelete d i) x) =
          _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (m + 1) i.succ (Fin.cons b (cubeFaceNormalVertex d x))
        rw [ih d i, cubeVertexDegeneracy_cons]
        rfl
    | keep d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · funext x j
        simp [cubeFaceNormalDelete, cubeFaceDeletionResultVertex, cubeFaceNormalVertex,
          _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
        rfl
      · funext x
        change cubeFaceDeletionResultVertex
          (cubeFaceDeletionResultKeep (cubeFaceNormalDelete d i)) x = _
        rw [cubeFaceDeletionResultKeep_vertex]
        change Fin.cons (x 0)
          (cubeFaceDeletionResultVertex (cubeFaceNormalDelete d i) (fun j => x j.succ)) =
            _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (m + 1) i.succ
              (Fin.cons (x 0) (cubeFaceNormalVertex d (fun j => x j.succ)))
        rw [ih d i, cubeVertexDegeneracy_cons]
        rfl

end SerrePositivity.KST.SConstruction
