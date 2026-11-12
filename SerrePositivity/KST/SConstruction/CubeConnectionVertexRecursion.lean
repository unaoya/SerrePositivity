module
public import SerrePositivity.KST.SConstruction.CubeFaceDeletionPathNormalization

/-! # ブロック標準表示の元の頂点関数の再帰式
概要：新しいブロックと右端への max の評価を、元の有限 fiber max から回収する。
方針：真の入力の存在を零番目と残りへ分け、元の connection の座標式と照合する。
規約：元の右端からの座標順を保持する。使われ方：ブロック出力削除の入力側への移動。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 新しい一入力の fiber は右端の一出力となり、残りの fiber をそのまま保つ。 -/
lemma cubeFiberMax_keep {n m : ℕ} (q : Fin n → Fin m) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (Fin.cons 0 (fun j => (q j).succ)) x =
      Fin.cons (x 0) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q (fun j => x j.succ)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · apply Bool.eq_iff_iff.mpr
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff, Fin.exists_fin_succ]
  · have hz : (0 : Fin (m + 1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
    apply Bool.eq_iff_iff.mpr
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff, Fin.exists_fin_succ, hz]

/-- 新しい右端入力を最初の fiber へ加えると、同じ出力でだけ max が加わる。 -/
lemma cubeFiberMax_merge {n m : ℕ} (q : Fin n → Fin (m + 1)) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (Fin.cons 0 q) x =
      Fin.cons (x 0 ⊔ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q (fun j => x j.succ) 0)
        (fun j => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax q (fun k => x k.succ) j.succ) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · apply Bool.eq_iff_iff.mpr
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff, Fin.exists_fin_succ]
  · have hz : (0 : Fin (m + 1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
    apply Bool.eq_iff_iff.mpr
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax_true_iff, Fin.exists_fin_succ, hz]

/-- 元の右端 connection は先頭二入力の max と残りの入力。 -/
lemma cubeVertexConnection_zero (n : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n 0 x =
      Fin.cons (x 0 ⊔ x (0 : Fin (n + 1)).succ) (fun j => x j.succ.succ) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]

/-- ブロック開始の元の評価は、右端入力と残りのブロックの評価。 -/
lemma cubeConnectionNormalVertex_keep {n m : ℕ} (d : CubeConnectionNormal n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeConnectionNormalVertex d.keep x =
      Fin.cons (x 0) (cubeConnectionNormalVertex d (fun j => x j.succ)) :=
  cubeFiberMax_keep _ x

/-- ブロックへの追加の元の評価は、残りの評価と右端入力の元の connection。 -/
lemma cubeConnectionNormalVertex_merge {n m : ℕ} (d : CubeConnectionNormal n (m + 1))
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeConnectionNormalVertex d.merge x = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0
      (Fin.cons (x 0) (cubeConnectionNormalVertex d (fun j => x j.succ))) := by
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeFiberMax (Fin.cons 0 (cubeConnectionNormalBlock d)) x = _
  rw [cubeFiberMax_merge, cubeVertexConnection_zero]
  rfl

/-- 元の右端 max の出力を削除すると、元の二入力を削除する。 -/
lemma cubeVertexConnection_delete_zero (n : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n 0 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n 0 x) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n 0 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) 0 x) := by
  rw [cubeVertexConnection_zero]
  funext j
  simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]

/-- 元の右端 max と離れた出力削除の交換は、同じ入力削除を回収する。 -/
lemma cubeVertexConnection_delete_succ (n : ℕ) (i : Fin (n + 1))
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 3)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) i.succ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + 1) 0 x) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n 0 (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 2) i.succ.succ x) := by
  rw [cubeVertexConnection_zero, cubeVertexDegeneracy_cons, cubeVertexConnection_zero]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]

end SerrePositivity.KST.SConstruction
