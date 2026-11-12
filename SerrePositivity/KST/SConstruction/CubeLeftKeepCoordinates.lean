module
public import SerrePositivity.KST.SConstruction.CubeRightKeep

/-! # 左端保持と元の cubical 座標射
概要：最後の座標を保持したときの、元の面・削除・connection の座標式を証明する。
方針：元の座標順を保った snoc と、削除添字の castSucc の交換を使う。
規約：左端は最大座標で、右端の座標零は移さない。使われ方：立方体の左 tensor 作用。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 内側座標の削除は、元の左端の値を保持する。 -/
lemma cubeVertexDegeneracy_snoc (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) i.castSucc (Fin.snoc x b) =
      Fin.snoc (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i x) b := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hl : i.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
      rw [Fin.succAbove_castSucc_of_le i (Fin.last n) (Fin.le_last i)]
      rfl
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy, hl, Fin.snoc_last]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy, Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc]

/-- 内側座標への端点挿入は、元の左端の値を保持する。 -/
lemma cubeVertexFace_snoc (b c : Bool) (n : ℕ) (i : Fin (n + 1)) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b (n + 1) i.castSucc (Fin.snoc x c) =
      Fin.snoc (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i x) c := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hl : i.castSucc.succAbove (Fin.last n) = Fin.last (n + 1) := by
      rw [Fin.succAbove_castSucc_of_le i (Fin.last n) (Fin.le_last i)]
      rfl
    rw [← hl]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_succAbove, Fin.snoc_last]
    rw [hl, Fin.snoc_last]
  · refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace]
    · rw [← Fin.castSucc_succAbove_castSucc]
      simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_apply_succAbove, Fin.snoc_castSucc]
      rw [Fin.castSucc_succAbove_castSucc, Fin.snoc_castSucc, Fin.insertNth_apply_succAbove]

/-- 内側の隣接 max は、元の左端の値を保持する。 -/
lemma cubeVertexConnection_snoc (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + 1) i.castSucc (Fin.snoc x b) =
      Fin.snoc (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i x) b := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection]
  rw [Fin.succ_castSucc, cubeVertexDegeneracy_snoc]
  simp only [Fin.snoc_castSucc]
  exact (Fin.snoc_update _ _ _ _).symm

end SerrePositivity.KST.SConstruction
