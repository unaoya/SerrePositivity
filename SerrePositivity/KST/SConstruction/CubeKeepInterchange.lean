module
public import SerrePositivity.KST.SConstruction.CubeLeftWhisker
public import SerrePositivity.KST.SConstruction.CubeRightWhisker

/-! # 左右の元の一座標保持の交換
概要：元の頂点写像に左右の一座標を加える二つの順序が厳密に一致することを示す。
方針：右端の cons と左端の snoc の元の交換式を使う。
規約：入力も出力も元の順序を保持する。使われ方：立方体の二変数の連結作用。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 左右の一座標保持の二つの順序は、元の頂点写像として厳密に一致する。 -/
lemma cubeVertexKeep_interchange {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    cubeVertexLeftKeep (cubeVertexRightKeep f) =
      cubeVertexRightKeep (cubeVertexLeftKeep f) := by
  funext x
  exact (Fin.cons_snoc_eq_snoc_cons (x 0) (f (fun j => x j.succ.castSucc))
    (x (Fin.last (n + 1)))).symm

end SerrePositivity.KST.SConstruction
