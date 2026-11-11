module
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensor

/-! # 具体的連結積の右恒等因子と元の有限保持
概要：連結積の右因子を恒等にした射が、元の有限右端保持の射そのものであることを示す。
方針：全ての元の連結頂点で両評価を回収する。
規約：左右の因子を交換しない。使われ方：鎖の有限右端保持の自然性と連結積の接続。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の有限右端保持は、連結した全頂点で右側の頂点を固定する。 -/
lemma cubeVertexRightWhisker_join (k : ℕ) {n p : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) (y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k) :
    cubeVertexRightWhisker k f (cubeVertexJoin x y) = cubeVertexJoin (f x) y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg (fun v : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex _ => Fin.cons (α := fun _ => Bool) (y 0) v)
      (ih (fun j => y j.succ))

/-- 元の有限右端保持は、右ブロックを恒等とする元の二ブロック作用。 -/
lemma cubeVertexRightWhisker_tensor (k : ℕ) {n p : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex p) :
    cubeVertexRightWhisker k f =
      cubeVertexTensor f (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k) :=
  cubeVertexTensor_eq_of_join _ _ _ (cubeVertexRightWhisker_join k f)

/-- 連結積の右因子が恒等のとき、元の有限右端保持の射を厳密に回収する。 -/
lemma concreteCubeTensorMap_id_right {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) (k : ℕ) :
    concreteCubeTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k)) = (concreteCubeRightWhisker k).map f :=
  Subtype.ext (cubeVertexRightWhisker_tensor k f.val).symm

end SerrePositivity.KST.SConstruction
