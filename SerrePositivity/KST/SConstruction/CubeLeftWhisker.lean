module
public import SerrePositivity.KST.SConstruction.CubeLeftKeep

/-! # 有限個の左端入力の保持
概要：左端に任意個の入力を保持した元の立方体の射を構成する。
方針：一座標の左端保持を反復し、元の恒等・合成と生成条件を保持する。
規約：型の次元は元の n+k。使われ方：有限鎖立方体の tensor 比較の自然性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の射の左端に k 個の入力保持を加える。 -/
def cubeVertexLeftWhisker : (k : ℕ) → {n m : ℕ} → (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + k) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (m + k))
  | 0, _, _, f => f
  | k + 1, _, _, f => cubeVertexLeftKeep (cubeVertexLeftWhisker k f)

/-- 有限左端保持は元の生成条件を保つ。 -/
lemma cubeMapGenerated_leftWhisker (k : ℕ) {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeVertexLeftWhisker k f) := by
  induction k with
  | zero => exact h
  | succ k ih => exact cubeMapGenerated_leftKeep ih

/-- 有限左端保持は元の恒等写像を保つ。 -/
lemma cubeVertexLeftWhisker_id (k n : ℕ) :
    cubeVertexLeftWhisker k (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) = _root_.id := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change cubeVertexLeftKeep (cubeVertexLeftWhisker k _root_.id) = _
    rw [ih, cubeVertexLeftKeep_id]

/-- 有限左端保持は元の写像合成を保つ。 -/
lemma cubeVertexLeftWhisker_comp (k : ℕ) {n m l : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex l) :
    cubeVertexLeftWhisker k (g ∘ f) =
      cubeVertexLeftWhisker k g ∘ cubeVertexLeftWhisker k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change cubeVertexLeftKeep (cubeVertexLeftWhisker k (g ∘ f)) = _
    rw [ih, cubeVertexLeftKeep_comp]
    rfl

/-- 元の具体的立方体圏での有限左端保持関手。 -/
def concreteCubeLeftWhisker (k : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  obj X := ⟨X.dimension + k⟩
  map f := ⟨cubeVertexLeftWhisker k f.val, cubeMapGenerated_leftWhisker k f.property⟩
  map_id X := Subtype.ext (cubeVertexLeftWhisker_id k X.dimension)
  map_comp f g := Subtype.ext (cubeVertexLeftWhisker_comp k f.val g.val)

/-- 零個の左端保持は元の具体的な射。 -/
lemma concreteCubeLeftWhisker_zero_map {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    (concreteCubeLeftWhisker 0).map f = f := rfl

/-- 一個増やす更新は元の左端保持の後合成。 -/
lemma concreteCubeLeftWhisker_succ_map (k : ℕ) {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    (concreteCubeLeftWhisker (k + 1)).map f =
      concreteCubeLeftKeep.map ((concreteCubeLeftWhisker k).map f) := rfl

end SerrePositivity.KST.SConstruction
