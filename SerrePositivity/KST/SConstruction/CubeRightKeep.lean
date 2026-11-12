module
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeFunctor

/-! # 具体的立方体の右端入力の保持
概要：右端の一座標を保持して元の具体的な射を作用させる操作を構成する。
方針：全生成射の座標を一つずらし、生成条件と恒等・合成を保つことを示す。
規約：右端が座標零で、因子順は変えない。使われ方：立方体の連結積と鎖の tensor 比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の頂点写像に右端の一入力の保持を添える。 -/
def cubeVertexRightKeep {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (m + 1) :=
  fun x => Fin.cons (x 0) (f (fun j => x j.succ))

/-- 右端入力の保持は元の恒等関数を保つ。 -/
lemma cubeVertexRightKeep_id (n : ℕ) :
    cubeVertexRightKeep (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) = _root_.id := by
  funext x
  exact Fin.cons_self_tail x

/-- 右端入力の保持は元の関数合成を保つ。 -/
lemma cubeVertexRightKeep_comp {n m k : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k) :
    cubeVertexRightKeep (g ∘ f) = cubeVertexRightKeep g ∘ cubeVertexRightKeep f := by
  funext x j
  refine Fin.cases rfl (fun j => rfl) j

/-- 右端入力の保持は、元の面の同じ座標を一つずらす。 -/
lemma cubeVertexRightKeep_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    cubeVertexRightKeep (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b (n + 1) i.succ := by
  funext x
  conv_rhs => rw [← Fin.cons_self_tail x]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace, Fin.insertNth_succ_cons, cubeVertexRightKeep]
  rfl

/-- 右端入力の保持は、元の削除の同じ座標を一つずらす。 -/
lemma cubeVertexRightKeep_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    cubeVertexRightKeep (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) i.succ := by
  funext x
  conv_rhs => rw [← Fin.cons_self_tail x]
  rw [cubeVertexDegeneracy_cons]
  rfl

/-- 右端入力の保持は、元の connection の同じ座標を一つずらす。 -/
lemma cubeVertexRightKeep_connection (n : ℕ) (i : Fin (n + 1)) :
    cubeVertexRightKeep (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + 1) i.succ := by
  funext x
  conv_rhs => rw [← Fin.cons_self_tail x]
  rw [cubeVertexConnection_cons]
  rfl

/-- 元の生成関数は右端入力の保持で閉じる。 -/
lemma cubeMapGenerated_rightKeep {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeVertexRightKeep f) := by
  induction h with
  | id n => rw [cubeVertexRightKeep_id]; exact .id _
  | face b n i => rw [cubeVertexRightKeep_face]; exact .face _ _ _
  | degeneracy n i => rw [cubeVertexRightKeep_degeneracy]; exact .degeneracy _ _
  | connection n i => rw [cubeVertexRightKeep_connection]; exact .connection _ _
  | comp hf hg ihf ihg => rw [cubeVertexRightKeep_comp]; exact .comp ihf ihg

/-- 具体的な立方体圏の元の右端入力保持関手。 -/
def concreteCubeRightKeep : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  obj X := ⟨X.dimension + 1⟩
  map f := ⟨cubeVertexRightKeep f.val, cubeMapGenerated_rightKeep f.property⟩
  map_id X := Subtype.ext (cubeVertexRightKeep_id X.dimension)
  map_comp f g := Subtype.ext (cubeVertexRightKeep_comp f.val g.val)

end SerrePositivity.KST.SConstruction
