module
public import SerrePositivity.KST.SConstruction.CubeLeftKeepCoordinates

/-! # 具体的立方体の左端入力の保持
概要：左端の一座標を保持して元の具体的な射を作用させる関手を構成する。
方針：最大座標の snoc と元の全生成射の交換を使う。
規約：右端の座標零は移さない。使われ方：具体的立方体の連結積の左 tensor 作用。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の頂点写像に左端の一入力の保持を添える。 -/
def cubeVertexLeftKeep {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (m + 1) :=
  fun x => Fin.snoc (f (fun j => x j.castSucc)) (x (Fin.last n))

/-- 左端入力の保持は元の恒等関数を保つ。 -/
lemma cubeVertexLeftKeep_id (n : ℕ) :
    cubeVertexLeftKeep (_root_.id : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) = _root_.id := by
  funext x
  exact Fin.snoc_init_self x

/-- 左端入力の保持は元の関数合成を保つ。 -/
lemma cubeVertexLeftKeep_comp {n m k : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex k) :
    cubeVertexLeftKeep (g ∘ f) = cubeVertexLeftKeep g ∘ cubeVertexLeftKeep f := by
  funext x j
  refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [cubeVertexLeftKeep, Function.comp_apply, Fin.snoc_last, Fin.snoc_castSucc]

/-- 左端入力の保持は、元の面の低い座標を保つ。 -/
lemma cubeVertexLeftKeep_face (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    cubeVertexLeftKeep (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b (n + 1) i.castSucc := by
  funext x
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [cubeVertexFace_snoc]
  rfl

/-- 左端入力の保持は、元の削除の低い座標を保つ。 -/
lemma cubeVertexLeftKeep_degeneracy (n : ℕ) (i : Fin (n + 1)) :
    cubeVertexLeftKeep (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) i.castSucc := by
  funext x
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [cubeVertexDegeneracy_snoc]
  rfl

/-- 左端入力の保持は、元の connection の低い座標を保つ。 -/
lemma cubeVertexLeftKeep_connection (n : ℕ) (i : Fin (n + 1)) :
    cubeVertexLeftKeep (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + 1) i.castSucc := by
  funext x
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [cubeVertexConnection_snoc]
  rfl

/-- 元の生成関数は左端入力の保持で閉じる。 -/
lemma cubeMapGenerated_leftKeep {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated f) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (cubeVertexLeftKeep f) := by
  induction h with
  | id n => rw [cubeVertexLeftKeep_id]; exact .id _
  | face b n i => rw [cubeVertexLeftKeep_face]; exact .face _ _ _
  | degeneracy n i => rw [cubeVertexLeftKeep_degeneracy]; exact .degeneracy _ _
  | connection n i => rw [cubeVertexLeftKeep_connection]; exact .connection _ _
  | comp hf hg ihf ihg => rw [cubeVertexLeftKeep_comp]; exact .comp ihf ihg

/-- 具体的な立方体圏の元の左端入力保持関手。 -/
def concreteCubeLeftKeep : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube ⥤ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube where
  obj X := ⟨X.dimension + 1⟩
  map f := ⟨cubeVertexLeftKeep f.val, cubeMapGenerated_leftKeep f.property⟩
  map_id X := Subtype.ext (cubeVertexLeftKeep_id X.dimension)
  map_comp f g := Subtype.ext (cubeVertexLeftKeep_comp f.val g.val)

end SerrePositivity.KST.SConstruction
