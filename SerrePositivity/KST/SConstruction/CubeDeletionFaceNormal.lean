module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceDeletionResult

/-! # 削除・面の二段標準表示と生成射の後合成
概要：削除と面の標準表示を束ね、元の面または削除の追加を同じ二段表示へ戻す。
方針：面の後の一出力削除の計算結果を、既存の削除標準表示へ吸収する。
規約：中間次元を明示する。使われ方：面・削除の混合語の正規化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の入力削除と定数面の二段標準表示。 -/
structure CubeDeletionFaceNormal (n m : ℕ) where
  middle : ℕ
  deletion : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n middle
  face : CubeFaceNormal middle m

/-- 二段標準表示の元の全頂点での評価。 -/
def cubeDeletionFaceNormalVertex {n m : ℕ} (r : CubeDeletionFaceNormal n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  cubeFaceNormalVertex r.face ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex r.deletion

/-- 元の恒等射の二段標準表示。 -/
def cubeDeletionFaceNormalId (n : ℕ) : CubeDeletionFaceNormal n n :=
  ⟨n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n, cubeFaceNormalId n⟩

/-- 元の恒等射の二段表示は、全頂点で恒等。 -/
lemma cubeDeletionFaceNormalId_vertex (n : ℕ) :
    cubeDeletionFaceNormalVertex (cubeDeletionFaceNormalId n) = _root_.id := by
  dsimp only [cubeDeletionFaceNormalId, cubeDeletionFaceNormalVertex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex]
  rw [cubeFaceNormalId_vertex, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId_embedding]
  rfl

/-- 元の二段表示へ任意座標の面を追加する。 -/
def cubeDeletionFaceNormalPoint {n m : ℕ} (r : CubeDeletionFaceNormal n m)
    (b : Bool) (i : Fin (m + 1)) : CubeDeletionFaceNormal n (m + 1) :=
  ⟨r.middle, r.deletion, cubeFaceNormalInsert r.face b i⟩

/-- 面の追加は、元の全頂点で同じ面の後合成を回収する。 -/
lemma cubeDeletionFaceNormalPoint_vertex {n m : ℕ} (r : CubeDeletionFaceNormal n m)
    (b : Bool) (i : Fin (m + 1)) :
    cubeDeletionFaceNormalVertex (cubeDeletionFaceNormalPoint r b i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b m i ∘ cubeDeletionFaceNormalVertex r := by
  dsimp only [cubeDeletionFaceNormalVertex, cubeDeletionFaceNormalPoint]
  rw [cubeFaceNormalInsert_vertex]
  rfl

/-- 高々一つの入力削除を、元の削除の標準表示へ吸収する。 -/
def cubeDeletionFaceNormalAfterResult {n : ℕ} : {a m : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a →
    CubeFaceDeletionResult a m → CubeDeletionFaceNormal n m
  | _, _, d, .pure f => ⟨_, d, f⟩
  | _, _, d, .input i f => ⟨_, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i, f⟩

/-- 入力削除の吸収は、元の全頂点で同じ計算結果との合成を回収する。 -/
lemma cubeDeletionFaceNormalAfterResult_vertex {n a m : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (r : CubeFaceDeletionResult a m) :
    cubeDeletionFaceNormalVertex (cubeDeletionFaceNormalAfterResult d r) =
      cubeFaceDeletionResultVertex r ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d := by
  cases r with
  | pure f => rfl
  | input i f =>
    change cubeFaceNormalVertex f ∘
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase d i) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex_erase]
    rfl

/-- 元の二段表示へ任意座標の一出力削除を追加して正規化する。 -/
def cubeDeletionFaceNormalDelete {n m : ℕ} (r : CubeDeletionFaceNormal n (m + 1))
    (i : Fin (m + 1)) : CubeDeletionFaceNormal n m :=
  cubeDeletionFaceNormalAfterResult r.deletion (cubeFaceNormalDelete r.face i)

/-- 一出力削除の正規化は、元の全頂点で同じ削除の後合成を回収する。 -/
lemma cubeDeletionFaceNormalDelete_vertex {n m : ℕ} (r : CubeDeletionFaceNormal n (m + 1))
    (i : Fin (m + 1)) :
    cubeDeletionFaceNormalVertex (cubeDeletionFaceNormalDelete r i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy m i ∘ cubeDeletionFaceNormalVertex r := by
  dsimp only [cubeDeletionFaceNormalDelete]
  rw [cubeDeletionFaceNormalAfterResult_vertex, cubeFaceNormalDelete_vertex]
  rfl

end SerrePositivity.KST.SConstruction
