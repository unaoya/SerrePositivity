module
public import SerrePositivity.KST.SConstruction.CubeConnectionPathIndependence

/-! # 面の後の削除を入力側へ移す計算結果
概要：面の残余、または一つの入力削除と面の残余を、元の次元を保つ型で表す。
方針：定数出力の追加と入力保持を結果に作用させ、元の頂点関数で評価する。
規約：入力削除は高々一つ。使われ方：混合語を削除・max・面へ移す第一工程。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 面の後の削除を入力側へ移した、次元を保つ結果。 -/
inductive CubeFaceDeletionResult : ℕ → ℕ → Type
  | pure {n m : ℕ} (d : CubeFaceNormal n m) : CubeFaceDeletionResult n m
  | input {n m : ℕ} (i : Fin (n + 1)) (d : CubeFaceNormal n m) :
      CubeFaceDeletionResult (n + 1) m

/-- 計算結果の元の頂点関数による評価。 -/
def cubeFaceDeletionResultVertex : {n m : ℕ} → CubeFaceDeletionResult n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, _, .pure d => cubeFaceNormalVertex d
  | _, _, .input i d => cubeFaceNormalVertex d ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i

/-- 計算結果の最初の出力へ元の定数を追加する。 -/
def cubeFaceDeletionResultPoint {n m : ℕ} (b : Bool) :
    CubeFaceDeletionResult n m → CubeFaceDeletionResult n (m + 1)
  | .pure d => .pure (.point b d)
  | .input i d => .input i (.point b d)

/-- 計算結果へ元の右端入力の保持を追加する。 -/
def cubeFaceDeletionResultKeep {n m : ℕ} :
    CubeFaceDeletionResult n m → CubeFaceDeletionResult (n + 1) (m + 1)
  | .pure d => .pure (.keep d)
  | .input i d => .input i.succ (.keep d)

/-- 内側の座標の削除は、元の右端の値を保ち、残りへ同じ削除を作用させる。 -/
lemma cubeVertexDegeneracy_cons (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) i.succ (Fin.cons b x) =
      Fin.cons b (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]

/-- 結果への定数の追加は、元の評価へ同じ定数を追加する。 -/
lemma cubeFaceDeletionResultPoint_vertex {n m : ℕ} (b : Bool)
    (r : CubeFaceDeletionResult n m) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    cubeFaceDeletionResultVertex (cubeFaceDeletionResultPoint b r) x =
      Fin.cons b (cubeFaceDeletionResultVertex r x) := by
  cases r <;> rfl

/-- 結果への入力保持の追加は、元の評価へ同じ右端入力を保持する。 -/
lemma cubeFaceDeletionResultKeep_vertex {n m : ℕ} (r : CubeFaceDeletionResult n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeFaceDeletionResultVertex (cubeFaceDeletionResultKeep r) x =
      Fin.cons (x 0) (cubeFaceDeletionResultVertex r (fun j => x j.succ)) := by
  cases r with
  | pure d => rfl
  | input i d =>
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [cubeFaceDeletionResultVertex, cubeFaceDeletionResultKeep, cubeFaceNormalVertex,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
    · simp [cubeFaceDeletionResultVertex, cubeFaceDeletionResultKeep, cubeFaceNormalVertex,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]
      rfl

end SerrePositivity.KST.SConstruction
