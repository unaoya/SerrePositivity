module
public import SerrePositivity.KST.SConstruction.CubeConnectionDeletionPathNormalization

/-! # 面の後の connection を入力側へ移す計算結果
概要：面の残余、または一入力削除・一入力結合と面の残余を次元を保つ型で表す。
方針：元の入力の順序を保ち、定数出力と入力保持を結果に作用させる。
規約：一回の connection で必要な入力操作は高々一つ。使われ方：混合語の三段正規化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 面の後の一 connection を移した、次元を保つ結果。 -/
inductive CubeFaceConnectionResult : ℕ → ℕ → Type
  | pure {n m : ℕ} (d : CubeFaceNormal n m) : CubeFaceConnectionResult n m
  | input {n m : ℕ} (i : Fin (n + 1)) (d : CubeFaceNormal n m) :
      CubeFaceConnectionResult (n + 1) m
  | connect {n m : ℕ} (i : Fin (n + 1)) (d : CubeFaceNormal (n + 1) m) :
      CubeFaceConnectionResult (n + 2) m

/-- 計算結果の元の頂点関数による評価。 -/
def cubeFaceConnectionResultVertex : {n m : ℕ} → CubeFaceConnectionResult n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, _, .pure d => cubeFaceNormalVertex d
  | _, _, .input i d => cubeFaceNormalVertex d ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i
  | _, _, .connect i d => cubeFaceNormalVertex d ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i

/-- 計算結果の元の先頭出力へ定数を追加する。 -/
def cubeFaceConnectionResultPoint {n m : ℕ} (b : Bool) :
    CubeFaceConnectionResult n m → CubeFaceConnectionResult n (m + 1)
  | .pure d => .pure (.point b d)
  | .input i d => .input i (.point b d)
  | .connect i d => .connect i (.point b d)

/-- 計算結果へ元の右端入力の保持を追加する。 -/
def cubeFaceConnectionResultKeep {n m : ℕ} :
    CubeFaceConnectionResult n m → CubeFaceConnectionResult (n + 1) (m + 1)
  | .pure d => .pure (.keep d)
  | .input i d => .input i.succ (.keep d)
  | .connect i d => .connect i.succ (.keep d)

/-- 元の右端座標削除は、そのまま入力列の tail を回収する。 -/
@[simp]
lemma cubeVertexDegeneracy_zero (n : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n 0 x = fun j => x j.succ := rfl

/-- 内側の connection は、元の右端の値を保ち、残りへ同じ connection を作用させる。 -/
lemma cubeVertexConnection_cons (n : ℕ) (i : Fin (n + 1)) (b : Bool)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (n + 1) i.succ (Fin.cons b x) =
      Fin.cons b (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · have hz : (0 : Fin (n + 2)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy, hz]
  · by_cases hj : j = i
    · subst j
      simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, Fin.castSucc_succ]
    · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy, hj, Fin.castSucc_succ]

/-- 計算結果への定数の追加は、元の評価へ同じ定数を追加する。 -/
lemma cubeFaceConnectionResultPoint_vertex {n m : ℕ} (b : Bool)
    (r : CubeFaceConnectionResult n m) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    cubeFaceConnectionResultVertex (cubeFaceConnectionResultPoint b r) x =
      Fin.cons b (cubeFaceConnectionResultVertex r x) := by
  cases r <;> rfl

/-- 計算結果への入力保持は、元の右端入力と残りの評価を回収する。 -/
lemma cubeFaceConnectionResultKeep_vertex {n m : ℕ} (r : CubeFaceConnectionResult n m)
    (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    cubeFaceConnectionResultVertex (cubeFaceConnectionResultKeep r) x =
      Fin.cons (x 0) (cubeFaceConnectionResultVertex r (fun j => x j.succ)) := by
  cases r with
  | pure d => rfl
  | input i d =>
    have hx : x = Fin.cons (x 0) (fun j => x j.succ) := (Fin.cons_self_tail x).symm
    rw [hx]
    simp only [cubeFaceConnectionResultVertex, cubeFaceConnectionResultKeep, cubeFaceNormalVertex,
      Function.comp_apply, cubeVertexDegeneracy_cons, Fin.cons_zero, Fin.cons_succ]
  | connect i d =>
    have hx : x = Fin.cons (x 0) (fun j => x j.succ) := (Fin.cons_self_tail x).symm
    rw [hx]
    simp only [cubeFaceConnectionResultVertex, cubeFaceConnectionResultKeep, cubeFaceNormalVertex,
      Function.comp_apply, cubeVertexConnection_cons, Fin.cons_zero, Fin.cons_succ]

end SerrePositivity.KST.SConstruction
