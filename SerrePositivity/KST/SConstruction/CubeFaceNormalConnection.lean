module
public import SerrePositivity.KST.SConstruction.CubeFaceConnectionResult

/-! # 面の標準表示の後の一 connection の正規化
概要：隣接二出力の定数・保持を判定し、高々一つの入力削除または入力結合へ移す。
方針：右端で単位・吸収・二入力結合を分け、残りの座標では出力次元で帰納する。
規約：元の頂点関数の合成を厳密に回収する。使われ方：一般の混合語の三段正規化。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 面の最初の二出力の max を、必要な入力操作と残余の面へ移す。 -/
def cubeFaceNormalConnectZero : {n m : ℕ} → CubeFaceNormal n (m + 2) →
    CubeFaceConnectionResult n (m + 1)
  | _, _, .point false d => .pure d
  | _, _, .point true (.point _ d) => .pure (.point true d)
  | _, _, .point true (.keep d) => .input 0 (.point true d)
  | _, _, .keep (.point false d) => .pure (.keep d)
  | _, _, .keep (.point true d) => .input 0 (.point true d)
  | _, _, .keep (.keep d) => .connect 0 (.keep d)

/-- 元の右端 connection の正規化は、同じ全頂点の評価を回収する。 -/
lemma cubeFaceNormalConnectZero_vertex {n m : ℕ} (d : CubeFaceNormal n (m + 2)) :
    cubeFaceConnectionResultVertex (cubeFaceNormalConnectZero d) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m 0 ∘ cubeFaceNormalVertex d := by
  cases d with
  | point b d =>
    cases b with
    | false =>
      funext x j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [cubeFaceNormalConnectZero, cubeFaceConnectionResultVertex, cubeFaceNormalVertex,
          cubeVertexConnection_zero]
    | true =>
      cases d with
      | point c d =>
        funext x j
        refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [cubeFaceNormalConnectZero, cubeFaceConnectionResultVertex, cubeFaceNormalVertex,
            cubeVertexConnection_zero]
      | keep d =>
        funext x j
        refine Fin.cases ?_ (fun j => ?_) j <;>
          simp [cubeFaceNormalConnectZero, cubeFaceConnectionResultVertex, cubeFaceNormalVertex,
            cubeVertexConnection_zero]
  | keep d =>
    cases d with
    | point b d =>
      cases b <;> funext x j <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [cubeFaceNormalConnectZero, cubeFaceConnectionResultVertex, cubeFaceNormalVertex,
          cubeVertexConnection_zero]
    | keep d =>
      funext x j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [cubeFaceNormalConnectZero, cubeFaceConnectionResultVertex, cubeFaceNormalVertex,
          cubeVertexConnection_zero]

/-- 面の任意の隣接二出力の max を、必要な入力操作と残余の面へ移す。 -/
def cubeFaceNormalConnect : {n m : ℕ} → CubeFaceNormal n (m + 2) →
    Fin (m + 1) → CubeFaceConnectionResult n (m + 1)
  | _, 0, d, _ => cubeFaceNormalConnectZero d
  | _, _ + 1, .point b d, i => Fin.cases (cubeFaceNormalConnectZero (.point b d))
      (fun j => cubeFaceConnectionResultPoint b (cubeFaceNormalConnect d j)) i
  | _, _ + 1, .keep d, i => Fin.cases (cubeFaceNormalConnectZero (.keep d))
      (fun j => cubeFaceConnectionResultKeep (cubeFaceNormalConnect d j)) i

/-- 元の一 connection の正規化は、同じ全頂点の関数合成を回収する。 -/
lemma cubeFaceNormalConnect_vertex {n m : ℕ} (d : CubeFaceNormal n (m + 2))
    (i : Fin (m + 1)) :
    cubeFaceConnectionResultVertex (cubeFaceNormalConnect d i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i ∘ cubeFaceNormalVertex d := by
  induction m generalizing n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact cubeFaceNormalConnectZero_vertex d
  | succ m ih =>
    cases d with
    | point b d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · exact cubeFaceNormalConnectZero_vertex _
      · funext x
        change cubeFaceConnectionResultVertex
          (cubeFaceConnectionResultPoint b (cubeFaceNormalConnect d i)) x = _
        rw [cubeFaceConnectionResultPoint_vertex, ih d i]
        change Fin.cons (α := fun _ => Bool) b
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i (cubeFaceNormalVertex d x)) = _
        simp only [Function.comp_apply, cubeFaceNormalVertex, cubeVertexConnection_cons]
    | keep d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · exact cubeFaceNormalConnectZero_vertex _
      · funext x
        change cubeFaceConnectionResultVertex
          (cubeFaceConnectionResultKeep (cubeFaceNormalConnect d i)) x = _
        rw [cubeFaceConnectionResultKeep_vertex, ih d i]
        change Fin.cons (α := fun _ => Bool) (x 0)
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection m i (cubeFaceNormalVertex d (fun j => x j.succ))) = _
        simp only [Function.comp_apply, cubeFaceNormalVertex, cubeVertexConnection_cons]

end SerrePositivity.KST.SConstruction
