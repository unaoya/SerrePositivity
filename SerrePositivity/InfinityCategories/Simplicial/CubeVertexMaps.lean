module
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-! # 具体的な立方体の頂点と三つの生成射
概要：Bool の有限積上で、二端点挿入・座標削除・隣接 max の元の関数を定義する。
方針：Fin の挿入・座標を飛ばす写像・更新を使い、pointwise join の保存を証明する。
規約：座標は右端から数える。使われ方：max connection を持つ具体的な立方体圏。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- n 次元の具体的な立方体の頂点。 -/
abbrev CubeVertex (n : ℕ) := Fin n → Bool

/-- 指定座標への元の端点の挿入。 -/
def cubeVertexFace (b : Bool) (n : ℕ) (i : Fin (n + 1)) : CubeVertex n → CubeVertex (n + 1) :=
  Fin.insertNth (α := fun _ => Bool) i b

/-- 指定座標を削除する元の射。 -/
def cubeVertexDegeneracy (n : ℕ) (i : Fin (n + 1)) : CubeVertex (n + 1) → CubeVertex n :=
  fun x j => x (i.succAbove j)

/-- 指定した隣接二座標を max で結合する元の射。 -/
def cubeVertexConnection (n : ℕ) (i : Fin (n + 1)) : CubeVertex (n + 2) → CubeVertex (n + 1) :=
  fun x => Function.update (cubeVertexDegeneracy (n + 1) i.succ x) i
    (x i.castSucc ⊔ x i.succ)

/-- 端点挿入は元の全頂点の pointwise join を保つ。 -/
lemma cubeVertexFace_sup (b : Bool) (n : ℕ) (i : Fin (n + 1)) (x y : CubeVertex n) :
    cubeVertexFace b n i (x ⊔ y) = cubeVertexFace b n i x ⊔ cubeVertexFace b n i y := by
  funext k
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · simp [cubeVertexFace]
  · simp [cubeVertexFace]

/-- 座標削除は元の全頂点の pointwise join を保つ。 -/
lemma cubeVertexDegeneracy_sup (n : ℕ) (i : Fin (n + 1)) (x y : CubeVertex (n + 1)) :
    cubeVertexDegeneracy n i (x ⊔ y) = cubeVertexDegeneracy n i x ⊔ cubeVertexDegeneracy n i y :=
  rfl

/-- 隣接 max は元の全頂点の pointwise join を保つ。 -/
lemma cubeVertexConnection_sup (n : ℕ) (i : Fin (n + 1)) (x y : CubeVertex (n + 2)) :
    cubeVertexConnection n i (x ⊔ y) =
      cubeVertexConnection n i x ⊔ cubeVertexConnection n i y := by
  funext k
  by_cases h : k = i
  · subst k
    simp only [cubeVertexConnection, Function.update_self, Pi.sup_apply]
    exact sup_sup_sup_comm _ _ _ _
  · simp [cubeVertexConnection, h, cubeVertexDegeneracy]

end SerrePositivity.KST.SConstruction
