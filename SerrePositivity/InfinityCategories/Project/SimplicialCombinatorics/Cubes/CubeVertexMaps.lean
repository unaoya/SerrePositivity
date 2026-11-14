module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-! # 具体的な立方体の頂点と三つの生成射
概要：Bool の有限積上で、二端点挿入・座標削除・隣接 max の元の関数を定義する。
方針：Fin の挿入・座標を飛ばす写像・更新を使い、pointwise join の保存を証明する。
規約：座標は右端から数える。使われ方：max connection を持つ具体的な立方体圏。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- n 次元の具体的な立方体の頂点。 -/
abbrev CubeVertex (n : ℕ) := Fin n → Bool

/-- 指定座標への元の端点の挿入。 -/
def cubeVertexFace (b : Bool) (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1) :=
  Fin.insertNth (α := fun _ => Bool) i b

/-- 指定座標を削除する元の射。 -/
def cubeVertexDegeneracy (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n :=
  fun x j => x (i.succAbove j)

/-- 指定した隣接二座標を max で結合する元の射。 -/
def cubeVertexConnection (n : ℕ) (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2) → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1) :=
  fun x => Function.update (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (n + 1) i.succ x) i
    (x i.castSucc ⊔ x i.succ)

/-- 端点挿入は元の全頂点の pointwise join を保つ。 -/
lemma cubeVertexFace_sup (b : Bool) (n : ℕ) (i : Fin (n + 1)) (x y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i (x ⊔ y) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i x ⊔ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b n i y := by
  funext k
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace]
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace]

/-- 座標削除は元の全頂点の pointwise join を保つ。 -/
lemma cubeVertexDegeneracy_sup (n : ℕ) (i : Fin (n + 1)) (x y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i (x ⊔ y) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i x ⊔ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n i y :=
  rfl

/-- 隣接 max は元の全頂点の pointwise join を保つ。 -/
lemma cubeVertexConnection_sup (n : ℕ) (i : Fin (n + 1)) (x y : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i (x ⊔ y) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i x ⊔ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection n i y := by
  funext k
  by_cases h : k = i
  · subst k
    simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, Function.update_self, Pi.sup_apply]
    exact sup_sup_sup_comm _ _ _ _
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection, h, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeVertex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexConnection := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexConnection_sup := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection_sup

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexDegeneracy := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexDegeneracy_sup := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy_sup

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexFace := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexFace_sup := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace_sup

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexConnection.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexDegeneracy.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeVertexFace.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace.eq_1
