module
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionNormal

/-! # 元の max の式の標準化と Serre 評価の保存
概要：隣接 max を順に合成した任意の式をブロック標準表示へ移し、元の二評価を回収する。
方針：任意座標の一結合との照合を各構文に適用する。
規約：同じ具体的な頂点関数から元の Serre 射の等号を結論する。
使われ方：元の生成語の圏の max のみの語への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の隣接 max を順に合成した式。 -/
inductive CubeConnectionExpression : ℕ → ℕ → Type
  | id (n : ℕ) : CubeConnectionExpression n n
  | connect {n m : ℕ} (p : CubeConnectionExpression n (m + 2)) (i : Fin (m + 1)) :
      CubeConnectionExpression n (m + 1)

/-- 元の max の式を具体的な頂点関数へ評価する。 -/
def cubeConnectionExpressionVertex {n : ℕ} : {m : ℕ} → CubeConnectionExpression n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, .id _ => _root_.id
  | _, .connect p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeConnectionExpressionVertex p
termination_by structural _m p => p

/-- 元の max の式をブロック標準表示へ移す。 -/
def cubeConnectionExpressionNormal {n : ℕ} : {m : ℕ} → CubeConnectionExpression n m →
    CubeConnectionNormal n m
  | _, .id _ => cubeConnectionNormalId n
  | _, .connect p i => cubeConnectionNormalConnect (cubeConnectionExpressionNormal p) i
termination_by structural _m p => p

/-- max の式の標準化は、元の全頂点での関数を厳密に保存する。 -/
lemma cubeConnectionExpressionNormal_vertex {n m : ℕ} (p : CubeConnectionExpression n m) :
    cubeConnectionNormalVertex (cubeConnectionExpressionNormal p) =
      cubeConnectionExpressionVertex p := by
  induction p with
  | id => exact cubeConnectionNormalId_vertex n
  | connect p i ih =>
    change cubeConnectionNormalVertex
      (cubeConnectionNormalConnect (cubeConnectionExpressionNormal p) i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeConnectionExpressionVertex p
    rw [cubeConnectionNormalVertex_connect, ih]

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の max の式を、元の Serre 余モノイド射へ評価する。 -/
def serreCubeConnectionExpression {n : ℕ} : {m : ℕ} → CubeConnectionExpression n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, .id _ => 𝟙 _
  | _, .connect p i => serreCubeConnectionExpression p ≫ serreCubeConnection A _ i
termination_by structural _m p => p

/-- max の式の標準化は、元の Serre 評価そのものを厳密に保存する。 -/
lemma serreCubeConnectionExpressionNormal {n m : ℕ} (p : CubeConnectionExpression n m) :
    serreCubeConnectionNormal A (cubeConnectionExpressionNormal p) =
      serreCubeConnectionExpression A p := by
  induction p with
  | id => exact serreCubeConnectionNormal_id A n
  | connect p i ih =>
    change serreCubeConnectionNormal A
      (cubeConnectionNormalConnect (cubeConnectionExpressionNormal p) i) =
        serreCubeConnectionExpression A p ≫ serreCubeConnection A _ i
    rw [serreCubeConnectionNormal_connect, ih]

/-- 同じ具体的な頂点関数を表す max の式の元の Serre 評価は一致する。 -/
lemma serreCubeConnectionExpression_eq_of_vertex_eq {n m : ℕ}
    (p q : CubeConnectionExpression n m)
    (h : cubeConnectionExpressionVertex p = cubeConnectionExpressionVertex q) :
    serreCubeConnectionExpression A p = serreCubeConnectionExpression A q := by
  have hn : cubeConnectionExpressionNormal p = cubeConnectionExpressionNormal q :=
    cubeConnectionNormalVertex_injective n m ((cubeConnectionExpressionNormal_vertex p).trans
      (h.trans (cubeConnectionExpressionNormal_vertex q).symm))
  rw [← serreCubeConnectionExpressionNormal, ← serreCubeConnectionExpressionNormal, hn]

end SerrePositivity.KST.SConstruction
