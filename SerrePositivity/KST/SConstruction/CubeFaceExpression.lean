module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceNormal

/-! # 元の面の式の標準化と Serre 評価の保存
概要：面を順に合成した任意の式を定数・保持標準表示へ移し、元の二つの評価を回収する。
方針：任意座標の一面挿入との照合を各構文に適用する。
規約：同じ具体的な頂点関数から元の Serre 射の等号を結論する。
使われ方：元の生成語の圏の面のみの語への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の二端点の面を順に合成した式。 -/
inductive CubeFaceExpression : ℕ → ℕ → Type
  | id (n : ℕ) : CubeFaceExpression n n
  | point {n m : ℕ} (p : CubeFaceExpression n m) (b : Bool) (i : Fin (m + 1)) :
      CubeFaceExpression n (m + 1)

/-- 元の面の式を具体的な頂点関数へ評価する。 -/
def cubeFaceExpressionVertex {n : ℕ} : {m : ℕ} → CubeFaceExpression n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, .id _ => _root_.id
  | _, .point p b i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeFaceExpressionVertex p
termination_by structural _m p => p

/-- 元の面の式を定数・保持標準表示へ移す。 -/
def cubeFaceExpressionNormal {n : ℕ} : {m : ℕ} → CubeFaceExpression n m → CubeFaceNormal n m
  | _, .id _ => cubeFaceNormalId n
  | _, .point p b i => cubeFaceNormalInsert (cubeFaceExpressionNormal p) b i
termination_by structural _m p => p

/-- 面の式の標準化は、元の全頂点での関数を厳密に保存する。 -/
lemma cubeFaceExpressionNormal_vertex {n m : ℕ} (p : CubeFaceExpression n m) :
    cubeFaceNormalVertex (cubeFaceExpressionNormal p) = cubeFaceExpressionVertex p := by
  induction p with
  | id => exact cubeFaceNormalId_vertex n
  | point p b i ih =>
    change cubeFaceNormalVertex (cubeFaceNormalInsert (cubeFaceExpressionNormal p) b i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeFaceExpressionVertex p
    rw [cubeFaceNormalInsert_vertex, ih]

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の面の式を、元の Serre 余モノイド射へ評価する。 -/
def serreCubeFaceExpression {n : ℕ} : {m : ℕ} → CubeFaceExpression n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, .id _ => 𝟙 _
  | _, .point p b i => serreCubeFaceExpression p ≫ serreCubeFace A b _ i
termination_by structural _m p => p

/-- 面の式の標準化は、元の Serre 評価そのものを厳密に保存する。 -/
lemma serreCubeFaceExpressionNormal {n m : ℕ} (p : CubeFaceExpression n m) :
    serreCubeFaceNormal A (cubeFaceExpressionNormal p) = serreCubeFaceExpression A p := by
  induction p with
  | id => exact serreCubeFaceNormal_id A n
  | point p b i ih =>
    change serreCubeFaceNormal A (cubeFaceNormalInsert (cubeFaceExpressionNormal p) b i) =
      serreCubeFaceExpression A p ≫ serreCubeFace A b _ i
    rw [serreCubeFaceNormal_insert, ih]

/-- 同じ具体的な頂点関数を表す面の式の元の Serre 評価は一致する。 -/
lemma serreCubeFaceExpression_eq_of_vertex_eq {n m : ℕ} (p q : CubeFaceExpression n m)
    (h : cubeFaceExpressionVertex p = cubeFaceExpressionVertex q) :
    serreCubeFaceExpression A p = serreCubeFaceExpression A q := by
  have hn : cubeFaceExpressionNormal p = cubeFaceExpressionNormal q :=
    cubeFaceNormalVertex_injective n m ((cubeFaceExpressionNormal_vertex p).trans
      (h.trans (cubeFaceExpressionNormal_vertex q).symm))
  rw [← serreCubeFaceExpressionNormal, ← serreCubeFaceExpressionNormal, hn]

end SerrePositivity.KST.SConstruction
