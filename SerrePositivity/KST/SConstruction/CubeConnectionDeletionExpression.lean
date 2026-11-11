module
public import SerrePositivity.KST.SConstruction.CubeDeletionConnectionUpdates

/-! # max・削除が混在する元の式の二段正規化
概要：元の隣接 max と削除が任意に交互に現れる式を、削除・max の二段表示へ移す。
方針：各構文の後合成を、元の二つの評価を保つ更新へ移す。
規約：面を含む語への拡張は別工程。使われ方：混合語の段階的正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の隣接 max と削除を任意に交互に合成した式。 -/
inductive CubeConnectionDeletionExpression : ℕ → ℕ → Type
  | id (n : ℕ) : CubeConnectionDeletionExpression n n
  | connect {n m : ℕ} (p : CubeConnectionDeletionExpression n (m + 2)) (i : Fin (m + 1)) :
      CubeConnectionDeletionExpression n (m + 1)
  | erase {n m : ℕ} (p : CubeConnectionDeletionExpression n (m + 1)) (i : Fin (m + 1)) :
      CubeConnectionDeletionExpression n m

/-- 元の max・削除の式の全頂点での評価。 -/
def cubeConnectionDeletionExpressionVertex {n : ℕ} :
    {m : ℕ} → CubeConnectionDeletionExpression n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, .id _ => _root_.id
  | _, .connect p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeConnectionDeletionExpressionVertex p
  | _, .erase p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeConnectionDeletionExpressionVertex p
termination_by structural _m p => p

/-- 元の max・削除の式を削除・max の二段標準表示へ移す。 -/
def cubeConnectionDeletionExpressionNormal {n : ℕ} :
    {m : ℕ} → CubeConnectionDeletionExpression n m →
    CubeDeletionConnectionNormal n m
  | _, .id _ => cubeDeletionConnectionNormalId n
  | _, .connect p i =>
      cubeDeletionConnectionNormalConnect (cubeConnectionDeletionExpressionNormal p) i
  | _, .erase p i => cubeDeletionConnectionNormalDelete (cubeConnectionDeletionExpressionNormal p) i
termination_by structural _m p => p

/-- max・削除の式の二段正規化は、元の頂点関数を厳密に保存する。 -/
lemma cubeConnectionDeletionExpressionNormal_vertex {n m : ℕ}
    (p : CubeConnectionDeletionExpression n m) :
    cubeDeletionConnectionNormalVertex (cubeConnectionDeletionExpressionNormal p) =
      cubeConnectionDeletionExpressionVertex p := by
  induction p with
  | id => exact cubeDeletionConnectionNormalId_vertex n
  | connect p i ih =>
    change cubeDeletionConnectionNormalVertex
      (cubeDeletionConnectionNormalConnect (cubeConnectionDeletionExpressionNormal p) i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeConnectionDeletionExpressionVertex p
    rw [cubeDeletionConnectionNormalConnect_vertex, ih]
  | erase p i ih =>
    change cubeDeletionConnectionNormalVertex
      (cubeDeletionConnectionNormalDelete (cubeConnectionDeletionExpressionNormal p) i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeConnectionDeletionExpressionVertex p
    rw [cubeDeletionConnectionNormalDelete_vertex, ih]

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の max・削除の式の元の Serre 余モノイド射としての評価。 -/
def serreCubeConnectionDeletionExpression {n : ℕ} :
    {m : ℕ} → CubeConnectionDeletionExpression n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, .id _ => 𝟙 _
  | _, .connect p i => serreCubeConnectionDeletionExpression p ≫ serreCubeConnection A _ i
  | _, .erase p i => serreCubeConnectionDeletionExpression p ≫ serreCubeDegeneracy A _ i
termination_by structural _m p => p

/-- max・削除の式の二段正規化は、元の Serre 評価を厳密に保存する。 -/
lemma serreCubeConnectionDeletionExpressionNormal {n m : ℕ}
    (p : CubeConnectionDeletionExpression n m) :
    serreCubeDeletionConnectionNormal A (cubeConnectionDeletionExpressionNormal p) =
      serreCubeConnectionDeletionExpression A p := by
  induction p with
  | id => exact serreCubeDeletionConnectionNormal_id A n
  | connect p i ih =>
    change serreCubeDeletionConnectionNormal A
      (cubeDeletionConnectionNormalConnect (cubeConnectionDeletionExpressionNormal p) i) =
        serreCubeConnectionDeletionExpression A p ≫ serreCubeConnection A _ i
    rw [serreCubeDeletionConnectionNormal_connect, ih]
  | erase p i ih =>
    change serreCubeDeletionConnectionNormal A
      (cubeDeletionConnectionNormalDelete (cubeConnectionDeletionExpressionNormal p) i) =
        serreCubeConnectionDeletionExpression A p ≫ serreCubeDegeneracy A _ i
    rw [serreCubeDeletionConnectionNormal_delete, ih]

end SerrePositivity.KST.SConstruction
