module
public import SerrePositivity.KST.SConstruction.SerreCubeDeletionFaceNormal

/-! # 面・削除が混在する元の式の二段正規化
概要：元の面と削除が任意に交互に現れる式を、削除・面の二段表示へ移す。
方針：各構文の後合成を、元の二つの評価を保つ更新へ移す。
規約：connection を含む語への拡張は別工程。使われ方：混合語の段階的正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の面と削除を任意に交互に合成した式。 -/
inductive CubeFaceDeletionExpression : ℕ → ℕ → Type
  | id (n : ℕ) : CubeFaceDeletionExpression n n
  | point {n m : ℕ} (p : CubeFaceDeletionExpression n m) (b : Bool) (i : Fin (m + 1)) :
      CubeFaceDeletionExpression n (m + 1)
  | erase {n m : ℕ} (p : CubeFaceDeletionExpression n (m + 1)) (i : Fin (m + 1)) :
      CubeFaceDeletionExpression n m

/-- 元の面・削除の式の全頂点での評価。 -/
def cubeFaceDeletionExpressionVertex {n : ℕ} : {m : ℕ} → CubeFaceDeletionExpression n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, .id _ => _root_.id
  | _, .point p b i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeFaceDeletionExpressionVertex p
  | _, .erase p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeFaceDeletionExpressionVertex p
termination_by structural _m p => p

/-- 元の面・削除の式を削除・面の二段標準表示へ移す。 -/
def cubeFaceDeletionExpressionNormal {n : ℕ} : {m : ℕ} → CubeFaceDeletionExpression n m →
    CubeDeletionFaceNormal n m
  | _, .id _ => cubeDeletionFaceNormalId n
  | _, .point p b i => cubeDeletionFaceNormalPoint (cubeFaceDeletionExpressionNormal p) b i
  | _, .erase p i => cubeDeletionFaceNormalDelete (cubeFaceDeletionExpressionNormal p) i
termination_by structural _m p => p

/-- 面・削除の式の二段正規化は、元の頂点関数を厳密に保存する。 -/
lemma cubeFaceDeletionExpressionNormal_vertex {n m : ℕ} (p : CubeFaceDeletionExpression n m) :
    cubeDeletionFaceNormalVertex (cubeFaceDeletionExpressionNormal p) =
      cubeFaceDeletionExpressionVertex p := by
  induction p with
  | id => exact cubeDeletionFaceNormalId_vertex n
  | point p b i ih =>
    change cubeDeletionFaceNormalVertex
      (cubeDeletionFaceNormalPoint (cubeFaceDeletionExpressionNormal p) b i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeFaceDeletionExpressionVertex p
    rw [cubeDeletionFaceNormalPoint_vertex, ih]
  | erase p i ih =>
    change cubeDeletionFaceNormalVertex
      (cubeDeletionFaceNormalDelete (cubeFaceDeletionExpressionNormal p) i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeFaceDeletionExpressionVertex p
    rw [cubeDeletionFaceNormalDelete_vertex, ih]

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の面・削除の式の元の Serre 余モノイド射としての評価。 -/
def serreCubeFaceDeletionExpression {n : ℕ} : {m : ℕ} → CubeFaceDeletionExpression n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, .id _ => 𝟙 _
  | _, .point p b i => serreCubeFaceDeletionExpression p ≫ serreCubeFace A b _ i
  | _, .erase p i => serreCubeFaceDeletionExpression p ≫ serreCubeDegeneracy A _ i
termination_by structural _m p => p

/-- 面・削除の式の二段正規化は、元の Serre 評価を厳密に保存する。 -/
lemma serreCubeFaceDeletionExpressionNormal {n m : ℕ} (p : CubeFaceDeletionExpression n m) :
    serreCubeDeletionFaceNormal A (cubeFaceDeletionExpressionNormal p) =
      serreCubeFaceDeletionExpression A p := by
  induction p with
  | id => exact serreCubeDeletionFaceNormal_id A n
  | point p b i ih =>
    change serreCubeDeletionFaceNormal A
      (cubeDeletionFaceNormalPoint (cubeFaceDeletionExpressionNormal p) b i) =
        serreCubeFaceDeletionExpression A p ≫ serreCubeFace A b _ i
    rw [serreCubeDeletionFaceNormal_point, ih]
  | erase p i ih =>
    change serreCubeDeletionFaceNormal A
      (cubeDeletionFaceNormalDelete (cubeFaceDeletionExpressionNormal p) i) =
        serreCubeFaceDeletionExpression A p ≫ serreCubeDegeneracy A _ i
    rw [serreCubeDeletionFaceNormal_delete, ih]

end SerrePositivity.KST.SConstruction
