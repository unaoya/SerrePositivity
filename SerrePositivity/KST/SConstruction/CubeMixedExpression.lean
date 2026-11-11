module
public import SerrePositivity.KST.SConstruction.CubeThreeNormalUpdates

/-! # 全生成射が混在する元の式の三段正規化
概要：元の面・削除・connection が任意に現れる式を三段表示へ移す。
方針：各構文の後合成を、元の二つの評価を保つ更新へ移す。
規約：三段表示の一意性と意味による降下は別工程。使われ方：混合語の段階的正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の面・削除・connection を任意に合成した式。 -/
inductive CubeMixedExpression : ℕ → ℕ → Type
  | id (n : ℕ) : CubeMixedExpression n n
  | point {n m : ℕ} (p : CubeMixedExpression n m) (b : Bool) (i : Fin (m + 1)) :
      CubeMixedExpression n (m + 1)
  | erase {n m : ℕ} (p : CubeMixedExpression n (m + 1)) (i : Fin (m + 1)) :
      CubeMixedExpression n m
  | connect {n m : ℕ} (p : CubeMixedExpression n (m + 2)) (i : Fin (m + 1)) :
      CubeMixedExpression n (m + 1)

/-- 元の混合式の全頂点での評価。 -/
def cubeMixedExpressionVertex {n : ℕ} : {m : ℕ} → CubeMixedExpression n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, .id _ => _root_.id
  | _, .point p b i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeMixedExpressionVertex p
  | _, .erase p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeMixedExpressionVertex p
  | _, .connect p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeMixedExpressionVertex p
termination_by structural _m p => p

/-- 元の混合式を削除・max・面の三段標準表示へ移す。 -/
def cubeMixedExpressionNormal {n : ℕ} : {m : ℕ} → CubeMixedExpression n m →
    CubeThreeNormal n m
  | _, .id _ => cubeThreeNormalId n
  | _, .point p b i => cubeThreeNormalPoint (cubeMixedExpressionNormal p) b i
  | _, .erase p i => cubeThreeNormalDelete (cubeMixedExpressionNormal p) i
  | _, .connect p i => cubeThreeNormalConnect (cubeMixedExpressionNormal p) i
termination_by structural _m p => p

/-- 混合式の三段正規化は、元の頂点関数を厳密に保存する。 -/
lemma cubeMixedExpressionNormal_vertex {n m : ℕ} (p : CubeMixedExpression n m) :
    cubeThreeNormalVertex (cubeMixedExpressionNormal p) =
      cubeMixedExpressionVertex p := by
  induction p with
  | id => exact cubeThreeNormalId_vertex n
  | point p b i ih =>
    change cubeThreeNormalVertex
      (cubeThreeNormalPoint (cubeMixedExpressionNormal p) b i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeMixedExpressionVertex p
    rw [cubeThreeNormalPoint_vertex, ih]
  | erase p i ih =>
    change cubeThreeNormalVertex
      (cubeThreeNormalDelete (cubeMixedExpressionNormal p) i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeMixedExpressionVertex p
    rw [cubeThreeNormalDelete_vertex, ih]
  | connect p i ih =>
    change cubeThreeNormalVertex
      (cubeThreeNormalConnect (cubeMixedExpressionNormal p) i) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeMixedExpressionVertex p
    rw [cubeThreeNormalConnect_vertex, ih]

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の混合式の元の Serre 余モノイド射としての評価。 -/
def serreCubeMixedExpression {n : ℕ} : {m : ℕ} → CubeMixedExpression n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, .id _ => 𝟙 _
  | _, .point p b i => serreCubeMixedExpression p ≫ serreCubeFace A b _ i
  | _, .erase p i => serreCubeMixedExpression p ≫ serreCubeDegeneracy A _ i
  | _, .connect p i => serreCubeMixedExpression p ≫ serreCubeConnection A _ i
termination_by structural _m p => p

/-- 混合式の三段正規化は、元の Serre 評価を厳密に保存する。 -/
lemma serreCubeMixedExpressionNormal {n m : ℕ} (p : CubeMixedExpression n m) :
    serreCubeThreeNormal A (cubeMixedExpressionNormal p) =
      serreCubeMixedExpression A p := by
  induction p with
  | id => exact serreCubeThreeNormal_id A n
  | point p b i ih =>
    change serreCubeThreeNormal A
      (cubeThreeNormalPoint (cubeMixedExpressionNormal p) b i) =
        serreCubeMixedExpression A p ≫ serreCubeFace A b _ i
    rw [serreCubeThreeNormal_point, ih]
  | erase p i ih =>
    change serreCubeThreeNormal A
      (cubeThreeNormalDelete (cubeMixedExpressionNormal p) i) =
        serreCubeMixedExpression A p ≫ serreCubeDegeneracy A _ i
    rw [serreCubeThreeNormal_delete, ih]
  | connect p i ih =>
    change serreCubeThreeNormal A
      (cubeThreeNormalConnect (cubeMixedExpressionNormal p) i) =
        serreCubeMixedExpression A p ≫ serreCubeConnection A _ i
    rw [serreCubeThreeNormal_connect, ih]

end SerrePositivity.KST.SConstruction
