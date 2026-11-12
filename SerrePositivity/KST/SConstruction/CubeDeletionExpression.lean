module
public import SerrePositivity.KST.SConstruction.SerreCubeDeletionNormal

/-! # 元の削除式の標準化と Serre 評価の保存
概要：削除を順に合成した任意の式を保持・削除標準表示へ移し、元の二つの評価を回収する。
方針：一出力削除との照合を各構文に適用する。
規約：具体的な頂点関数の等号から元の Serre 射の等号を結論する。
使われ方：元の生成語の圏の削除のみの語への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の座標削除を順に合成した式。 -/
inductive CubeDeletionExpression : ℕ → ℕ → Type
  | id (n : ℕ) : CubeDeletionExpression n n
  | erase {n m : ℕ} (p : CubeDeletionExpression n (m + 1)) (i : Fin (m + 1)) :
      CubeDeletionExpression n m

/-- 元の削除式を具体的な頂点関数へ評価する。 -/
def cubeDeletionExpressionVertex {n : ℕ} : {m : ℕ} → CubeDeletionExpression n m →
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m)
  | _, .id _ => _root_.id
  | _, .erase p i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeDeletionExpressionVertex p
termination_by structural _m p => p

/-- 元の削除式を保持・削除標準表示へ移す。 -/
def cubeDeletionExpressionNormal {n : ℕ} : {m : ℕ} → CubeDeletionExpression n m →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n m
  | _, .id _ => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n
  | _, .erase p i => _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase (cubeDeletionExpressionNormal p) i
termination_by structural _m p => p

/-- 削除式の標準化は、元の全頂点での関数を厳密に保存する。 -/
lemma cubeDeletionExpressionNormal_vertex {n m : ℕ} (p : CubeDeletionExpression n m) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (cubeDeletionExpressionNormal p) =
      cubeDeletionExpressionVertex p := by
  induction p with
  | id =>
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n)) = _root_.id
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId_embedding]
    rfl
  | erase p i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase (cubeDeletionExpressionNormal p) i) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeDeletionExpressionVertex p
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex_erase, ih]

open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の削除式を、元の Serre 余モノイド射へ評価する。 -/
def serreCubeDeletionExpression {n : ℕ} : {m : ℕ} → CubeDeletionExpression n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, .id _ => 𝟙 _
  | _, .erase p i => serreCubeDeletionExpression p ≫ serreCubeDegeneracy A _ i
termination_by structural _m p => p

/-- 削除式の標準化は、元の Serre 評価そのものを厳密に保存する。 -/
lemma serreCubeDeletionExpressionNormal {n m : ℕ} (p : CubeDeletionExpression n m) :
    serreCubeDeletionNormal A (cubeDeletionExpressionNormal p) =
      serreCubeDeletionExpression A p := by
  induction p with
  | id =>
    change serreCubeDeletionNormal A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalId n) = 𝟙 _
    exact serreCubeDeletionNormal_id A n
  | erase p i ih =>
    change serreCubeDeletionNormal A
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalErase (cubeDeletionExpressionNormal p) i) =
        serreCubeDeletionExpression A p ≫ serreCubeDegeneracy A _ i
    rw [serreCubeDeletionNormal_erase, ih]

/-- 同じ具体的な頂点関数を表す削除式の元の Serre 評価は一致する。 -/
lemma serreCubeDeletionExpression_eq_of_vertex_eq {n m : ℕ}
    (p q : CubeDeletionExpression n m)
    (h : cubeDeletionExpressionVertex p = cubeDeletionExpressionVertex q) :
    serreCubeDeletionExpression A p = serreCubeDeletionExpression A q := by
  have hn : cubeDeletionExpressionNormal p = cubeDeletionExpressionNormal q :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex_injective n m
      ((cubeDeletionExpressionNormal_vertex p).trans
        (h.trans (cubeDeletionExpressionNormal_vertex q).symm))
  rw [← serreCubeDeletionExpressionNormal, ← serreCubeDeletionExpressionNormal, hn]

end SerrePositivity.KST.SConstruction
