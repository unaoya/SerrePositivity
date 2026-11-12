module
public import SerrePositivity.KST.SConstruction.CubeDeletionExpression
public import SerrePositivity.KST.SConstruction.SerreCubeWordEvaluation

/-! # 元の生成語の圏への削除式の接続
概要：削除式を元の生成語へ送り、具体的な評価と Serre 評価を同時に回収する。
方針：path 圏の一文字追加の定義を削除式の帰納法で照合する。
規約：元の語の圏も元の Serre 射も置き換えない。使われ方：削除のみの語の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の削除式を、元の cubical 生成語の圏の path として実現する。 -/
def cubeDeletionExpressionPath {n : ℕ} : {m : ℕ} → CubeDeletionExpression n m →
    Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m)
  | _, .id _ => .nil
  | _, .erase p i => (cubeDeletionExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy _ i)
termination_by structural _m p => p

/-- 削除式の path の具体的評価は、同じ削除式の元の頂点関数。 -/
lemma cubeDeletionExpressionPath_concrete {n m : ℕ} (p : CubeDeletionExpression n m) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeDeletionExpressionPath p)).val =
      cubeDeletionExpressionVertex p := by
  induction p with
  | id => rfl
  | erase p i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeDeletionExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeDeletionExpressionVertex p
    rw [ih]
    rfl

noncomputable section
universe u
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 削除式の path の Serre 評価は、同じ削除式の元の Serre 射。 -/
lemma cubeDeletionExpressionPath_serre {n m : ℕ} (p : CubeDeletionExpression n m) :
    (serreCubeWordFunctor A).map (cubeDeletionExpressionPath p) =
      serreCubeDeletionExpression A p := by
  induction p with
  | id => rfl
  | erase p i ih =>
    change (serreCubeWordFunctor A).map (cubeDeletionExpressionPath p) ≫
      serreCubeDegeneracy A _ i =
        serreCubeDeletionExpression A p ≫ serreCubeDegeneracy A _ i
    rw [ih]
    rfl

end
end SerrePositivity.KST.SConstruction
