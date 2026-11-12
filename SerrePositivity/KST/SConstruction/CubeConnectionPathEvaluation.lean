module
public import SerrePositivity.KST.SConstruction.CubeConnectionExpression
public import SerrePositivity.KST.SConstruction.SerreCubeWordEvaluation

/-! # 元の生成語の圏への max の式の接続
概要：max の式を元の生成語へ送り、具体的な評価と Serre 評価を同時に回収する。
方針：path 圏の一文字追加の定義を元の式の帰納法で照合する。
規約：元の語の圏も元の Serre 射も置き換えない。使われ方：max のみの語の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の max の式を、元の cubical 生成語の圏の path として実現する。 -/
def cubeConnectionExpressionPath {n : ℕ} : {m : ℕ} → CubeConnectionExpression n m →
    Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m)
  | _, .id _ => .nil
  | _, .connect p i => (cubeConnectionExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection _ i)
termination_by structural _m p => p

/-- max の式の path の具体的評価は、同じ式の元の頂点関数。 -/
lemma cubeConnectionExpressionPath_concrete {n m : ℕ} (p : CubeConnectionExpression n m) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeConnectionExpressionPath p)).val =
      cubeConnectionExpressionVertex p := by
  induction p with
  | id => rfl
  | connect p i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeConnectionExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeConnectionExpressionVertex p
    rw [ih]
    rfl

noncomputable section
universe u
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- max の式の path の Serre 評価は、同じ式の元の Serre 射。 -/
lemma cubeConnectionExpressionPath_serre {n m : ℕ} (p : CubeConnectionExpression n m) :
    (serreCubeWordFunctor A).map (cubeConnectionExpressionPath p) =
      serreCubeConnectionExpression A p := by
  induction p with
  | id => rfl
  | connect p i ih =>
    change (serreCubeWordFunctor A).map (cubeConnectionExpressionPath p) ≫
      serreCubeConnection A _ i =
        serreCubeConnectionExpression A p ≫ serreCubeConnection A _ i
    rw [ih]
    rfl

end
end SerrePositivity.KST.SConstruction
