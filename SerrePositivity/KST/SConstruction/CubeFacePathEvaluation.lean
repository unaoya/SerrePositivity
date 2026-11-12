module
public import SerrePositivity.KST.SConstruction.CubeFaceExpression
public import SerrePositivity.KST.SConstruction.SerreCubeWordEvaluation

/-! # 元の生成語の圏への面の式の接続
概要：面の式を元の生成語へ送り、具体的な評価と Serre 評価を同時に回収する。
方針：path 圏の一文字追加の定義を面の式の帰納法で照合する。
規約：元の語の圏も元の Serre 射も置き換えない。使われ方：面のみの語の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の面の式を、元の cubical 生成語の圏の path として実現する。 -/
def cubeFaceExpressionPath {n : ℕ} : {m : ℕ} → CubeFaceExpression n m →
    Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m)
  | _, .id _ => .nil
  | _, .point p b i => (cubeFaceExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b _ i)
termination_by structural _m p => p

/-- 面の式の path の具体的評価は、同じ式の元の頂点関数。 -/
lemma cubeFaceExpressionPath_concrete {n m : ℕ} (p : CubeFaceExpression n m) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeFaceExpressionPath p)).val =
      cubeFaceExpressionVertex p := by
  induction p with
  | id => rfl
  | point p b i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeFaceExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeFaceExpressionVertex p
    rw [ih]
    rfl

noncomputable section
universe u
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 面の式の path の Serre 評価は、同じ式の元の Serre 射。 -/
lemma cubeFaceExpressionPath_serre {n m : ℕ} (p : CubeFaceExpression n m) :
    (serreCubeWordFunctor A).map (cubeFaceExpressionPath p) = serreCubeFaceExpression A p := by
  induction p with
  | id => rfl
  | point p b i ih =>
    change (serreCubeWordFunctor A).map (cubeFaceExpressionPath p) ≫ serreCubeFace A b _ i =
      serreCubeFaceExpression A p ≫ serreCubeFace A b _ i
    rw [ih]
    rfl

end
end SerrePositivity.KST.SConstruction
