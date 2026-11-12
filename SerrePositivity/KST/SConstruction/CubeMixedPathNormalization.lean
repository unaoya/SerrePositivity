module
public import SerrePositivity.KST.SConstruction.CubeMixedExpression
public import SerrePositivity.KST.SConstruction.SerreCubeWordEvaluation

/-! # 元の全混合語の三段正規化
概要：元の path 圏の任意の語を、二つの評価を保つ削除・max・面の表示へ移す。
方針：全生成射の混合式で元の語を厳密に回収し、構文の正規化を適用する。
規約：意味による表示非依存性は別工程。使われ方：Serre 評価の具体的立方体圏への降下。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 全生成射のの混合式を元の生成語の path として厳密に実現する。 -/
def cubeMixedExpressionPath {n : ℕ} : {m : ℕ} → CubeMixedExpression n m →
    Quiver.Path (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk n) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m)
  | _, .id _ => .nil
  | _, .point p b i => (cubeMixedExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b _ i)
  | _, .erase p i => (cubeMixedExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy _ i)
  | _, .connect p i => (cubeMixedExpressionPath p).cons (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection _ i)
termination_by structural _m p => p

/-- 混合式の path の具体的評価は、同じ式の元の頂点関数。 -/
lemma cubeMixedExpressionPath_concrete {n m : ℕ} (p : CubeMixedExpression n m) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeMixedExpressionPath p)).val =
      cubeMixedExpressionVertex p := by
  induction p with
  | id => rfl
  | point p b i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeMixedExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexFace b _ i ∘ cubeMixedExpressionVertex p
    rw [ih]
    rfl
  | erase p i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeMixedExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy _ i ∘ cubeMixedExpressionVertex p
    rw [ih]
    rfl
  | connect p i ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map (cubeMixedExpressionPath p)).val =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexConnection _ i ∘ cubeMixedExpressionVertex p
    rw [ih]
    rfl

/-- 混合式の path の Serre 評価は、同じ式の元の Serre 射。 -/
lemma cubeMixedExpressionPath_serre (A : Type u) [CommRing A] {n m : ℕ}
    (p : CubeMixedExpression n m) :
    (serreCubeWordFunctor A).map (cubeMixedExpressionPath p) =
      serreCubeMixedExpression A p := by
  induction p with
  | id => rfl
  | point p b i ih =>
    change (serreCubeWordFunctor A).map (cubeMixedExpressionPath p) ≫
      serreCubeFace A b _ i = serreCubeMixedExpression A p ≫ serreCubeFace A b _ i
    rw [ih]
    rfl
  | erase p i ih =>
    change (serreCubeWordFunctor A).map (cubeMixedExpressionPath p) ≫
      serreCubeDegeneracy A _ i = serreCubeMixedExpression A p ≫ serreCubeDegeneracy A _ i
    rw [ih]
    rfl
  | connect p i ih =>
    change (serreCubeWordFunctor A).map (cubeMixedExpressionPath p) ≫
      serreCubeConnection A _ i = serreCubeMixedExpression A p ≫ serreCubeConnection A _ i
    rw [ih]
    rfl

/-- 混合式の末尾へ元の一生成射を追加する。 -/
def cubeMixedExpressionAppend {n : ℕ} : {a b : ℕ} → CubeMixedExpression n a →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator a b → CubeMixedExpression n b
  | _, _, p, .face c _ i => .point p c i
  | _, _, p, .degeneracy _ i => .erase p i
  | _, _, p, .connection _ i => .connect p i

/-- 一生成射の追加は、元の path の末尾への同じ追加を回収する。 -/
lemma cubeMixedExpressionAppend_path {n a b : ℕ} (p : CubeMixedExpression n a)
    (g : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator a b) :
    cubeMixedExpressionPath (cubeMixedExpressionAppend p g) =
      (cubeMixedExpressionPath p).cons g := by
  cases g <;> rfl

/-- 元の任意の生成語は、その同じ構文の混合式から厳密に回収される。 -/
lemma cubeWordPath_exists_mixedExpression {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} (p : Quiver.Path X Y) :
    ∃ e : CubeMixedExpression X.dimension Y.dimension, cubeMixedExpressionPath e = p := by
  induction p with
  | nil => exact ⟨.id X.dimension, rfl⟩
  | cons p g ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨cubeMixedExpressionAppend e g, ?_⟩
    rw [cubeMixedExpressionAppend_path, he]

/-- 元の任意の混合語を、両方の実際の評価を保った三段表示へ移す。 -/
lemma cubeWordPath_normalization (A : Type u) [CommRing A]
    {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p : X ⟶ Y) :
    ∃ r : CubeThreeNormal X.dimension Y.dimension,
      cubeThreeNormalVertex r = (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p).val ∧
        serreCubeThreeNormal A r = (serreCubeWordFunctor A).map p := by
  obtain ⟨e, he⟩ := cubeWordPath_exists_mixedExpression p
  have hvertex := cubeMixedExpressionPath_concrete e
  have hserre := cubeMixedExpressionPath_serre A e
  erw [he] at hvertex hserre
  exact ⟨cubeMixedExpressionNormal e,
    (cubeMixedExpressionNormal_vertex e).trans hvertex.symm,
    (serreCubeMixedExpressionNormal A e).trans hserre.symm⟩

end SerrePositivity.KST.SConstruction
