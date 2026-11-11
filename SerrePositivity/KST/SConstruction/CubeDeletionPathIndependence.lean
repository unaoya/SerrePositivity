module
public import SerrePositivity.KST.SConstruction.CubeDeletionPathEvaluation

/-! # 元の削除語の Serre 評価の表示非依存性
概要：元の path 圏で削除のみからなる二つの語は、同じ具体的射なら同じ Serre 射を表す。
方針：各 path を削除式として厳密に回収し、その標準化と一意性を適用する。
規約：面・connection を含む一般の語への拡張は別工程。使われ方：三段表示の削除因子。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の生成語が削除だけからなる条件。 -/
inductive CubeDeletionPath : {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} → Quiver.Path X Y → Prop
  | nil (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject) : CubeDeletionPath (.nil : Quiver.Path X X)
  | step {X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {m : ℕ}
      (p : Quiver.Path X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1))) (hp : CubeDeletionPath p)
      (i : Fin (m + 1)) : CubeDeletionPath
        (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.degeneracy m i))

/-- 元の削除 path は、その同じ構文の削除式から厳密に回収される。 -/
lemma cubeDeletionPath_exists_expression {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {p : Quiver.Path X Y}
    (h : CubeDeletionPath p) : ∃ e : CubeDeletionExpression X.dimension Y.dimension,
      cubeDeletionExpressionPath e = p := by
  induction h with
  | nil => exact ⟨.id X.dimension, rfl⟩
  | step p hp i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.erase e i, ?_⟩
    change (cubeDeletionExpressionPath e).cons _ = p.cons _
    rw [he]

/-- 同じ具体射を表す元の削除語は、元の Serre 余モノイド射として一致する。 -/
lemma serreCubeWordFunctor_deletion_independent (A : Type u) [CommRing A]
    {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p q : X ⟶ Y) (hp : CubeDeletionPath p) (hq : CubeDeletionPath q)
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map q) :
    (serreCubeWordFunctor A).map p = (serreCubeWordFunctor A).map q := by
  obtain ⟨e, he⟩ := cubeDeletionPath_exists_expression hp
  obtain ⟨f, hf⟩ := cubeDeletionPath_exists_expression hq
  have hvertex : cubeDeletionExpressionVertex e = cubeDeletionExpressionVertex f := by
    rw [← cubeDeletionExpressionPath_concrete, ← cubeDeletionExpressionPath_concrete, he, hf]
    exact congrArg Subtype.val h
  have hpe := cubeDeletionExpressionPath_serre A e
  have hqe := cubeDeletionExpressionPath_serre A f
  erw [he] at hpe
  erw [hf] at hqe
  exact hpe.trans ((serreCubeDeletionExpression_eq_of_vertex_eq A e f hvertex).trans hqe.symm)

end SerrePositivity.KST.SConstruction
