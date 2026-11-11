module
public import SerrePositivity.KST.SConstruction.CubeConnectionPathEvaluation

/-! # 元の max の語の Serre 評価の表示非依存性
概要：元の path 圏で max のみからなる二つの語は、同じ具体的射なら同じ Serre 射を表す。
方針：各 path を max の式として厳密に回収し、その標準化と一意性を適用する。
規約：一般の混合語への拡張は別工程。使われ方：三段表示の max の因子。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の生成語が隣接 max だけからなる条件。 -/
inductive CubeConnectionPath : {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} → Quiver.Path X Y → Prop
  | nil (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject) : CubeConnectionPath (.nil : Quiver.Path X X)
  | step {X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {m : ℕ}
      (p : Quiver.Path X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 2))) (hp : CubeConnectionPath p)
      (i : Fin (m + 1)) : CubeConnectionPath
        (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 2) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.connection m i))

/-- 元の max の path は、その同じ構文の max の式から厳密に回収される。 -/
lemma cubeConnectionPath_exists_expression {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {p : Quiver.Path X Y}
    (h : CubeConnectionPath p) : ∃ e : CubeConnectionExpression X.dimension Y.dimension,
      cubeConnectionExpressionPath e = p := by
  induction h with
  | nil => exact ⟨.id X.dimension, rfl⟩
  | step p hp i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.connect e i, ?_⟩
    change (cubeConnectionExpressionPath e).cons _ = p.cons _
    rw [he]

/-- 同じ具体射を表す元の max の語は、元の Serre 余モノイド射として一致する。 -/
lemma serreCubeWordFunctor_connection_independent (A : Type u) [CommRing A]
    {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p q : X ⟶ Y) (hp : CubeConnectionPath p) (hq : CubeConnectionPath q)
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map q) :
    (serreCubeWordFunctor A).map p = (serreCubeWordFunctor A).map q := by
  obtain ⟨e, he⟩ := cubeConnectionPath_exists_expression hp
  obtain ⟨f, hf⟩ := cubeConnectionPath_exists_expression hq
  have hvertex : cubeConnectionExpressionVertex e = cubeConnectionExpressionVertex f := by
    rw [← cubeConnectionExpressionPath_concrete, ← cubeConnectionExpressionPath_concrete, he, hf]
    exact congrArg Subtype.val h
  have hpe := cubeConnectionExpressionPath_serre A e
  have hqe := cubeConnectionExpressionPath_serre A f
  erw [he] at hpe
  erw [hf] at hqe
  exact hpe.trans ((serreCubeConnectionExpression_eq_of_vertex_eq A e f hvertex).trans hqe.symm)

end SerrePositivity.KST.SConstruction
