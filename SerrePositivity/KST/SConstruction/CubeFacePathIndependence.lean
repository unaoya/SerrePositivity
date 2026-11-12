module
public import SerrePositivity.KST.SConstruction.CubeFacePathEvaluation

/-! # 元の面の語の Serre 評価の表示非依存性
概要：元の path 圏で面のみからなる二つの語は、同じ具体的射なら同じ Serre 射を表す。
方針：各 path を面の式として厳密に回収し、その標準化と一意性を適用する。
規約：connection と混合語への拡張は別工程。使われ方：三段表示の面の因子。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の生成語が二端点の面だけからなる条件。 -/
inductive CubeFacePath : {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} → Quiver.Path X Y → Prop
  | nil (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject) : CubeFacePath (.nil : Quiver.Path X X)
  | step {X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {m : ℕ} (p : Quiver.Path X (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m))
      (hp : CubeFacePath p) (b : Bool) (i : Fin (m + 1)) : CubeFacePath
        (p.cons (show _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject.mk (m + 1) from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeGenerator.face b m i))

/-- 元の面の path は、その同じ構文の面の式から厳密に回収される。 -/
lemma cubeFacePath_exists_expression {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordObject} {p : Quiver.Path X Y}
    (h : CubeFacePath p) : ∃ e : CubeFaceExpression X.dimension Y.dimension,
      cubeFaceExpressionPath e = p := by
  induction h with
  | nil => exact ⟨.id X.dimension, rfl⟩
  | step p hp b i ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨.point e b i, ?_⟩
    change (cubeFaceExpressionPath e).cons _ = p.cons _
    rw [he]

/-- 同じ具体射を表す元の面の語は、元の Serre 余モノイド射として一致する。 -/
lemma serreCubeWordFunctor_face_independent (A : Type u) [CommRing A]
    {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWords} (p q : X ⟶ Y) (hp : CubeFacePath p) (hq : CubeFacePath q)
    (h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map p = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeWordConcreteFunctor.map q) :
    (serreCubeWordFunctor A).map p = (serreCubeWordFunctor A).map q := by
  obtain ⟨e, he⟩ := cubeFacePath_exists_expression hp
  obtain ⟨f, hf⟩ := cubeFacePath_exists_expression hq
  have hvertex : cubeFaceExpressionVertex e = cubeFaceExpressionVertex f := by
    rw [← cubeFaceExpressionPath_concrete, ← cubeFaceExpressionPath_concrete, he, hf]
    exact congrArg Subtype.val h
  have hpe := cubeFaceExpressionPath_serre A e
  have hqe := cubeFaceExpressionPath_serre A f
  erw [he] at hpe
  erw [hf] at hqe
  exact hpe.trans ((serreCubeFaceExpression_eq_of_vertex_eq A e f hvertex).trans hqe.symm)

end SerrePositivity.KST.SConstruction
