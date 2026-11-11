module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackDiagramTriangleConstant
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatTriangleConstantFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

/-!
概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramUpperComparisonIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramUpperComparisonIso p q f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isFunctorEqIso_catInfinityTriangleIso_of_faces
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramUpperTriangle_constant p q f
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramLowerComparisonIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramLowerComparisonIso p q f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isFunctorEqIso_catInfinityTriangleIso_of_faces
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramLowerTriangle_constant p q f
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramComparisonIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramComparisonIso p q f) :=
  (catPullbackDiagramLowerComparisonIso_isFunctorEqIso p q f).symm.trans
    (catPullbackDiagramUpperComparisonIso_isFunctorEqIso p q f)
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramComparisonIso_eq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagramComparisonIso p q f =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q).map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q).app j)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackDiagram p q).map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q).app j)
        from Iso.refl _) rfl ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackReplacementNatTrans p q).naturality f) :=
  (catPullbackDiagramComparisonIso_isFunctorEqIso p q f).eq _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
