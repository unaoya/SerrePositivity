module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackDiagramTriangleConstant
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleConstantFaces
public import SerrePositivity.InfinityCategories.Core.CatInfinity.FunctorEqIsoAlgebra

/-!
概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramUpperComparisonIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    IsFunctorEqIso (catPullbackDiagramUpperComparisonIso p q f) := by
  apply isFunctorEqIso_catInfinityTriangleIso_of_faces
  exact catPullbackDiagramUpperTriangle_constant p q f
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramLowerComparisonIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    IsFunctorEqIso (catPullbackDiagramLowerComparisonIso p q f) := by
  apply isFunctorEqIso_catInfinityTriangleIso_of_faces
  exact catPullbackDiagramLowerTriangle_constant p q f
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramComparisonIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    IsFunctorEqIso (catPullbackDiagramComparisonIso p q f) :=
  (catPullbackDiagramLowerComparisonIso_isFunctorEqIso p q f).symm.trans
    (catPullbackDiagramUpperComparisonIso_isFunctorEqIso p q f)
/-- 概要：引き戻し図式の指定比較同型を自然性等式で簡約。
方針：上下の定値三角形の同型を合成し等式から来る同型と同定する。
規約：元の指定二単体と同型を保持する。
使われ方：各脚の比較の自然性の式の簡約。 -/
lemma catPullbackDiagramComparisonIso_eq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    catPullbackDiagramComparisonIso p q f =
      functorIsoOfEq (show FunctorIso
        ((catPullbackDiagram p q).map f ≫ (catPullbackReplacementNatTrans p q).app j)
        ((catPullbackDiagram p q).map f ≫ (catPullbackReplacementNatTrans p q).app j)
        from Iso.refl _) rfl ((catPullbackReplacementNatTrans p q).naturality f) :=
  (catPullbackDiagramComparisonIso_isFunctorEqIso p q f).eq _

end SerrePositivity.InfinityCategories.F2
