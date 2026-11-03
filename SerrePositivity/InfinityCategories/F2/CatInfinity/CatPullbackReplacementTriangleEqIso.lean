module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTriangleConstantFaces
public import SerrePositivity.InfinityCategories.Core.CatInfinity.FunctorEqIsoAlgebra
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackReplacementTriangleIso

/-!
概要：置換後の引き戻し錐の指定三角形の同型の簡約。
方針：strict な錐の定値性から等式による標準同型と同定する。
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
/-- 概要：置換後の錐の指定三角形の同型は錐の可換等式から来る。
方針：strict な錐の定値性と指定同型の判定を使う。
規約：元の二単体から得る指定同型の値を保つ。
使われ方：脚の自然性の整合式の簡約。 -/
lemma catPullbackReplacementTriangleIso_isFunctorEqIso (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    IsFunctorEqIso (catPullbackReplacementTriangleIso p q f) := by
  apply isFunctorEqIso_catInfinityTriangleIso_of_faces
  exact isConstantCoherentTriangle_strictCone (catPullbackReplacementOrdinaryCone p q) _
/-- 概要：置換後の錐の指定三角形の同型は錐の可換等式から来る。
方針：strict な錐の定値性と指定同型の判定を使う。
規約：元の二単体から得る指定同型の値を保つ。
使われ方：脚の自然性の整合式の簡約。 -/
lemma catPullbackReplacementTriangleIso_eq (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    catPullbackReplacementTriangleIso p q f =
      functorIsoOfEq (show FunctorIso ((catPullbackReplacementOrdinaryCone p q).π.app j)
        ((catPullbackReplacementOrdinaryCone p q).π.app j) from Iso.refl _) rfl
        ((catPullbackReplacementOrdinaryCone p q).w f).symm :=
  (catPullbackReplacementTriangleIso_isFunctorEqIso p q f).eq _

end SerrePositivity.InfinityCategories.F2
