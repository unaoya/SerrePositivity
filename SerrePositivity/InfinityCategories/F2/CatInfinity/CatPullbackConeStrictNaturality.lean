module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackDiagramEqIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackReplacementTriangleEqIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeComparisonNaturality

/-!
概要：各脚の指定比較の自然性から strict な面を簡約。
方針：図式の自然性と strict な錐の可換等式による同型へ置き換える。
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
/-- 概要：各脚の指定比較の整合式の strict な二面は等式から来る標準同型。
方針：図式側と置換後の錐の指定同型の定値性を既存の自然性へ適用する。
規約：元の錐の三角形と各脚の指定比較同型を変更しない。
使われ方：二脚の比較と引き戻し候補の指定 path の整合。 -/
lemma catPullbackConeLegSectionIso_strict_naturality (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    (catPullbackConeLegTriangleIso p q f).postcomp
        ((catPullbackReplacementNatTrans p q).app j) ≪≫
      functorEqIso (congrArg
        (fun k ↦ (show catPullback p q ⟶ ((catPullbackDiagram p q).obj i).obj from
          catPullbackConeFunctorLeg p q i) ≫ k)
        ((catPullbackReplacementNatTrans p q).naturality f)) ≪≫
      (catPullbackConeLegSectionIso p q i).postcomp
        ((catPullbackReplacementDiagram p q).map f) =
    catPullbackConeLegSectionIso p q j ≪≫
      functorEqIso ((catPullbackReplacementOrdinaryCone p q).w f).symm := by
  have h := catPullbackConeLegSectionIso_naturality p q f
  have hb := ((catPullbackDiagramComparisonIso_isFunctorEqIso p q f).precomp
    (show catPullback p q ⟶ ((catPullbackDiagram p q).obj i).obj from
      catPullbackConeFunctorLeg p q i)).eq
        (congrArg (fun k ↦ (catPullbackConeFunctorLeg p q i) ≫ k)
          ((catPullbackReplacementNatTrans p q).naturality f))
  have ht := ((catPullbackReplacementTriangleIso_isFunctorEqIso p q f).precomp
    (𝟙 (catPullback p q))).eq ((catPullbackReplacementOrdinaryCone p q).w f).symm
  rw [hb, ht] at h
  exact h

end SerrePositivity.InfinityCategories.F2
