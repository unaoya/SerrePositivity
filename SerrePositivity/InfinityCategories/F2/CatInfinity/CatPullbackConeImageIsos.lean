module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeNativeCommutativity
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportSquare

/-!
概要：引き戻しの二脚の像から置換後の中心への指定比較同型。
方針：切断の等式と引き戻しの可換性で両端だけを揃える。
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
/-- 概要：引き戻しの二脚の像から置換後の中心への指定比較同型。
方針：切断の等式と引き戻しの可換性で両端だけを揃える。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
def catPullbackConeLeftImageIso (p : A ⟶ C) (q : B ⟶ C) :
    FunctorIso (catPullbackConeFst p q ≫ p)
      (pullback.fst (equivalencePathReplacementMap p) q ≫ equivalencePathReplacementMap p) :=
  functorIsoOfEq
    ((catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)).postcomp
      (equivalencePathReplacementMap p))
    (by change (catPullbackConeFst p q ≫ equivalencePathReplacementSection p) ≫
      equivalencePathReplacementMap p = _
        rw [Category.assoc, equivalencePathReplacementSection_map]) rfl
/-- 概要：引き戻しの二脚の像から置換後の中心への指定比較同型。
方針：切断の等式と引き戻しの可換性で両端だけを揃える。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
def catPullbackConeRightImageIso (p : A ⟶ C) (q : B ⟶ C) :
    FunctorIso (catPullbackConeSnd p q ≫ q)
      (pullback.fst (equivalencePathReplacementMap p) q ≫ equivalencePathReplacementMap p) :=
  functorIsoOfEq
    ((catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)).postcomp q)
    (by change (catPullbackConeSnd p q ≫ 𝟙 B) ≫ q = _
        rw [Category.comp_id]) pullback.condition.symm

end SerrePositivity.InfinityCategories.F2
