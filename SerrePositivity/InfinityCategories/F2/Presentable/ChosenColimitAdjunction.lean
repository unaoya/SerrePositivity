module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitUnitHomFormula
public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitUnitHomFlipCriterion

/-!
概要：指定形状の余極限関手は定値図式関手の左随伴である。
方針：元の全単位の Hom 写像を関手圏内の普遍余錐の全単射へ移す。
規約：余極限関手と全単位の選択を保持する。
使われ方：有限余積の全関手による余極限保存と指定比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：選んだ余極限単位の全パラメータの Hom 写像は全単射。
方針：変数交換の同値と native な普遍余錐の Hom 全単射を合成する。
規約：同じ指定単位を使う。
使われ方：余極限と定値図式の随伴判定。 -/
lemma chosenColimitUnitHom_bijective {K A X : SSet.{u}} [Quasicategory X] [Quasicategory A]
    (hX : ∀ p : K ⟶ X, HasColimit p) (U : A ⟶ (ihom K).obj X) (V : A ⟶ X) :
    Function.Bijective (qcatUnitHomMap (chosenColimitUnitHom K X hX) U V) :=
  (parameterUnitHomMap_bijective_iff (chosenColimitUnitHom K X hX) U V).mp
    (colimitUnitHom_bijective_of_flip (chosenColimitParameterCocone hX U)
      (chosenColimitParameterCocone_isColimit hX U) (chosenColimitParameterCocone_vertex hX U)
      (parameterUnitHomMap (chosenColimitUnitHom K X hX) U V)
      (chosenColimitUnitHomMap_flip hX U V))

/-- 概要：選んだ余極限関手と定値図式関手の実際の随伴。
方針：指定した全単位の全 Hom 全単射を随伴の単位判定へ適用する。
規約：元の余極限関手を変更しない。
使われ方：有限余積の全関手の余極限保存。 -/
def chosenColimitAdjunction (K X : SSet.{u}) [Quasicategory X]
    (hX : ∀ p : K ⟶ X, HasColimit p) :
    QCatAdjunction (chosenColimitFunctor K X hX) (constantFunctorMap K X) :=
  qcatAdjunctionOfUnitHomBijective (chosenColimitUnitHom K X hX)
    (chosenColimitUnitHom_bijective hX)

end SerrePositivity.InfinityCategories.F2.Presentable
