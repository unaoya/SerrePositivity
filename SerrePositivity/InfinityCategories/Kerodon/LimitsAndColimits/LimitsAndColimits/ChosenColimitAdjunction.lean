module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitUnitHomFormula
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ColimitUnitHomFlipCriterion

/-!
概要：指定形状の余極限関手は定値図式関手の左随伴である。
方針：元の全単位の Hom 写像を関手圏内の普遍余錐の全単射へ移す。
規約：余極限関手と全単位の選択を保持する。
使われ方：有限余積の全関手による余極限保存と指定比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 概要：選んだ余極限単位の全パラメータの Hom 写像は全単射。
方針：変数交換の同値と native な普遍余錐の Hom 全単射を合成する。
規約：同じ指定単位を使う。
使われ方：余極限と定値図式の随伴判定。 -/
lemma chosenColimitUnitHom_bijective {K A X : SSet.{u}} [Quasicategory X] [Quasicategory A]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (U : A ⟶ (ihom K).obj X) (V : A ⟶ X) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitUnitHom K X hX) U V) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.parameterUnitHomMap_bijective_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitUnitHom K X hX) U V).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.colimitUnitHom_bijective_of_flip (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isColimit hX U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_vertex hX U)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitUnitHom K X hX) U V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitUnitHomMap_flip hX U V))

/-- 概要：選んだ余極限関手と定値図式関手の実際の随伴。
方針：指定した全単位の全 Hom 全単射を随伴の単位判定へ適用する。
規約：元の余極限関手を変更しない。
使われ方：有限余積の全関手の余極限保存。 -/
def chosenColimitAdjunction (K X : SSet.{u}) [Quasicategory X]
    (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor K X hX) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitHomBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitUnitHom K X hX)
    (chosenColimitUnitHom_bijective hX)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
