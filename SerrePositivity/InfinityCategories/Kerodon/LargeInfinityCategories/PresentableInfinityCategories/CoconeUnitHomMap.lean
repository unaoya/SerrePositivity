module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeUnitHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeApexHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConstantEvaluationHomTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.InitialBoundaryHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeWholeEdgeNaturality

/-!
概要：native な余錐の単位が与える頂点からの Hom 対応。
方針：形状ホモトピーを端点の等式で輸送し、右頂点評価の自然性を使う。
規約：指定した全余錐とその頂点を保つ。
使われ方：選んだ余極限関手と定値図式の随伴。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SSet.Truncated.HomotopyCategory

/-- 概要：元の全余錐の図式から定値頂点への単位。
方針：形状の標準ホモトピーの像の両端を輸送する。
規約：元の図式と native な頂点を保つ。
使われ方：普遍余錐の Hom の表示。 -/
def coconeUnitHom {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom p (SSet.const c.vertex) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr c.property (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cocone_const_rightApex c)
    (homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeDomainHomotopy K) c.val)))

/-- 概要：余錐単位と頂点評価の合成は底制限そのもの。
方針：定値標的への前合成自然性と評価の定値化の公式を合わせる。
規約：元の全余錐からの指定 Hom を使う。
使われ方：単位による普遍 Hom 写像の全単射性。 -/
lemma coconeUnitHom_evaluation {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (y : X _⦋0⦌) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom c.val (SSet.const y)) :
    coconeUnitHom c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K) ≫
        eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply y _))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr c.property (SSet.comp_const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) y)
      ((hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0])).app X)).toFunctor.map α) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constantEndpointUnitHom_evaluation (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRightApexVertex K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeDomainHomotopy K) c.val c.property y α

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
