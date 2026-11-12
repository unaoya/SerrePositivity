module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeUnitHomNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SSetProductEvaluation

/-!
概要：定値標的への射の頂点評価と定値化を、端点の表示を保って比較する。
方針：既存の評価自然性に等式の同型を補い、輸送を簡約する。
規約：標的の充填性を仮定しない。
使われ方：余錐単位による Hom 因子化。

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

/-- 概要：頂点評価の定値化は、同じ頂点での定値前合成の端点輸送に一致する。
方針：評価の公式と定値二胞体の定義を用い、端点の輸送を相殺する。
規約：指定した射そのものを保持する。
使われ方：普遍余錐の単位との自然性。 -/
lemma constantEvaluationHom_transport {A B X : SSet.{u}} (H : B ⟶ X)
    (x : B _⦋0⦌) (y : X _⦋0⦌) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x ≫
      eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply y x))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (SSet.const_comp x H)
      (SSet.comp_const (SSet.const x : A ⟶ B) y)
      ((hoFunctor.map ((pre (SSet.const x : A ⟶ B)).app X)).toFunctor.map α) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_constantFunctorHomMap A α x]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap, eqToHom_map, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 概要：図式端点の等式による Hom 輸送は合成を保つ。
方針：同じ中間同型を相殺する一般の Hom 共役の公式を使う。
規約：三つの端点を明示する。
使われ方：余錐の底と頂点での単位の因子化。 -/
lemma functorHomCongr_comp {A X : SSet.{u}} {U V W U' V' W' : A ⟶ X}
    (hU : U = U') (hV : V = V') (hW : W = W')
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hW (α ≫ β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hU hV α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hV hW β :=
  Iso.homCongr_comp _ _ _ α β

/-- 概要：頂点への形状ホモトピーの単位と頂点評価は底制限を与える。
方針：一般の端点輸送の合成公式で前合成自然性を移す。
規約：形状とホモトピーを抽象のまま保持する。
使われ方：native な余錐の単位への適用。 -/
lemma constantEndpointUnitHom_evaluation {A B X : SSet.{u}}
    {f : A ⟶ B} (x : B _⦋0⦌) (T : SSet.Homotopy f (SSet.const x))
    (H : B ⟶ X) {p : A ⟶ X} (hp : f ≫ H = p)
    (y : X _⦋0⦌) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H (SSet.const y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hp (SSet.const_comp x H)
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp T H))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x ≫
        eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply y x))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hp (SSet.comp_const f y)
      ((hoFunctor.map ((pre f).app X)).toFunctor.map α) := by
  rw [constantEvaluationHom_transport]
  exact (functorHomCongr_comp hp (SSet.const_comp x H) (SSet.comp_const _ y) _ _).symm.trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hp (SSet.comp_const f y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precompositionHomotopy_constant_naturality T H y α).symm)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
