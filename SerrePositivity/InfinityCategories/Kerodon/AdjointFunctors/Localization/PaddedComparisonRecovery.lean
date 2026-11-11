module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PaddedForwardColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PaddingColimitRetraction

/-!
# 元の三列の比較から全語の標準射の回収

概要：padding 図式への元の三列の射は、元の全語の標準射を厳密に回収する。
方針：余極限比較の逆射の式と、元の padding 余錐の標準射への一致を使う。
規約：三列の語の等式による移送を含め、同じ元の射の等式を証明する。
使われ方：分数計算で得る比較の弱同値を元の hammock の標準射へ移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (H : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ C)
  [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)]

def paddedThreeComparison : H.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ⟶ colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) :=
  H.map (eqToHom _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward.symm) ≫
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)

lemma paddedThreeComparison_fac [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedForwardColimitIso H).inv ≫ colimMap
        (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)) =
      paddedThreeComparison H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedForwardColimitIso_inv_comparison H

lemma paddedThreeComparison_retraction [HasColimit H] :
    paddedThreeComparison H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitRetraction H = colimit.ι H _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow := by
  change (H.map (eqToHom _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward.symm) ≫
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitRetraction H = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitRetraction_fac]
  exact colimit.w H (eqToHom _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward.symm)

lemma paddedForwardColimit_comparison_recovery [HasColimit H]
    [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)] :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedForwardColimitIso H).inv ≫ colimMap
        (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitRetraction H = colimit.ι H _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow := by
  rw [← Category.assoc, paddedThreeComparison_fac, paddedThreeComparison_retraction]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
