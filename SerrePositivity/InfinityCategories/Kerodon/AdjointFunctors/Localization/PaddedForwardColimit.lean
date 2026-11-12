module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPaddedCollapse

/-!
# padding した forward 部分語の余極限と元の三列

概要：元の三列の値を余極限として回収し、元の包含による比較の後の像を照合する。
方針：一列への普遍性と元の三列の語の等式を合成し、逆射は標準包含で検査する。
規約：元の自然変換の colimMap への一致を証明する。
使われ方：分数計算の比較を元の三本矢の標準射へ移す工程。

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
  [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)]

def paddedForwardColimitIso :
    colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) ≅ H.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardColimitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) ≪≫ H.mapIso (eqToIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward)

lemma paddedForwardColimitIso_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) a ≫
        (paddedForwardColimitIso H).hom = H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedCollapse a) := by
  change colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)) a ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardColimitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)).hom ≫
      (H.mapIso (eqToIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward)).hom) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardColimitIso_fac]
  change H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a)) ≫
    H.map (eqToHom _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward) = H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedCollapse a)
  exact (CategoryTheory.Functor.map_comp H _ _).symm

lemma paddedForwardColimitIso_inv_comparison [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)] :
    (paddedForwardColimitIso H).inv ≫ colimMap
        (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)) =
      H.map (eqToHom _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward.symm) ≫
        colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) := by
  have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardColimitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)).inv ≫ colimMap
      (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)) =
        colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) := by
    apply (cancel_epi ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H).mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardSingleIso).hom).1
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardColimitIso_inv_fac, ι_colimMap]
    rfl
  change ((H.mapIso (eqToIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.padding_single_forward)).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardColimitIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)).inv) ≫ colimMap
      (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)) = _
  rw [Category.assoc, hi]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
