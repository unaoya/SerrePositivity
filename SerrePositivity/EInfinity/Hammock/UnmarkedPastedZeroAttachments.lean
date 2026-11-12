module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedCutLength
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorWordZeroNatural

/-!
# 元の貼り戻しの内部接続列全体の恒等移送としての回収

概要：元の貼り戻しを切った左右の接続自然変換は、関手の等式による移送自身である。
方針：元の全行の切断の長さ零と自然性から全関手の等式を回収する。
規約：元の自然変換全体と元の全縦射を保持する。
使われ方：元の prefix と残りを恒等列の挿入による標準射へ照合する。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma leftAttachment_length_zero (d : Fin (n.unop.len + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h)).app d).length =
        0 := by
  change (((eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint_eq_rowSource W (simplex W g σ τ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h))).app d) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W (simplex W g σ τ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h)).app d).length = 0
  rw [eqToHom_app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_length_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_length_eqToHom, Nat.zero_add]
  exact cut_left_length_zero W g σ τ h d

lemma rightAttachment_length_zero (d : Fin (n.unop.len + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h)).app d).length =
        0 := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W (simplex W g σ τ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h)).app d ≫
    (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint_eq_rowTarget W (simplex W g σ τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h)).symm).app d).length = 0
  rw [eqToHom_app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_length_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_length_eqToHom, Nat.add_zero]
  exact cut_right_length_zero W g σ τ h d

lemma leftAttachment_eqToHom :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W (simplex W g σ τ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) =
      (Functor.const (Fin (n.unop.len + 1))).obj
        (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W (simplex W g σ τ) h).val.left),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W (simplex W g σ τ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h) = eqToHom e :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zeroNatTrans_eqToHom _ (leftAttachment_length_zero W g σ τ h)

lemma rightAttachment_eqToHom :
    ∃ e : (Functor.const (Fin (n.unop.len + 1))).obj
        (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W (simplex W g σ τ) h).val.right) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W (simplex W g σ τ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W (simplex W g σ τ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h) = eqToHom e :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zeroNatTrans_eqToHom _ (rightAttachment_length_zero W g σ τ h)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
