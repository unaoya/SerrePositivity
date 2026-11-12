module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedZeroAttachments

/-!
# 元の貼り戻しの接合点関手の元の生成矢の端点への回収

概要：生成位置で切り出した接合点関手は元の同じ生成矢の端点の定数関手である。
方針：元の内部接続の関手等式と最小位置・同じ Total 生成矢の回収を結合する。
規約：元の全対象・全縦射を含む関手の等式である。
使われ方：前後の全図式の端点表示を含む同定。
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

lemma sourceJoint_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W (simplex W g σ τ) (columnIndex a b) =
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.left) := by
  let h := simplex_nonempty W g σ τ
  obtain ⟨he, _⟩ := leftAttachment_eqToHom W g σ τ h
  have hi := simplex_firstColumn W g σ τ h
  have hg := simplex_generator W g σ τ h
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W (simplex W g σ τ)) hi).symm.trans
    (he.trans (congrArg (fun t : Quiver.Total C =>
      (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.left)) hg))

lemma targetJoint_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W (simplex W g σ τ) (columnIndex a b) =
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from g.val.right) := by
  let h := simplex_nonempty W g σ τ
  obtain ⟨he, _⟩ := rightAttachment_eqToHom W g σ τ h
  have hi := simplex_firstColumn W g σ τ h
  have hg := simplex_generator W g σ τ h
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W (simplex W g σ τ)) hi).symm.trans
    (he.symm.trans (congrArg (fun t : Quiver.Total C =>
      (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from t.right)) hg))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
