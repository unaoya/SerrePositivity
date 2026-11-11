module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowFactorizationSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingPrecompLaws

/-!
# 元の内部接続自然変換と全単体作用素

概要：前後の接合点と内部切断を繋ぐ元の自然変換を、再添字へ照合する。
方針：語の切断の再添字と元の行の因子化の単体的整合を使う。
規約：元の接合点関手と生成矢の端点の表示を保持する。
使われ方：prefix・残りの全図式の単体的整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma beforeDiagram_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W τ i).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit.before_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

lemma afterDiagram_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W τ i).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit.after_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

lemma sourceJoint_simplex : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.sourceJoint W τ i :=
  congrArg (fun F => F.leftPart.jointFunctor)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit.expanded_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ))

lemma targetJoint_simplex : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.targetJoint W τ i :=
  congrArg (fun F => F.jointFunctor)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnSplit.expanded_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ))

lemma whiskerLeft_eqToHom {D E : Type*} [Category D] [Category E]
    (K : D ⥤ E) {A B : E ⥤ Paths C} (e : A = B) :
    Functor.whiskerLeft K (eqToHom e) = eqToHom (congrArg (fun F => K ⋙ F) e) := by
  cases e
  rfl

lemma leftAttachment_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment]
  rw [Functor.whiskerLeft_comp, whiskerLeft_eqToHom]
  simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix_simplex W τ i h θ hθ

lemma rightAttachment_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W τ i h)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment]
  rw [Functor.whiskerLeft_comp, whiskerLeft_eqToHom]
  simp only [comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual_simplex W τ i h θ hθ

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
