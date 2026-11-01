module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedIdentityDiagrams
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzagConstantDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFixedAppendFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitFunctor

/-!
# 元の切断因子の関手と恒等列付き元の関手の比較

概要：固定した全端点の実際の prefix・残りの関手を回収する。
方針：元の全図式の比較を fixedFunctor へ移し、一列の一定関手を照合する。
規約：元の選択生成矢の端点の表示変更を保持する。
使われ方：同じ元の標準射による二因子の余極限の点の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory Zigzag.MovingDiagram

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : FactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma selected_prefix_word :
    Word.CutFactor.prefixWord (Word.append (Word.append a (Word.single .forward)) b)
      (AttachedPrefix.index W (simplex W g σ τ) h) = Word.append a (Word.single .forward) :=
  (congrArg (Word.CutFactor.prefixWord (Word.append (Word.append a (Word.single .forward)) b))
    (simplex_firstColumn W g σ τ h)).trans (prefix_word a b)

lemma selected_residual_word :
    Word.CutFactor.residualWord (Word.append (Word.append a (Word.single .forward)) b)
      (AttachedPrefix.index W (simplex W g σ τ) h) = Word.append (Word.single .forward) b :=
  (congrArg (Word.CutFactor.residualWord (Word.append (Word.append a (Word.single .forward)) b))
    (simplex_firstColumn W g σ τ h)).trans (residual_word a b)

lemma prefix_identity_functor :
    HEq (Attachments.prefixFunctor W (simplex W g σ τ)
      (AttachedPrefix.index W (simplex W g σ τ) h) (AttachedPrefix.nonempty W _ h))
      ((((AllMarked.graphMap W X g.val.left a).app n σ).prod'
        (arrowSimplex W.paths (𝟙 (show Paths C from g.val.left)) n)) ⋙ ZigzagAppend.functor) := by
  have hg := congrArg (fun t : Quiver.Total C => (show Paths C from t.left))
    (simplex_generator W g σ τ h)
  have he := fixedFunctor_heq (selected_prefix_word W g σ τ h) rfl hg _ _
    (prefix_identity_diagram W g σ τ h)
  rw [append_fixedFunctor, ofFunctor_fixedFunctor,
    ForwardZigzag.identity_diagram_fixedFunctor] at he
  exact he

lemma residual_identity_functor :
    HEq (Attachments.residualFunctor W (simplex W g σ τ)
      (AttachedPrefix.index W (simplex W g σ τ) h) (AttachedPrefix.nonempty W _ h))
      ((arrowSimplex W.paths (𝟙 (show Paths C from g.val.right)) n).prod' τ ⋙
        ZigzagAppend.functor) := by
  have hg := congrArg (fun t : Quiver.Total C => (show Paths C from t.right))
    (simplex_generator W g σ τ h)
  have he := fixedFunctor_heq (selected_residual_word W g σ τ h) hg rfl _ _
    (residual_identity_diagram W g σ τ h)
  rw [append_fixedFunctor, ofFunctor_fixedFunctor,
    ForwardZigzag.identity_diagram_fixedFunctor] at he
  exact he

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
