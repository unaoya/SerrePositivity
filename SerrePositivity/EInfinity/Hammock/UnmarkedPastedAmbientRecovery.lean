module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedIdentityFunctors
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.EndpointColimitHEq
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitIdentityPoint

/-!
# 元の貼り戻しの二因子の ambient hammock の点の回収

概要：切断した prefix と残りの標準射の像を元の二点へ回収する。
方針：全関手の異種等式を同じ標準射へ渡し、元の合成単位則を使う。
規約：語の値だけでなく実際の全語の余極限の点を回収する。
使われ方：指定部分圏での prefix の反映と逆向きの因子回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : FactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma prefix_ambient_point :
    let η := simplex W g σ τ
    let i := AttachedPrefix.index W η h
    let A : Paths C := (FirstFactor.generator W η h).val.left
    let e : A = g.val.left := congrArg (fun t : Quiver.Total C =>
      (show Paths C from t.left)) (simplex_generator W g σ τ h)
    (EndpointChange.colimitMap W.paths rfl e).app n
      ((graphInclusion W.paths X A (Word.CutFactor.prefixWord _ i)).app n
        (Attachments.prefixFunctor W η i (AttachedPrefix.nonempty W _ h))) =
      (graphInclusion W.paths X g.val.left a).app n
        ((AllMarked.graphMap W X g.val.left a).app n σ) := by
  dsimp only
  exact (EndpointChange.image_heq W.paths (selected_prefix_word W g σ τ h) rfl _ _ _
    (prefix_identity_functor W g σ τ h)).trans
    ((composePoint_inclusions W.paths X g.val.left g.val.left a (Word.single .forward)
      ((AllMarked.graphMap W X g.val.left a).app n σ)
      (arrowSimplex W.paths (𝟙 (show Paths C from g.val.left)) n)).symm.trans
        (composePoint_identity_right W.paths _))

lemma residual_ambient_point :
    let η := simplex W g σ τ
    let i := AttachedPrefix.index W η h
    let B : Paths C := (FirstFactor.generator W η h).val.right
    let e : B = g.val.right := congrArg (fun t : Quiver.Total C =>
      (show Paths C from t.right)) (simplex_generator W g σ τ h)
    (EndpointChange.colimitMap W.paths e rfl).app n
      ((graphInclusion W.paths B Y (Word.CutFactor.residualWord _ i)).app n
        (Attachments.residualFunctor W η i (AttachedPrefix.nonempty W _ h))) =
      (graphInclusion W.paths g.val.right Y b).app n τ := by
  dsimp only
  exact (EndpointChange.image_heq W.paths (selected_residual_word W g σ τ h) _ rfl _ _
    (residual_identity_functor W g σ τ h)).trans
    ((composePoint_inclusions W.paths g.val.right g.val.right Y (Word.single .forward) b
      (arrowSimplex W.paths (𝟙 (show Paths C from g.val.right)) n) τ).symm.trans
        (composePoint_identity_left W.paths _))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
