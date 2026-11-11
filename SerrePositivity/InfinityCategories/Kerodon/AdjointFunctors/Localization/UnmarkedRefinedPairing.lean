module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRefinementSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFixedAppendFunctor

/-!
# 元の refined 全図式と同じ三因子の合成関手

概要：内部切断の元の全図式を prefix・同じ生成射・残りの連結関手として回収する。
方針：固定端点での連結関手と元の一定の生成射の全縦成分を照合する。
規約：元の全行・全縦射・同じ生成矢を保持する。
使われ方：一段の貼り戻しが元の標準射へ戻る式。

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
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

lemma generator_fixedFunctor : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ i h).fixedFunctor =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).hom.toPath n := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ i h).fixedFunctor =
    (Functor.const (Fin (n.unop.len + 1))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W.paths) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).hom.toPath)
  refine CategoryTheory.Functor.ext (F := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ i h).fixedFunctor)
    (G := (Functor.const (Fin (n.unop.len + 1))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W.paths) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).hom.toPath)) (fun _ => rfl) ?_
  intro d e f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  change Fin 2 at j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => rfl

lemma refinedFunctor_pair : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W τ i h =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixFunctor W τ i h).prod' (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).hom.toPath n) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor).prod' (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W τ i h) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ i h)).append
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h)).fixedFunctor = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_fixedFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_fixedFunctor, generator_fixedFunctor]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
