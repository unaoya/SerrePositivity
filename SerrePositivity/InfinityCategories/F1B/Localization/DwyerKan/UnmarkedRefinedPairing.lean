module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedRefinementSimplex
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFixedAppendFunctor

/-!
# 元の refined 全図式と同じ三因子の合成関手

概要：内部切断の元の全図式を prefix・同じ生成射・残りの連結関手として回収する。
方針：固定端点での連結関手と元の一定の生成射の全縦成分を照合する。
規約：元の全行・全縦射・同じ生成矢を保持する。
使われ方：一段の貼り戻しが元の標準射へ戻る式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length) (h : column W (τ.obj 0) i ≠ [])

lemma generator_fixedFunctor : (generatorBlock W τ i h).fixedFunctor =
    arrowSimplex W.paths (rowGenerator W τ i h).hom.toPath n := by
  change (generatorBlock W τ i h).fixedFunctor =
    (Functor.const (Fin (n.unop.len + 1))).obj
      (ForwardZigzag.obj (W := W.paths) (rowGenerator W τ i h).hom.toPath)
  refine CategoryTheory.Functor.ext (F := (generatorBlock W τ i h).fixedFunctor)
    (G := (Functor.const (Fin (n.unop.len + 1))).obj
      (ForwardZigzag.obj (W := W.paths) (rowGenerator W τ i h).hom.toPath)) (fun _ => rfl) ?_
  intro d e f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Zigzag.hom_ext
  intro j
  change Fin 2 at j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => rfl

lemma refinedFunctor_pair : refinedFunctor W τ i h =
    ((prefixFunctor W τ i h).prod' (arrowSimplex W.paths (rowGenerator W τ i h).hom.toPath n) ⋙
      ZigzagAppend.functor).prod' (residualFunctor W τ i h) ⋙ ZigzagAppend.functor := by
  change (((prefixDiagram W τ i h).append (generatorBlock W τ i h)).append
    (residualDiagram W τ i h)).fixedFunctor = _
  rw [append_fixedFunctor, append_fixedFunctor, generator_fixedFunctor]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
