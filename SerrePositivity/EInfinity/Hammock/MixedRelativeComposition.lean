module

public import SerrePositivity.EInfinity.Hammock.MixedRelativeColimitMap
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeAppendFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitPoints

/-!
# 異なる Hom の宇宙を持つ元の相対関手の合成保存

概要：全語の標準射で定めた元の写像が各次数の全ての合成を保つ。
方針：両変数の共同全射性と宇宙に依存しない元の連結関手の一致を使う。
規約：元の余極限と元の合成を使用する。
使われ方：cofibrant 包含と HomLift を通る元の比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.MixedRelative
open CategoryTheory
variable {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y Z : C} {n : SimplexCategoryᵒᵖ}

lemma graphInclusion_point {a : Word} (σ : (graph W a X Y).obj n) :
    (colimitMap F X Y).app n ((graphInclusion W X Y a).app n σ) =
      (graphInclusion V (F.functor.obj X) (F.functor.obj Y) a).app n
        (σ ⋙ Zigzag.Relative.functor F) :=
  congrArg (fun k => k.app n σ) (graphInclusion_colimitMap F X Y a)

lemma append_simplex {a b : Word} (σ : (graph W a X Y).obj n)
    (τ : (graph W b Y Z).obj n) :
    (σ.prod' τ ⋙ ZigzagAppend.functor) ⋙ Zigzag.Relative.functor F =
      (σ ⋙ Zigzag.Relative.functor F).prod' (τ ⋙ Zigzag.Relative.functor F) ⋙
        ZigzagAppend.functor := by
  rw [CategoryTheory.Functor.assoc, Zigzag.Relative.append_functor]
  rfl

lemma composePoint_map (p : (colimitGraph W X Y).obj n) (q : (colimitGraph W Y Z).obj n) :
    (colimitMap F X Z).app n (composePoint W X Y Z p q) =
      composePoint V (F.functor.obj X) (F.functor.obj Y) (F.functor.obj Z)
        ((colimitMap F X Y).app n p) ((colimitMap F Y Z).app n q) := by
  obtain ⟨a, σ, hp⟩ := colimit_point_surjective (graphDiagram W X Y) n p
  change (graphInclusion W X Y a).app n σ = p at hp
  cases hp
  obtain ⟨b, τ, hq⟩ := colimit_point_surjective (graphDiagram W Y Z) n q
  change (graphInclusion W Y Z b).app n τ = q at hq
  cases hq
  rw [composePoint_inclusions, graphInclusion_point, graphInclusion_point,
    graphInclusion_point, composePoint_inclusions]
  exact congrArg (fun H =>
    (graphInclusion V (F.functor.obj X) (F.functor.obj Z) (Word.append a b)).app n H)
      (append_simplex F σ τ)

end SerrePositivity.EInfinity.Hammock.MixedRelative
