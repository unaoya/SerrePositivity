module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverPathRelative
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeObjectEmbedding

/-!
# 元の有限部分集合の hammock 射影の各次数の単射性

概要：元の有限自由圏の射影は全行と全図式を区別する。
方針：元の対象の単射性と射列の忠実性を相対関手へ適用する。
規約：同じ元の nerve の全単体を使う。
使われ方：有限支持の持ち上げの整合と余極限の単射性。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FiniteQuiver
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (S : Finset Q)

lemma pathInclusion_obj_injective : letI := quiver S
    Function.Injective (pathInclusion S).obj := by
  let := quiver S
  intro x y h
  change Vertex S at x y
  exact Subtype.ext h

lemma zigzagProjection_obj_injective (a : Word) : letI := quiver S
    ∀ X Y : Paths (Vertex S), Function.Injective
      (Zigzag.Relative.functor (w := a) (X := X) (Y := Y) (pathRelative S)).obj := by
  let := quiver S
  let : (pathRelative S).functor.Faithful := pathInclusion_faithful S
  intro X Y
  exact Zigzag.Relative.obj_injective (pathRelative S) (pathInclusion_obj_injective S)

lemma zigzagProjection_faithful (a : Word) : letI := quiver S
    ∀ X Y : Paths (Vertex S),
      (Zigzag.Relative.functor (w := a) (X := X) (Y := Y) (pathRelative S)).Faithful := by
  let := quiver S
  let : (pathRelative S).functor.Faithful := pathInclusion_faithful S
  intro X Y
  exact Zigzag.Relative.functor_faithful (pathRelative S)

lemma gridProjection_injective (a : Word) {I : Type w} [Category.{w'} I] : letI := quiver S
    ∀ X Y : Paths (Vertex S), Function.Injective
      (fun F : I ⥤ Zigzag (⊤ : MorphismProperty (Paths (Vertex S))) a X Y =>
        F ⋙ Zigzag.Relative.functor (pathRelative S)) := by
  let := quiver S
  let : (pathRelative S).functor.Faithful := pathInclusion_faithful S
  intro X Y
  exact Zigzag.Relative.postcompose_injective (pathRelative S) (pathInclusion_obj_injective S)

lemma graphProjection_injective (a : Word) (n : SimplexCategoryᵒᵖ) : letI := quiver S
    ∀ X Y : Paths (Vertex S), Function.Injective
      ((nerveMap (Zigzag.Relative.functor (w := a) (X := X) (Y := Y) (pathRelative S))).app n) := by
  let := quiver S
  intro X Y
  exact gridProjection_injective S a X Y

end SerrePositivity.EInfinity.Hammock.FiniteQuiver
