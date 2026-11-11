module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategoryLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverPathRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverProjectionEmbedding

/-!
# 元の有限包から全体への固定端点の射影

概要：各有限包から全体への元の包含が全ての有限部分集合の遷移と可換となる。
方針：元の自由関手の射影の等式を固定端点の相対関手へ移す。
規約：元の各行・全縦射と同じ全体への射影を使う。
使われ方：全被覆への余錐と全次数の単射性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def projectionFunctor (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (S : Finset Q) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.termCategory T X Y a S ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) a ((Paths.of Q).obj X) ((Paths.of Q).obj Y) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)) rfl rfl

lemma mapFunctor_projection (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {S R : Finset Q} (h : S ⊆ R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y a h ⋙ projectionFunctor T X Y a R = projectionFunctor T X Y a S := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y R)
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subsetRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_mono T X Y h)
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y R)
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (F.comp G) rfl rfl :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_comp F G rfl rfl rfl rfl).symm
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor_congr
      (F := F.comp G) (G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)) (w := a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subsetFunctor_pathInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_mono T X Y h))
        rfl rfl rfl rfl

lemma projectionFunctor_obj_injective (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (S : Finset Q) :
    Function.Injective (projectionFunctor T X Y a S).obj := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagProjection_obj_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S) a _ _

lemma projectionFunctor_faithful (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (S : Finset Q) :
    (projectionFunctor T X Y a S).Faithful := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagProjection_faithful (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S) a _ _

lemma projection_nerve_injective (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (S : Finset Q) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((nerveMap (projectionFunctor T X Y a S)).app n) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphProjection_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S) a n _ _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
