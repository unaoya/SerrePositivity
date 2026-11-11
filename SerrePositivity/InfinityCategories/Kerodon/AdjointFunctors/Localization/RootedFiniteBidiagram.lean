module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteWordAction

/-!
# 元の有限部分集合と全語の二変数の graph 図式

概要：元の二方向の作用を strict な単体集合値図式へ束ねる。
方針：同じ元の nerve と全語の作用の可換性を使う。
規約：どちらの方向でも元の標準射を保持する。
使われ方：二つの元の余極限の交換。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram
open CategoryTheory Limits
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def graphWordDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ Finset Q ⥤ SSet.{max u v} where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a
  map f :=
    { app S := nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S f)
      naturality S R h := by
        change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y _ (leOfHom h) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y R f) =
          nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y _ (leOfHom h))
        exact congrArg nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mapFunctor_wordAction T X Y (leOfHom h) f) }
  map_id a := by
    apply NatTrans.ext
    funext S
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S (𝟙 a)) = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor_id]
    exact nerveFunctor.map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.termCategory T X Y a S)
  map_comp f g := by
    apply NatTrans.ext
    funext S
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S (f ≫ g)) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S f) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S g)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor_comp]
    exact nerveFunctor.map_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S f).toCatHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S g).toCatHom

def graphWordProjection : graphWordDiagram T X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q))
      ((Paths.of Q).obj X) ((Paths.of Q).obj Y) ⋙
      Functor.const (Finset Q) where
  app a := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphCocone T X Y a).ι
  naturality a b f := by
    apply NatTrans.ext
    funext S
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y b S) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    exact congrArg nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor_wordAction T X Y S f).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram
