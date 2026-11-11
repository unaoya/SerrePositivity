module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteProjection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 元の有限包の全語の作用と二方向の整合

概要：有限部分集合の包含と全体への射影が元の全語の作用と可換となる。
方針：既存の相対関手の固定端点での全語の自然性を使う。
規約：元の全列と全縦射を保持した厳密な関手の等式を使う。
使われ方：有限部分集合と Word の二変数の図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def wordActionFunctor (S : Finset Q) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.termCategory T X Y a S ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.termCategory T X Y b S := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f

lemma wordActionFunctor_id (S : Finset Q) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    wordActionFunctor T X Y S (𝟙 a) = 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.termCategory T X Y a S) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_id

lemma wordActionFunctor_comp (S : Finset Q) {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (g : b ⟶ c) :
    wordActionFunctor T X Y S (f ≫ g) =
      wordActionFunctor T X Y S f ⋙ wordActionFunctor T X Y S g := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition.functor_comp f g

lemma mapFunctor_wordAction {S R : Finset Q} (h : S ⊆ R) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y a h ⋙ wordActionFunctor T X Y R f =
      wordActionFunctor T X Y S f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.mapFunctor T X Y b h := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y R)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_fixedFunctor_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subsetRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_mono T X Y h)) rfl rfl f

lemma projectionFunctor_wordAction (S : Finset Q) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f =
      wordActionFunctor T X Y S f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y b S := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_fixedFunctor_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S))
    rfl rfl f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
