module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFiniteGraphColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram

/-!
# 固定語の元の余極限同型の全語での自然性

概要：元の全標準射を回収する同型を Word の図式の自然同型へ束ねる。
方針：元の有限部分集合の標準射上で射影の全語の整合を検査する。
規約：元の全体の graph 図式へ同じ作用で戻る。
使われ方：二つの元の余極限の交換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def graphColimitDiagramIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y ⋙ colim ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q))
      ((Paths.of Q).obj X) ((Paths.of Q).obj Y) :=
  NatIso.ofComponents (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso T X Y) (fun {a b} f => by
    let τ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y b := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).map f
    change colim.map τ ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso T X Y b).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso T X Y a).hom ≫ nerveMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := ⊤) (X := (Paths.of Q).obj X) (Y := (Paths.of Q).obj Y) f)
    apply colimit.hom_ext
    intro S
    change colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a) S ≫ colim.map τ ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso T X Y b).hom = colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a) S ≫
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso T X Y a).hom ≫ nerveMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := ⊤) (X := (Paths.of Q).obj X) (Y := (Paths.of Q).obj Y) f)
    rw [← Category.assoc, colimit.ι_map, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso_fac,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso_fac]
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordActionFunctor T X Y S f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y b S) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    exact congrArg nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor_wordAction T X Y S f).symm)

lemma wordDiagram_eq (S : Finset Q) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).flip.obj S =
      letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.left T X Y S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.right T X Y S) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory.hull T X Y S)
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite
