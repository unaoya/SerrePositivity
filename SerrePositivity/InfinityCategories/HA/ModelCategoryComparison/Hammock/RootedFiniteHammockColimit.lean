module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFiniteGraphColimitNaturality
public import Mathlib.CategoryTheory.Limits.Fubini
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 全体の元の hammock と有限包の hammock の余極限の同型

概要：元の二方向の余極限を交換して同じ全語の hammock を回収する。
方針：元の固定語の余極限自然同型と Fubini 同型を合成する。
規約：元の各有限集合・各語の標準射を保持する。
使われ方：有限包の可縮性を全被覆へ移す。
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

def hammockDiagram : Finset Q ⥤ SSet.{max u v} := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).flip ⋙ colim

def hammockColimitIso : colimit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockDiagram T X Y) ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj X) ((Paths.of Q).obj Y) :=
  colimitFlipCompColimIsoColimitCompColim (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y) ≪≫
    colim.mapIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitDiagramIso T X Y)

lemma hammockColimitIso_fac (S : Finset Q) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).flip.obj S) a ≫
      colimit.ι (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockDiagram T X Y) S ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.hammockColimitIso T X Y).hom =
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (Paths Q))
            ((Paths.of Q).obj X) ((Paths.of Q).obj Y) a := by
  change colimit.ι ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).flip.obj S) a ≫
    colimit.ι ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y).flip ⋙ colim) S ≫
      ((colimitFlipCompColimIsoColimitCompColim (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteBidiagram.graphWordDiagram T X Y)).hom ≫
        colim.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitDiagramIso T X Y).hom) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectionFunctor T X Y a S) ≫ colimit.ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q))
        ((Paths.of Q).obj X) ((Paths.of Q).obj Y)) a
  rw [colimitFlipCompColimIsoColimitCompColim_ι_ι_hom_assoc]
  rw [colimit.ι_map]
  change colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteDiagram.graphDiagram T X Y a) S ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso T X Y a).hom ≫ _ = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite.graphColimitIso_fac]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RootedFinite
