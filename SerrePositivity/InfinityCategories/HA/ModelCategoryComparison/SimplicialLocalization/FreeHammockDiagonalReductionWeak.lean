module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeWordDiagonalWeak
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockDiagonal
public import SerrePositivity.EInfinity.Hammock.WordDiagonalProper
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DoubleSimplicialColimit
public import SerrePositivity.EInfinity.Hammock.WeakProperColimit

/-!
# 元の自由 hammock 対角の左比較射自身の弱同値性

概要：元の全語の比較を proper 余極限と同じ対角・余極限の交換で移す。
方針：各標準射で元の augmentation の可換式を証明し、同じ比較射を回収する。
規約：全語の filtered 性や各自由次数の通常の hammock 比較の弱同値性は仮定しない。
使われ方：DK命題2.2の実際の左右比較を完成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
def freeHammockDiagonalColimitIso :
    colimit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockWordDiagram C X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor) ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal C X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalColimitIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockWordDiagram C X Y)
lemma freeHammockDiagonalAugmentation_inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map ((pointwiseCocone (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockWordDiagram C X Y)).ι.app w) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y).app w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion C.weakEquivalences X Y w := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  have h := colimit.ι_map ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockGraphAugmentation C X Y).app n) w
  exact ConcreteCategory.congr_hom (congrArg (fun k :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences w
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y => k.app n) h) σ
lemma freeHammockDiagonalColimitIso_augmentation :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalColimitIso C X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y =
      colim.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y) := by
  apply colimit.hom_ext
  intro w
  change colimit.ι (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockWordDiagram C X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor) w ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalColimitIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockWordDiagram C X Y)).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalColimitIso_ι, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation_inclusion,
    colimit.ι_map]
  rfl
lemma freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X Y) := by
  have hc := weakProperColimitMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation C X Y)
    (FixedObjectDiagram.wordDiagonalDiagram_proper (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) C
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C) (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) X Y)
    (graphDiagram_proper C.weakEquivalences X Y)
    (fun w => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeWordDiagonalAugmentation_weak C w X Y)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalColimitIso C X Y)).isWeakHomotopyEquivalence.cancel_left
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalColimitIso_augmentation]
  exact hc
lemma freeHammockDiagonalReduction_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
      (reducedColimitIso C.weakEquivalences X Y)).isWeakHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
