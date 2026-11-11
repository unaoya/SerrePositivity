module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeWordDiagonalWeak
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockDiagonal
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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory CategoryTheory.Limits Hammock
open SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
def freeHammockDiagonalColimitIso :
    colimit (freeHammockWordDiagram C X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor) ≅ freeHammockDiagonal C X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalColimitIso (freeHammockWordDiagram C X Y)
lemma freeHammockDiagonalAugmentation_inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.map ((pointwiseCocone (freeHammockWordDiagram C X Y)).ι.app w) ≫
      freeHammockDiagonalAugmentation C X Y =
    (freeWordDiagonalAugmentation C X Y).app w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion C.weakEquivalences X Y w := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  have h := colimit.ι_map ((freeHammockGraphAugmentation C X Y).app n) w
  exact ConcreteCategory.congr_hom (congrArg (fun k :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph ((freeResolution C).obj n).weakEquivalences w
        (freeResolutionObject C n X) (freeResolutionObject C n Y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y => k.app n) h) σ
lemma freeHammockDiagonalColimitIso_augmentation :
    (freeHammockDiagonalColimitIso C X Y).hom ≫ freeHammockDiagonalAugmentation C X Y =
      colim.map (freeWordDiagonalAugmentation C X Y) := by
  apply colimit.hom_ext
  intro w
  change colimit.ι (freeHammockWordDiagram C X Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor) w ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalColimitIso (freeHammockWordDiagram C X Y)).hom ≫
      freeHammockDiagonalAugmentation C X Y) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalColimitIso_ι, freeHammockDiagonalAugmentation_inclusion,
    colimit.ι_map]
  rfl
lemma freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeHammockDiagonalAugmentation C X Y) := by
  have hc := weakProperColimitMap (freeWordDiagonalAugmentation C X Y)
    (FixedObjectDiagram.wordDiagonalDiagram_proper (freeResolution C) C
      (freeResolutionObject C) (fun θ X => freeResolutionObject_naturality C θ X) X Y)
    (graphDiagram_proper C.weakEquivalences X Y)
    (fun w => freeWordDiagonalAugmentation_weak C w X Y)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeHammockDiagonalColimitIso C X Y)).isWeakHomotopyEquivalence.cancel_left
  rw [freeHammockDiagonalColimitIso_augmentation]
  exact hc
lemma freeHammockDiagonalReduction_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeHammockDiagonalReduction C X Y) :=
  (freeHammockDiagonalAugmentation_isWeakHomotopyEquivalence C X Y).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
      (reducedColimitIso C.weakEquivalences X Y)).isWeakHomotopyEquivalence
end SerrePositivity.EInfinity.SimplicialLocalization
