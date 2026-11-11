module

public import SerrePositivity.EInfinity.Hammock.SingleZigzagHomDiagram
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHomWeak

/-!
# 元の選択対象による指定 Hom の弱比較

概要：元の自由解像の固定 Hom augmentation を一列の比較へ接続する。
方針：同じ対象の表示を移す同型と元の augmentation の可換式を使う。
規約：元の比較射自身の弱同値性を証明する。
使われ方：DK5.7の全語の帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock.FixedObjectDiagram SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
def freeResolutionCanonicalMarkedHom : SSet.{u} :=
  backwardHomDiagram (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) Y X
lemma freeResolutionCanonicalMarkedObject_eq (n : SimplexCategoryᵒᵖ) (X : C.category) :
    markedObject (freeResolution C) (freeResolutionObject C) n X =
      freeResolutionMarkedObject C n X :=
  congrArg (fun Z => (⟨Z⟩ : WideSubcategory ((freeResolution C).obj n).weakEquivalences))
    (freeResolutionObject_eq_homObject C n X)
def freeResolutionCanonicalMarkedHomIso :
    freeResolutionCanonicalMarkedHom C X Y ≅ freeResolutionNativeMarkedHom C X Y where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (freeResolutionMarkedDiagram C)
    (freeResolutionMarkedDiagram C) (markedObject (freeResolution C) (freeResolutionObject C))
    (freeResolutionMarkedObject C)
    (markedObject_naturality (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X))
    (fun θ X => freeResolutionMarkedObject_naturality C θ X) (𝟙 _) id
    (freeResolutionCanonicalMarkedObject_eq C) X Y
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (freeResolutionMarkedDiagram C)
    (freeResolutionMarkedDiagram C) (freeResolutionMarkedObject C)
    (markedObject (freeResolution C) (freeResolutionObject C))
    (fun θ X => freeResolutionMarkedObject_naturality C θ X)
    (markedObject_naturality (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X)) (𝟙 _) id
    (fun n X => (freeResolutionCanonicalMarkedObject_eq C n X).symm) X Y
  hom_inv_id := by
    ext n f
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap]
  inv_hom_id := by
    ext n f
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap]
def freeResolutionCanonicalMarkedHomAugmentation : freeResolutionCanonicalMarkedHom C X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨X⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨Y⟩) :=
  (freeResolutionCanonicalMarkedHomIso C X Y).hom ≫ freeResolutionNativeMarkedHomAugmentation C X Y
lemma freeResolutionCanonicalMarkedHomAugmentation_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeResolutionCanonicalMarkedHomAugmentation C X Y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeResolutionCanonicalMarkedHomIso C X Y)).isWeakHomotopyEquivalence.comp
      (freeResolutionNativeMarkedHomAugmentation_isWeakHomotopyEquivalence C X Y)
end SerrePositivity.EInfinity.SimplicialLocalization
