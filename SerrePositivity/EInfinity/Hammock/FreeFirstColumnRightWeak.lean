module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnHomWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomRepresentation

/-!
# 元の自由解像の二方向比較の右 Hom 係数の弱同値性

概要：元の右係数の対角比較射自身を底の通常の Hom augmentation へ回収する。
方針：全作用素と実際の射を離散圏の nerve の自然同型で照合する。
規約：右係数の弱同値性を仮定せず、同じ元の射の正方形で証明する。
使われ方：DK10.4–10.6の右係数の具体的な入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeFirstRightNerveDiagramIso :
    rightDiagram (D := freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeFirstMarkedObjectEquiv_naturality C w X Y) Z ⋙ nerveFunctor ≅
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHom C X Z ⋙ Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents (fun n => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n Z)) (by
      intro n m θ
      ext k σ
      have hZ : (eqToHom (freeFirstMarkedObjectEquiv_naturality C w X Y θ Z)).hom =
          eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ Z) :=
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom (C := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m) _
      change ((eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X).symm ≫
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ).functor.map (σ.obj 0).as) ≫
          (eqToHom (freeFirstMarkedObjectEquiv_naturality C w X Y θ Z)).hom) =
        eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X).symm ≫
          ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ).functor.map (σ.obj 0).as ≫
            eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ Z)
      simp only [hZ, Category.assoc])

def freeFirstTargetRightNerveDiagramIso :
    rightDiagram (D := (Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y) (freeFirstTargetObjectEquiv_naturality C w X Y) Z ⋙
        nerveFunctor ≅
      ((Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Z)) ⋙ Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents (fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso.iso (X ⟶ Z)) (by
    intro n m θ
    ext k σ
    change (σ.obj 0).as ≫ (𝟙 Z) = (σ.obj 0).as
    exact Category.comp_id _)

def freeFirstRightSpaceIso :
    rightSpace (freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeFirstMarkedObjectEquiv_naturality C w X Y) Z ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHom C X Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (freeFirstRightNerveDiagramIso C w X Y Z) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso _
def freeFirstTargetRightSpaceIso :
    rightSpace ((Functor.const SimplexCategoryᵒᵖ).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardData C w X Y))
      (freeFirstTargetObjectEquiv C w X Y) (freeFirstTargetObjectEquiv_naturality C w X Y) Z ≅
        (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalFunctor.mapIso (freeFirstTargetRightNerveDiagramIso C w X Y Z) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagonalDiscreteIso _
def freeFirstRightSpaceMap :=
  rightSpaceMap (freeFirstMarkedObjectEquiv C) (freeFirstTargetObjectEquiv C w X Y)
    (freeFirstMarkedObjectEquiv_naturality C w X Y)
    (freeFirstTargetObjectEquiv_naturality C w X Y) (freeForwardForwardAugmentation C w X Y)
    (freeFirstMarkedObjectEquiv_augmentation C w X Y) Z

lemma freeFirstRightSpaceIso_augmentation :
    (freeFirstRightSpaceIso C w X Y Z).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomAugmentation C X Z =
      freeFirstRightSpaceMap C w X Y Z ≫ (freeFirstTargetRightSpaceIso C w X Y Z).hom := by
  ext n σ
  have hZ : (eqToHom (freeFirstMarkedObjectEquiv_augmentation C w X Y n Z)).hom =
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z) :=
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.marked_eqToHom_hom (C := C) _
  change (eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X).symm ≫
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).functor.map (σ.obj 0).as ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n Z)) =
    ((eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_augmentation C n X).symm ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).functor.map (σ.obj 0).as) ≫
        (eqToHom (freeFirstMarkedObjectEquiv_augmentation C w X Y n Z)).hom)
  simp only [hZ, Category.assoc]

lemma freeFirstRightSpaceMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeFirstRightSpaceMap C w X Y Z) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeFirstRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionHomAugmentation_isWeakHomotopyEquivalence C X Z)
  rw [freeFirstRightSpaceIso_augmentation] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeFirstTargetRightSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right h
end SerrePositivity.EInfinity.Hammock.FirstColumn
