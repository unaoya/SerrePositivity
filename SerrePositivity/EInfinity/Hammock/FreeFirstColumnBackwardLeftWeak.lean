module

public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardHomWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.DiscreteNerveIso
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionHomRepresentation

/-!
# 元の自由解像の二方向比較の左 Hom 係数の弱同値性

概要：元の左係数の対角比較射自身を底の指定 Hom augmentation へ回収する。
方針：全作用素と実際の射を離散圏の nerve の自然同型で照合する。
規約：左係数の弱同値性を仮定せず、同じ元の射の正方形で証明する。
使われ方：DK10.4–10.6の左係数の具体的な入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization SerrePositivity.InfinityCategories
open TwoSidedDiagram.FixedVertices
variable (C : RelativeCategory.{u}) (w : Word) (X Y Z : C.category)
def freeBackwardFirstLeftNerveDiagramIso :
    leftDiagram (D := freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ⋙ nerveFunctor ≅
    freeResolutionCanonicalMarkedHom C Z X ⋙ Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents (fun n => DiscreteNerve.iso
    ((freeFirstMarkedObjectEquiv C n Z) ⟶ (freeFirstMarkedObjectEquiv C n X))) (by
      intro n m θ
      ext k σ
      change ((eqToHom (congrArg op
          (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y θ Z))).unop ≫
        ((markedCategoryMap ((freeResolution C).map θ)).map (σ.obj 0).as ≫ eqToHom _)) =
        eqToHom _ ≫ (markedCategoryMap ((freeResolution C).map θ)).map (σ.obj 0).as ≫ eqToHom _
      rw [eqToHom_unop])

def freeBackwardFirstTargetLeftNerveDiagramIso :
    leftDiagram (D := (Functor.const SimplexCategoryᵒᵖ).obj (backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y) (freeBackwardFirstTargetObjectEquiv_naturality C
        w X Y) Z ⋙
        nerveFunctor ≅
      ((Functor.const SimplexCategoryᵒᵖ).obj ((⟨Z⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨X⟩)) ⋙
        Functor.const SimplexCategoryᵒᵖ :=
  NatIso.ofComponents (fun _ => DiscreteNerve.iso ((⟨Z⟩ : WideSubcategory C.weakEquivalences) ⟶
    ⟨X⟩)) (by
    intro n m θ
    ext k σ
    change (𝟙 (⟨Z⟩ : WideSubcategory C.weakEquivalences)) ≫ (σ.obj 0).as =
      (σ.obj 0).as
    exact Category.id_comp _)

def freeBackwardFirstLeftSpaceIso :
    leftSpace (freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ≅ freeResolutionCanonicalMarkedHom
        C Z X :=
  DoubleSimplicial.diagonalFunctor.mapIso (freeBackwardFirstLeftNerveDiagramIso C w X Y Z) ≪≫
    DoubleSimplicial.diagonalDiscreteIso _
def freeBackwardFirstTargetLeftSpaceIso :
    leftSpace ((Functor.const SimplexCategoryᵒᵖ).obj (backwardBackwardData C w X Y))
      (freeBackwardFirstTargetObjectEquiv C w X Y) (freeBackwardFirstTargetObjectEquiv_naturality C
        w X Y) Z ≅
        (Functor.const SimplexCategoryᵒᵖ).obj ((⟨Z⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨X⟩) :=
  DoubleSimplicial.diagonalFunctor.mapIso (freeBackwardFirstTargetLeftNerveDiagramIso C w X Y Z) ≪≫
    DoubleSimplicial.diagonalDiscreteIso _
def freeBackwardFirstLeftSpaceMap :=
  leftSpaceMap (freeFirstMarkedObjectEquiv C) (freeBackwardFirstTargetObjectEquiv C w X Y)
    (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y)
    (freeBackwardFirstTargetObjectEquiv_naturality C w X Y) (freeBackwardBackwardAugmentation C w X
      Y)
    (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y) Z

lemma freeBackwardFirstLeftSpaceIso_augmentation :
    (freeBackwardFirstLeftSpaceIso C w X Y Z).hom ≫ freeResolutionCanonicalMarkedHomAugmentation C
      Z X =
      freeBackwardFirstLeftSpaceMap C w X Y Z ≫ (freeBackwardFirstTargetLeftSpaceIso C w X Y Z).hom
        := by
  ext n σ
  apply WideSubcategory.hom_ext
  change (eqToHom _ ≫ (markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map
      (eqToHom _ ≫ (σ.obj 0).as ≫ eqToHom _) ≫ eqToHom _).hom =
    ((eqToHom (congrArg op
        (freeBackwardFirstMarkedObjectEquiv_augmentation C w X Y n Z))).unop ≫
      ((markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map (σ.obj 0).as ≫
        eqToHom _)).hom
  rw [eqToHom_unop]
  generalize (σ.obj 0).as = f
  change (freeFirstMarkedObjectEquiv C n Z ⟶ freeFirstMarkedObjectEquiv C n X) at f
  simp only [Functor.map_comp, WideSubcategory.comp_def, marked_eqToHom_hom,
    Category.assoc, eqToHom_map, eqToHom_trans_assoc, eqToHom_trans]
  change eqToHom (freeResolutionObject_augmentation C n Z).symm ≫
      ((freeResolutionAugmentationNatTrans C).app n).functor.map f.hom ≫
        eqToHom (freeResolutionObject_augmentation C n X) =
    (eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory C.weakEquivalences))
        (freeResolutionObject_augmentation C n Z)).symm ≫
      (markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map f ≫
        eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory C.weakEquivalences))
          (freeResolutionObject_augmentation C n X))).hom
  simp only [WideSubcategory.comp_def, marked_eqToHom_hom (C := C)]
  rfl

lemma freeBackwardFirstLeftSpaceMap_weak :
    IsWeakHomotopyEquivalence (freeBackwardFirstLeftSpaceMap C w X Y Z) := by
  have h := (isPrecompositionEquivalence_of_iso
    (freeBackwardFirstLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.comp
      (freeResolutionCanonicalMarkedHomAugmentation_weak C Z X)
  rw [freeBackwardFirstLeftSpaceIso_augmentation] at h
  exact (isPrecompositionEquivalence_of_iso
    (freeBackwardFirstTargetLeftSpaceIso C w X Y Z)).isWeakHomotopyEquivalence.cancel_right h
end SerrePositivity.EInfinity.Hammock.FirstColumn
