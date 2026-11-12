module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionNativeMarkedHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
# 元の指定部分圏の Hom augmentation 自身の弱同値性

概要：wide 部分圏の Hom と指定射の部分単体集合を同型で照合し、同じ射の弱比較を得る。
方針：元の射と指定性を保つ往復と、augmentation の可換式を証明する。
規約：元の部分圏の Hom 構造体・全作用素・augmentation を保持する。
使われ方：DK2.4の元の指定部分圏の入力。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite SerrePositivity.InfinityCategories

lemma marked_eqToHom_hom {C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
    {X Y : WideSubcategory C.weakEquivalences} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg WideSubcategory.obj h) := by
  cases h
  rfl

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionNativeMarkedHomIso :
    freeResolutionNativeMarkedHom C X Y ≅ freeResolutionMarkedHom C X Y where
  hom :=
    { app n := ↾fun f => ⟨f.hom, f.property⟩
      naturality n m θ := by
        apply ConcreteCategory.hom_ext
        intro f
        apply Subtype.ext
        change (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((freeResolution C).map θ)).map f ≫
          eqToHom _).hom = eqToHom _ ≫ ((freeResolution C).map θ).functor.map f.hom ≫ eqToHom _
        simp only [WideSubcategory.comp_def, marked_eqToHom_hom]
        rfl }
  inv :=
    { app n := ↾fun f => ⟨f.val, f.property⟩
      naturality n m θ := by
        apply ConcreteCategory.hom_ext
        intro f
        apply WideSubcategory.hom_ext
        change (eqToHom _ ≫ ((freeResolution C).map θ).functor.map f.val ≫ eqToHom _) =
          (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((freeResolution C).map θ)).map
            ⟨f.val, f.property⟩ ≫ eqToHom _).hom
        simp only [WideSubcategory.comp_def, marked_eqToHom_hom]
        rfl }
  hom_inv_id := by ext n f; rfl
  inv_hom_id := by ext n f; rfl

def markedHomSubtypeEquiv :
    ((⟨X⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨Y⟩) ≃
      {f : X ⟶ Y // C.weakEquivalences f} where
  toFun f := ⟨f.hom, f.property⟩
  invFun f := ⟨f.val, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedHomSubtypeIso :
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((⟨X⟩ : WideSubcategory C.weakEquivalences) ⟶ ⟨Y⟩) ≅
    (Functor.const SimplexCategoryᵒᵖ).obj {f : X ⟶ Y // C.weakEquivalences f} :=
  (Functor.const SimplexCategoryᵒᵖ).mapIso (Equiv.toIso (markedHomSubtypeEquiv C X Y))

lemma freeResolutionNativeMarkedHomIso_augmentation :
    (freeResolutionNativeMarkedHomIso C X Y).hom ≫ freeResolutionMarkedHomAugmentation C X Y =
      freeResolutionNativeMarkedHomAugmentation C X Y ≫ (markedHomSubtypeIso C X Y).hom := by
  ext n f
  apply Subtype.ext
  change (eqToHom _ ≫ ((freeResolutionAugmentationNatTrans C).app n).functor.map f.hom ≫
    eqToHom _) =
      (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap ((freeResolutionAugmentationNatTrans C).app n)).map f ≫
        eqToHom _).hom
  simp only [WideSubcategory.comp_def, marked_eqToHom_hom]
  rfl

lemma freeResolutionNativeMarkedHomAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeResolutionNativeMarkedHomAugmentation C X Y) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeResolutionNativeMarkedHomIso C X Y)).isWeakHomotopyEquivalence.comp
      (freeResolutionMarkedHomAugmentation_isWeakHomotopyEquivalence C X Y)
  rw [freeResolutionNativeMarkedHomIso_augmentation] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (markedHomSubtypeIso C X Y)).isWeakHomotopyEquivalence.cancel_right h

end SerrePositivity.EInfinity.SimplicialLocalization
