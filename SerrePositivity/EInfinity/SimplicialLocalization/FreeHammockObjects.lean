module

public import SerrePositivity.EInfinity.SimplicialLocalization.ResolutionObjects
public import SerrePositivity.EInfinity.SimplicialLocalization.ResolutionRepresentatives

/-!
# 自由相対解像の固定対象の表示

概要：局所化する前の元の自由相対解像で、固定対象と全作用素の対象上の等式を得る。
方針：元の augmentation の対象上の全単射性を使い、標準生成対象とも照合する。
規約：元の全単体作用素の保存を証明し、対象の同一性を仮定しない。
使われ方：自由相対解像の固定した両対象の hammock の二重単体的図式。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite
open scoped Simplicial

def freeResolutionObjectEquiv (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    ((freeResolution C).obj n).category ≃ C.category :=
  Equiv.ofBijective ((freeResolutionAugmentationNatTrans C).app n).functor.obj
    (freeResolutionAugmentation_obj_bijective C n)

def freeResolutionObject (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : C.category) : ((freeResolution C).obj n).category :=
  (freeResolutionObjectEquiv C n).symm X

lemma freeResolutionObject_augmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : C.category) :
    ((freeResolutionAugmentationNatTrans C).app n).functor.obj (freeResolutionObject C n X) = X :=
  (freeResolutionObjectEquiv C n).apply_symm_apply X

lemma freeResolutionObject_naturality (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : C.category) :
    ((freeResolution C).map θ).functor.obj (freeResolutionObject C n X) =
      freeResolutionObject C m X := by
  apply (freeResolutionObjectEquiv C m).injective
  have h := congrArg (fun F : (freeResolution C).obj n ⟶ C => F.functor)
    ((freeResolutionAugmentationNatTrans C).naturality θ)
  change ((freeResolution C).map θ).functor ⋙
      ((freeResolutionAugmentationNatTrans C).app m).functor =
    ((freeResolutionAugmentationNatTrans C).app n).functor ⋙ 𝟭 _ at h
  have h' : ((freeResolution C).map θ).functor ⋙
      ((freeResolutionAugmentationNatTrans C).app m).functor =
        ((freeResolutionAugmentationNatTrans C).app n).functor := by
    simpa only [CategoryTheory.Functor.comp_id] using h
  change ((freeResolutionAugmentationNatTrans C).app m).functor.obj
    (((freeResolution C).map θ).functor.obj (freeResolutionObject C n X)) =
      ((freeResolutionAugmentationNatTrans C).app m).functor.obj (freeResolutionObject C m X)
  rw [← CategoryTheory.Functor.comp_obj, h']
  exact (freeResolutionObject_augmentation C n X).trans
    (freeResolutionObject_augmentation C m X).symm

lemma freeResolutionObject_generator (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : ℕ) (X : C.category) :
    freeResolutionObject C (op ⦋n⦌) X = freeResolutionGeneratorObject C (n + 1) X := by
  apply (freeResolutionObjectEquiv C (op ⦋n⦌)).injective
  exact (freeResolutionObject_augmentation C _ X).trans
    (freeResolutionGeneratorObject_augmentation C (n + 1) X).symm

end SerrePositivity.EInfinity.SimplicialLocalization
