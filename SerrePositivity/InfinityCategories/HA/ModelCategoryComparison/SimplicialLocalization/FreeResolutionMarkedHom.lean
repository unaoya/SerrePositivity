module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeResolutionHomRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# 元の指定射からなる自由解消 Hom

概要：自由解消の指定射の Hom と元の指定射への augmentation を構成する。
方針：元の指定射の述語を全単体作用素で保つ部分単体集合として扱う。
規約：指定射は元の相対圏の同じ射の類であり、飽和性を要求しない。
使われ方：DK ホモトピー補題2.4の指定射の Hom の入力。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.Opposite
open scoped _root_.Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionMarkedHomSubcomplex : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHom C X Y).Subcomplex where
  obj n := {f | ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences f}
  map θ f hf := by
    change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj _).weakEquivalences
      (eqToHom _ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ).functor.map f ≫ eqToHom _)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ).map f hf)

abbrev freeResolutionMarkedHom : SSet.{u} := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedHomSubcomplex C X Y).toSSet

def freeResolutionMarkedHomAugmentation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedHom C X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj {f : X ⟶ Y // C.weakEquivalences f} where
  app n := ↾fun f => ⟨(_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHomAugmentation C X Y).app n f.val, by
    change C.weakEquivalences (eqToHom _ ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).functor.map f.val ≫ eqToHom _)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2
      (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionAugmentationNatTrans C).app n).map f.val f.property)⟩
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionGeneratorHomAugmentation C X Y).naturality θ) f.val

def freeResolutionMarkedHomSection (f : {f : X ⟶ Y // C.weakEquivalences f}) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedHom C X Y) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomSection C f.val, ⟨trivial, f.property⟩⟩

def freeResolutionMarkedHomExtra (n : ℕ) (f : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedHom C X Y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionMarkedHom C X Y) _⦋n + 1⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.generatorHomExtra C n f.val, ⟨trivial, f.property⟩⟩

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
