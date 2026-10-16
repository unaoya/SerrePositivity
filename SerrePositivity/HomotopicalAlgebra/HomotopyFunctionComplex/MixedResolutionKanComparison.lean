module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BalancedResolutionComparison

/-! # Connecting the actual mixed action output to both existing Kan diagrams

All three comparisons have the same raw double Hom as their source.
The new output remains small in the original Hom universe.
-/

@[expose] public section
universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedResolutionKanComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C
local instance : ModelCategory (SimplexCategory ⥤ Cᵒᵖ) := Reedy.simplexModelCategory Cᵒᵖ

lemma action_ofLift {X X' : ResolutionObject C} (k : X ⟶ X')
    {Y Y' : ResolutionObject Cᵒᵖ} (l : Y ⟶ Y') {T : SSet.{v}}
    (d : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (e : T ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (t : T ⟶ MixedResolutionLiftAction.input X' Y') :
    MixedResolutionLiftAction.action X X' k.base Y Y' l.base
        (d ≫ ResolutionLiftSpace.ofLift k) (e ≫ ResolutionLiftSpace.ofLift l) t =
      t ≫ MixedDiagonalHom.map k.diagram l.diagram ≫
        MixedDiagonalHom.map (MixedResolutionComparison.augmentation X)
          (MixedResolutionComparison.augmentation Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (MixedResolutionLiftAction.family X X' k.base
      (d ≫ ResolutionLiftSpace.ofLift k)).app n x ≫ t.app n x ≫
        ((MixedResolutionLiftAction.family Y Y' l.base
          (e ≫ ResolutionLiftSpace.ofLift l)).app n x).unop = _
  rw [MixedResolutionLiftAction.family_point, MixedResolutionLiftAction.family_point]
  change (_ ≫ _) ≫ t.app n x ≫ (_ ≫ _).unop =
    _ ≫ (k.diagram.app n.unop ≫ t.app n x ≫ (l.diagram.app n.unop).unop) ≫ _
  dsimp [CosimplicialMapFamily.ofMap, MixedResolutionComparison.augmentation]
  simp only [Category.assoc]

abbrev raw : BiresolutionRawMapping.functor (C := C) ⟶ MixedResolutionComparison.output :=
  MixedBiresolutionComparison.rawIso.hom ≫ MixedResolutionComparison.comparison

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma raw_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((raw (C := C)).app X) :=
  (weakEquivalences SSet.{v}).comp_mem _ _ ((weakEquivalences SSet.{v}).of_isIso _)
    (MixedResolutionComparison.comparison_weakEquivalence hcof hfib X)

abbrev functor : RightResolutionMapping.Index C ⥤ SSet.{v} :=
  MixedResolutionComparison.output ⋙ KanReplacement.functor hcof hfib

def comparison : BalancedResolutionComparison.middle (C := C) hcof hfib ⟶
    functor hcof hfib :=
  Functor.whiskerRight raw (KanReplacement.functor hcof hfib)

lemma comparison_weakEquivalence (X : RightResolutionMapping.Index C) :
    weakEquivalences SSet.{v} ((comparison hcof hfib).app X) :=
  KanReplacement.map_weakEquivalence hcof hfib _ (raw_weakEquivalence hcof hfib X)

lemma middle_map_weakEquivalence {X Y : RightResolutionMapping.Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((RightResolutionMapping.projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((BalancedResolutionComparison.middle hcof hfib).map f) := by
  have h := (weakEquivalences SSet.{v}).comp_mem _ _
    (BalancedResolutionComparison.left_weakEquivalence hcof hfib X)
    (RightResolutionMapping.kanFunctor_map_weakEquivalence hcof hfib f hs ht)
  rw [← (BalancedResolutionComparison.left hcof hfib).naturality f] at h
  exact (weakEquivalences SSet.{v}).of_postcomp _ _
    (BalancedResolutionComparison.left_weakEquivalence hcof hfib Y) h

lemma map_weakEquivalence {X Y : RightResolutionMapping.Index C} (f : X ⟶ Y)
    (hs : weakEquivalences C f.1.unop.map.base)
    (ht : weakEquivalences C ((RightResolutionMapping.projection (C := C)).map f).2) :
    weakEquivalences SSet.{v} ((functor hcof hfib).map f) := by
  have h := (weakEquivalences SSet.{v}).comp_mem _ _
    (middle_map_weakEquivalence hcof hfib f hs ht) (comparison_weakEquivalence hcof hfib Y)
  rw [(comparison hcof hfib).naturality f] at h
  exact (weakEquivalences SSet.{v}).of_precomp _ _
    (comparison_weakEquivalence hcof hfib X) h

lemma kanComplex (X : RightResolutionMapping.Index C) :
    SSet.KanComplex ((functor hcof hfib).obj X) := KanReplacement.kanComplex hcof hfib _

lemma comparison_piZero_bijective (X : RightResolutionMapping.Index C) :
    Function.Bijective (SSet.mapπ₀ ((comparison hcof hfib).app X)) := by
  have : IsFibrant ((BalancedResolutionComparison.middle hcof hfib).obj X) :=
    KanReplacement.isFibrant hcof hfib _
  have : IsFibrant ((functor hcof hfib).obj X) := KanReplacement.isFibrant hcof hfib _
  have : WeakEquivalence ((comparison hcof hfib).app X) :=
    ⟨comparison_weakEquivalence hcof hfib X⟩
  exact piZero_bijective_of_weakEquivalence_of_fibrant hcof _

def piZeroEquiv {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] (X : RightResolutionMapping.Index C) :
    SSet.π₀ ((functor hcof hfib).obj X) ≃
      (Q.obj ((RightResolutionMapping.projection (C := C)).obj X).1.unop ⟶
        Q.obj ((RightResolutionMapping.projection (C := C)).obj X).2) :=
  (Equiv.ofBijective _ (comparison_piZero_bijective hcof hfib X)).symm.trans
    ((Equiv.ofBijective _
      (BalancedResolutionComparison.left_piZero_bijective hcof hfib X)).trans
        (RightResolutionMapping.piZeroEquiv hcof hfib Q X))

def localizedIso {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{v})] :
    functor (C := C) hcof hfib ⋙ L ≅ RightResolutionMapping.kanFunctor hcof hfib ⋙ L := by
  have : IsIso (Functor.whiskerRight (comparison (C := C) hcof hfib) L) := by
    have (X : RightResolutionMapping.Index C) :
        IsIso ((Functor.whiskerRight (comparison hcof hfib) L).app X) :=
      Localization.inverts L _ _ (comparison_weakEquivalence hcof hfib X)
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (BalancedResolutionComparison.left
      (C := C) hcof hfib) L) := by
    have (X : RightResolutionMapping.Index C) :
        IsIso ((Functor.whiskerRight (BalancedResolutionComparison.left hcof hfib) L).app X) :=
      Localization.inverts L _ _
        (BalancedResolutionComparison.left_weakEquivalence hcof hfib X)
    exact NatIso.isIso_of_isIso_app _
  exact (asIso (Functor.whiskerRight (comparison hcof hfib) L)).symm ≪≫
    asIso (Functor.whiskerRight (BalancedResolutionComparison.left hcof hfib) L)

end SerrePositivity.HomotopyFunctionComplex.MixedResolutionKanComparison
