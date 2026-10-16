module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionKanComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters

/-! # The comparison targets the same whole-center action output

The source projection keeps both actual framed resolutions and all their
maps. The Kan output is literally the existing action's value diagram.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison
variable (C : Type u) [Category.{v} C] [ModelCategory C]

def sources : MixedResolutionCenters.Index C ⥤ RightResolutionMapping.Index C where
  obj q := (op (ResolutionArrowDiagram.source C q.1),
    op (ResolutionArrowDiagram.source Cᵒᵖ q.2))
  map f := (f.1.hom.1, f.2.hom.1)

def outputIso : sources C ⋙ MixedResolutionComparison.output ≅
    MixedResolutionCenters.output C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro q p f
    ext n h
    rfl)

def comparison : sources C ⋙ MixedBiresolutionComparison.functor ⟶
    MixedResolutionCenters.output C :=
  Functor.whiskerLeft (sources C) MixedResolutionComparison.comparison ≫ (outputIso C).hom

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma comparison_weakEquivalence (q : MixedResolutionCenters.Index C) :
    weakEquivalences SSet.{v} ((comparison C).app q) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (MixedResolutionComparison.comparison_weakEquivalence hcof hfib ((sources C).obj q))
    ((weakEquivalences SSet.{v}).of_isIso _)

def kanComparison : sources C ⋙ BalancedResolutionComparison.middle hcof hfib ⟶
    MixedResolutionCenters.kanOutput C hcof hfib :=
  Functor.whiskerLeft (sources C) (MixedResolutionKanComparison.comparison hcof hfib) ≫
    Functor.whiskerRight (outputIso C).hom (KanReplacement.functor hcof hfib)

lemma kanComparison_weakEquivalence (q : MixedResolutionCenters.Index C) :
    weakEquivalences SSet.{v} ((kanComparison C hcof hfib).app q) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (MixedResolutionKanComparison.comparison_weakEquivalence hcof hfib ((sources C).obj q))
    ((weakEquivalences SSet.{v}).of_isIso _)

end SerrePositivity.HomotopyFunctionComplex.MixedCenterComparison
