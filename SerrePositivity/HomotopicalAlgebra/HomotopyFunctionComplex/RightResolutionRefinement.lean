module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RightResolutionMapping
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # A natural weak span from existing presentations to target resolution mapping spaces

The index records actual weak target comparisons. Every original presentation
occurs in it, by model lifting. It is not a strict section over the base category.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.ModelReplacement

namespace SerrePositivity.HomotopyFunctionComplex.RightResolutionRefinement
variable (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev targetZero := DualResolutionTargets.framedPresentation C (op (SimplexCategory.mk 0))
abbrev TargetComma := Comma (targetZero C) (𝟭 (FibrantReplacementObject C))

def weakTargets : ObjectProperty (TargetComma C) := fun r => weakEquivalences C r.hom.base
abbrev TargetIndex := (weakTargets C).FullSubcategory

abbrev resolvedTarget : TargetIndex C ⥤ DualResolutionTargets.FramedIndex C :=
  (weakTargets C).ι ⋙ Comma.fst _ _
abbrev originalTarget : TargetIndex C ⥤ FibrantReplacementObject C :=
  (weakTargets C).ι ⋙ Comma.snd _ _

abbrev targetComparison : resolvedTarget C ⋙ targetZero C ⟶ originalTarget C :=
  Functor.whiskerLeft (weakTargets C).ι (Comma.natTrans _ _)

abbrev Index := (FramedResolution C)ᵒᵖ × TargetIndex C
abbrev original : Index C ⥤ ReplacementMapping.Index C :=
  (𝟭 (FramedResolution C)ᵒᵖ).prod (originalTarget C)
abbrev resolved : Index C ⥤ RightResolutionMapping.Index C :=
  (𝟭 (FramedResolution C)ᵒᵖ).prod (resolvedTarget C)

def ofTarget (Y : FibrantReplacementObject C) : TargetIndex C :=
  ⟨{ left := DualResolutionTargets.ofObject C Y.base
     right := Y
     hom := FibrantReplacementObject.liftBase (𝟙 Y.base) },
    (weakEquivalences C).id_mem Y.base⟩

abbrev ofOriginal (X : ReplacementMapping.Index C) : Index C := (X.1, ofTarget C X.2)

@[simp] lemma ofOriginal_original (X : ReplacementMapping.Index C) :
    (original C).obj (ofOriginal C X) = X := rfl

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev middle : Index C ⥤ SSet.{v} := resolved C ⋙ RightResolutionMapping.zero hcof hfib

/-- The actual comparison to the original mapping diagram, natural on all refinement maps. -/
def left : middle C hcof hfib ⟶ original C ⋙ ReplacementMapping.uncurried hcof hfib :=
  Functor.whiskerRight (NatTrans.prod (𝟙 _) (targetComparison C))
    (ReplacementMapping.uncurried hcof hfib)

/-- The diagonal comparison is natural over the same refinement index. -/
abbrev right : middle C hcof hfib ⟶ resolved C ⋙ RightResolutionMapping.functor hcof hfib :=
  Functor.whiskerLeft (resolved C) (RightResolutionMapping.comparison hcof hfib)

lemma left_weakEquivalence (X : Index C) :
    weakEquivalences SSet.{v} ((left C hcof hfib).app X) :=
  ReplacementMapping.uncurried_weakEquivalence hcof hfib _
    ((weakEquivalences C).id_mem _) X.2.property

lemma right_weakEquivalence (X : Index C) :
    weakEquivalences SSet.{v} ((right C hcof hfib).app X) :=
  RightResolutionMapping.comparison_weakEquivalence hcof hfib ((resolved C).obj X)

abbrev kanRight : middle C hcof hfib ⟶
    resolved C ⋙ RightResolutionMapping.kanFunctor hcof hfib :=
  Functor.whiskerLeft (resolved C) (RightResolutionMapping.kanComparison hcof hfib)

lemma kanRight_weakEquivalence (X : Index C) :
    weakEquivalences SSet.{v} ((kanRight C hcof hfib).app X) :=
  RightResolutionMapping.kanComparison_weakEquivalence hcof hfib ((resolved C).obj X)

end SerrePositivity.HomotopyFunctionComplex.RightResolutionRefinement
