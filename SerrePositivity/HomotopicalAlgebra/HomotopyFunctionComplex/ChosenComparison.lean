module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetComparison

/-! # Natural weak equivalence zigzags between actual chosen Hom bifunctors

The two ends may use different cofibrant resolutions and different fibrant
target replacements. Both map naturally to one actual Kan-valued bifunctor.
The auxiliary comparison factorizations are explicit and may be chosen
independently of either end.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.ChosenComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof cof₁ cof₂ : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))

abbrev sourceFamily := ResolutionComparison.common cof
  (cosimplicialResolutionFamily cof₁) (cosimplicialResolutionFamily cof₂)

abbrev middle : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (sourceFamily cof cof₁ cof₂).obj (TargetComparison.common fib fib₁ fib₂)

abbrev left : chosenResolutionHom cof₁ fib₁ ⟶ middle cof cof₁ cof₂ fib fib₁ fib₂ :=
  ResolutionComparison.homLeft cof (cosimplicialResolutionFamily cof₁)
    (cosimplicialResolutionFamily cof₂) (fibrantTarget fib₁) ≫
      TargetComparison.homLeft fib fib₁ fib₂ (sourceFamily cof cof₁ cof₂).obj

abbrev right : chosenResolutionHom cof₂ fib₂ ⟶ middle cof cof₁ cof₂ fib fib₁ fib₂ :=
  ResolutionComparison.homRight cof (cosimplicialResolutionFamily cof₁)
    (cosimplicialResolutionFamily cof₂) (fibrantTarget fib₂) ≫
      TargetComparison.homRight fib fib₁ fib₂ (sourceFamily cof cof₁ cof₂).obj

lemma middle_kanComplex (X : Cᵒᵖ) (Y : C) :
    SSet.KanComplex (((middle cof cof₁ cof₂ fib fib₁ fib₂).obj X).obj Y) := by
  have := TargetComparison.isFibrant_obj fib fib₁ fib₂ Y
  exact cosimplicialHom_kanComplex _ ((sourceFamily cof cof₁ cof₂).cofibrant X.unop)
    ((sourceFamily cof cof₁ cof₂).atObject X.unop).homotopicallyConstant _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma left_weakEquivalence (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((left cof cof₁ cof₂ fib fib₁ fib₂).app X).app Y) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (ResolutionComparison.homLeft_weakEquivalence cof (cosimplicialResolutionFamily cof₁)
      (cosimplicialResolutionFamily cof₂) hcof (fibrantTarget fib₁)
      (fibrantTarget_isFibrant fib₁) X Y)
    (TargetComparison.homLeft_weakEquivalence fib fib₁ fib₂ hcof
      (sourceFamily cof cof₁ cof₂) X Y)

include hcof in
lemma right_weakEquivalence (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((right cof cof₁ cof₂ fib fib₁ fib₂).app X).app Y) :=
  (weakEquivalences SSet.{v}).comp_mem _ _
    (ResolutionComparison.homRight_weakEquivalence cof (cosimplicialResolutionFamily cof₁)
      (cosimplicialResolutionFamily cof₂) hcof (fibrantTarget fib₂)
      (fibrantTarget_isFibrant fib₂) X Y)
    (TargetComparison.homRight_weakEquivalence fib fib₁ fib₂ hcof
      (sourceFamily cof cof₁ cof₂) X Y)

include hcof in
lemma geometricWeakEquivalences
    (hw : weakEquivalences SSet.{v} = SimplicialHomotopy.weakEquivalences)
    (X : Cᵒᵖ) (Y : C) :
    SimplicialHomotopy.weakEquivalences (((left cof cof₁ cof₂ fib fib₁ fib₂).app X).app Y) ∧
      SimplicialHomotopy.weakEquivalences (((right cof cof₁ cof₂ fib fib₁ fib₂).app X).app Y) :=
  ⟨hw ▸ left_weakEquivalence cof cof₁ cof₂ fib fib₁ fib₂ hcof X Y,
    hw ▸ right_weakEquivalence cof cof₁ cof₂ fib fib₁ fib₂ hcof X Y⟩

end SerrePositivity.HomotopyFunctionComplex.ChosenComparison
