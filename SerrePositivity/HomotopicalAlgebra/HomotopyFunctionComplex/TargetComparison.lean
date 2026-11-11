module

public import SerrePositivity.HomotopicalAlgebra.Generated.CommonFibrantReplacement
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TargetInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHomNaturality

/-! # Natural comparison of actual fibrant target replacements -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.TargetComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (fib fib₁ fib₂ : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))

lemma comparison_trivialCofibration
    (d : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X : C) : trivialCofibrations C ((fibrantTargetComparison d).app X) := d.hi _

abbrev common : C ⥤ C := ModelReplacement.CommonFibrant.obj fib
  (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂)

abbrev left : fibrantTarget fib₁ ⟶ common fib fib₁ fib₂ :=
  ModelReplacement.CommonFibrant.left fib
    (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂)

abbrev right : fibrantTarget fib₂ ⟶ common fib fib₁ fib₂ :=
  ModelReplacement.CommonFibrant.right fib
    (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂)

lemma under : fibrantTargetComparison fib₁ ≫ left fib fib₁ fib₂ =
    fibrantTargetComparison fib₂ ≫ right fib fib₁ fib₂ :=
  ModelReplacement.CommonFibrant.under fib
    (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂)

lemma isFibrant_obj (X : C) : IsFibrant ((common fib fib₁ fib₂).obj X) :=
  ModelReplacement.CommonFibrant.isFibrant_obj fib
    (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂) X

lemma left_trivialCofibration (X : C) : trivialCofibrations C ((left fib fib₁ fib₂).app X) :=
  ModelReplacement.CommonFibrant.left_trivialCofibration fib
    (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂)
    (comparison_trivialCofibration fib₂) X

lemma right_trivialCofibration (X : C) : trivialCofibrations C ((right fib fib₁ fib₂).app X) :=
  ModelReplacement.CommonFibrant.right_trivialCofibration fib
    (fibrantTargetComparison fib₁) (fibrantTargetComparison fib₂)
    (comparison_trivialCofibration fib₁) X

abbrev homLeft (Q : C ⥤ (SimplexCategory ⥤ C)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q (fibrantTarget fib₁) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q (common fib fib₁ fib₂) :=
  resolutionHomMapTarget Q (left fib fib₁ fib₂)

abbrev homRight (Q : C ⥤ (SimplexCategory ⥤ C)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q (fibrantTarget fib₂) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q (common fib fib₁ fib₂) :=
  resolutionHomMapTarget Q (right fib fib₁ fib₂)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma homLeft_weakEquivalence (q : CofibrantResolutionFamily (C := C) simplex)
    (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((homLeft fib fib₁ fib₂ q.obj).app X).app Y) := by
  have := fibrantTarget_isFibrant fib₁ Y
  have := isFibrant_obj fib fib₁ fib₂ Y
  have : WeakEquivalence ((left fib fib₁ fib₂).app Y) :=
    ⟨(left_trivialCofibration fib fib₁ fib₂ Y).2⟩
  exact cosimplicialHom_weakEquivalence_of_fibrant hcof _ (q.cofibrant X.unop) _

include hcof in
lemma homRight_weakEquivalence (q : CofibrantResolutionFamily (C := C) simplex)
    (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((homRight fib fib₁ fib₂ q.obj).app X).app Y) := by
  have := fibrantTarget_isFibrant fib₂ Y
  have := isFibrant_obj fib fib₁ fib₂ Y
  have : WeakEquivalence ((right fib fib₁ fib₂).app Y) :=
    ⟨(right_trivialCofibration fib fib₁ fib₂ Y).2⟩
  exact cosimplicialHom_weakEquivalence_of_fibrant hcof _ (q.cofibrant X.unop) _

end SerrePositivity.HomotopyFunctionComplex.TargetComparison
