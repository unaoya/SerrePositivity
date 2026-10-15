module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.FunctorialResolution
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexModelCategory

/-! # Cosimplicial and simplicial resolutions over a general model source -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev cosimplicialResolution (X : C) : CofibrantResolution simplex X :=
  cofibrantResolution simplex (fun _ _ h ↦ SimplexCategory.ext h)
    (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩) X

abbrev simplicialResolution (X : C) : FibrantResolution simplexOp X :=
  fibrantResolution simplexOp (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩) X

abbrev cosimplicialResolutionFamily
    (source : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    CofibrantResolutionFamily (C := C) simplex :=
  cofibrantResolutionFamily simplex (fun _ _ h ↦ SimplexCategory.ext h)
    (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩) source

abbrev simplicialResolutionFamily
    (source : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    FibrantResolutionFamily (C := C) simplexOp :=
  fibrantResolutionFamily simplexOp
    (fun _ _ h ↦ Opposite.unop_injective (SimplexCategory.ext h))
    (fun n ↦ ⟨Opposite.op (SimplexCategory.mk n), rfl⟩) source

end SerrePositivity.Reedy
