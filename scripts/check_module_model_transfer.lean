import SerrePositivity.HomotopicalAlgebra.Foundations

universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
open SerrePositivity.MonoidalModelTransfer

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  [HasMonoidAxiom.{w} C] (M : C) [MonObj M]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  [(I.strictMap (SerrePositivity.MonoidalFreeModule.freeFunctor M)).HasSmallObjectArgument.{w}]
  [(J.strictMap (SerrePositivity.MonoidalFreeModule.freeFunctor M)).HasSmallObjectArgument.{w}]

-- No pre-existing model structure on Mod C M and no cofibrancy of M are assumed.
example : ModelCategory (Mod C M) := moduleModelCategory M I J

example : relativeCells.{w} (J.strictMap (SerrePositivity.MonoidalFreeModule.freeFunctor M)) ≤
    (weakEquivalences C).inverseImage (Mod.forget M) := freeModule_cells_acyclic M I J

example : let := moduleModelCategory M I J
    weakEquivalences (Mod C M) = (weakEquivalences C).inverseImage (Mod.forget M) :=
  moduleModelCategory_weakEquivalences M I J

example : let := moduleModelCategory M I J
    fibrations (Mod C M) = (fibrations C).inverseImage (Mod.forget M) :=
  moduleModelCategory_fibrations M I J

example : let := moduleModelCategory M I J
    IsLeftQuillen (SerrePositivity.MonoidalFreeModule.freeFunctor M) :=
  moduleModelCategory_isLeftQuillen M I J

example : let := moduleModelCategory M I J
    IsRightQuillen (Mod.forget (D := C) M) := moduleModelCategory_isRightQuillen M I J

example : let := moduleModelCategory M I J
    (cofibrations (Mod C M)).HasFactorization (trivialFibrations (Mod C M)) := by
  let := moduleModelCategory M I J
  infer_instance

example : let := moduleModelCategory M I J
    (trivialCofibrations (Mod C M)).HasFactorization (fibrations (Mod C M)) := by
  let := moduleModelCategory M I J
  infer_instance
