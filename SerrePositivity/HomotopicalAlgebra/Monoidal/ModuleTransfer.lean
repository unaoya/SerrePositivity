module

public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap
public import SerrePositivity.HomotopicalAlgebra.Transfer.Right
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Free
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Limits
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Model structures on modules from the monoid axiom

Free-module cell acyclicity is proved from the monoid axiom and preservation
by forgetting modules. Smallness of the image generators remains an explicit
input to the small-object argument. The monoid need not be cofibrant.
-/

@[expose] public section
universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration

namespace SerrePositivity.MonoidalModelTransfer
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{w, w} C] [ModelCategory C] [HasMonoidAxiom.{w} C]
  (M : C) [MonObj M] (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

include I in
/-- Free-module relative J-cells are weak equivalences after forgetting.
This proof accounts for coproducts, pushouts and limit ordinal stages. -/
lemma freeModule_cells_acyclic :
    relativeCells.{w} (J.strictMap (MonoidalFreeModule.freeFunctor M)) ≤
      (weakEquivalences C).inverseImage (Mod.forget M) := by
  let : PreservesColimitsOfSize.{w, w} (Mod.forget (D := C) M) := {}
  have hgen : J ≤ trivialCofibrations C :=
    J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le
  have hmap : J.strictMap (MonoidalFreeModule.freeFunctor M) ≤
      (tensorRightImages J).inverseImage (Mod.forget M) := by
    intro A B f hf
    cases hf with
    | map hf => exact tensorLeft_mem _ hf M
  exact (relativeCells_map_le (Mod.forget M) _ _ hmap).trans
    (MorphismProperty.monotone_inverseImage _ (tensorCells_le_weakEquivalences J hgen))

variable [(I.strictMap (MonoidalFreeModule.freeFunctor M)).HasSmallObjectArgument.{w}]
  [(J.strictMap (MonoidalFreeModule.freeFunctor M)).HasSmallObjectArgument.{w}]

/-- Right-induced Mathlib model structure on modules over any monoid M.
The weak equivalences and fibrations are detected in the underlying category. -/
@[instance_reducible]
def moduleModelCategory : ModelCategory (Mod C M) := by
  let : HasFiniteLimits (Mod C M) := { out := fun J _ _ ↦ inferInstance }
  let : HasFiniteColimits (Mod C M) := { out := fun J _ _ ↦ inferInstance }
  exact rightTransfer I J (MonoidalFreeModule.freeForgetAdjunction M)
    (freeModule_cells_acyclic M I J)

lemma moduleModelCategory_weakEquivalences :
    @weakEquivalences (Mod C M) _ (moduleModelCategory M I J).categoryWithWeakEquivalences =
      (weakEquivalences C).inverseImage (Mod.forget M) := rfl

lemma moduleModelCategory_fibrations :
    @fibrations (Mod C M) _ (moduleModelCategory M I J).categoryWithFibrations =
      (fibrations C).inverseImage (Mod.forget M) := rfl

lemma moduleModelCategory_isLeftQuillen :
    let := moduleModelCategory M I J
    IsLeftQuillen (MonoidalFreeModule.freeFunctor M) := by
  let : HasFiniteLimits (Mod C M) := { out := fun J _ _ ↦ inferInstance }
  let : HasFiniteColimits (Mod C M) := { out := fun J _ _ ↦ inferInstance }
  exact rightTransfer_isLeftQuillen I J (MonoidalFreeModule.freeForgetAdjunction M)
    (freeModule_cells_acyclic M I J)

lemma moduleModelCategory_isRightQuillen :
    let := moduleModelCategory M I J
    IsRightQuillen (Mod.forget (D := C) M) := by
  let : HasFiniteLimits (Mod C M) := { out := fun J _ _ ↦ inferInstance }
  let : HasFiniteColimits (Mod C M) := { out := fun J _ _ ↦ inferInstance }
  exact rightTransfer_isRightQuillen I J (MonoidalFreeModule.freeForgetAdjunction M)
    (freeModule_cells_acyclic M I J)
end SerrePositivity.MonoidalModelTransfer
