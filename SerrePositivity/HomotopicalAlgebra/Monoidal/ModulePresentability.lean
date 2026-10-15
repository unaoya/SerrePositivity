module

public import SerrePositivity.HomotopicalAlgebra.Smith.ConservativeAdjunction
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import SerrePositivity.CategoryTheory.Monoidal.FreeModule
public import SerrePositivity.CategoryTheory.Monoidal.ModuleColimits

/-! # Local presentability of actual internal modules

The forgetful functor creates colimits when left tensor preserves them.
Its free adjunction, faithfulness and conservativity then transfer a small
strong generator. No model structure, cofibrancy or monoid axiom is used.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.MonoidalModulePresentability
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [IsLocallyPresentable.{w} C]
  [∀ X : C, PreservesColimitsOfSize.{w, w} (tensorLeft X)]
  (M : C) [MonObj M]

lemma isLocallyPresentable : IsLocallyPresentable.{w} (Mod C M) := by
  have := Smith.locallyPresentable_hasColimits (C := C)
  let U := Mod.forget (D := C) M
  have : U.Faithful := ⟨fun h ↦ Mod.hom_ext _ _ h⟩
  have : LocallySmall.{w} (Mod C M) := locallySmall_of_faithful U
  have : HasColimitsOfSize.{w, w} (Mod C M) := { }
  have : Fact Cardinal.aleph0.{w}.IsRegular := Cardinal.fact_isRegular_aleph0
  have : U.IsCardinalAccessible Cardinal.aleph0.{w} := { }
  have : (Mod.forget (D := C) M).IsAccessible.{w} :=
    ⟨Cardinal.aleph0, inferInstance, inferInstance⟩
  exact Smith.ConservativeAdjunction.isLocallyPresentable
    (MonoidalFreeModule.freeForgetAdjunction M)

end SerrePositivity.MonoidalModulePresentability
