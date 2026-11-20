module

public import SerrePositivity.Spectra.General.Basic
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Free

/-! # Free Sym(K) modules and their universal property -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] (K : C)

abbrev freeObj (F : SymmetricSequence C) : GeneralSymmetricSpectrum C K :=
  MonoidalFreeModule.freeObj (SymmetricSequence.tensorPowerSequence K) F

abbrev freeFunctor : SymmetricSequence C ⥤ GeneralSymmetricSpectrum C K :=
  MonoidalFreeModule.freeFunctor (SymmetricSequence.tensorPowerSequence K)

abbrev generator (F : SymmetricSequence C) : F ⟶ (freeObj K F).X :=
  MonoidalFreeModule.generator (SymmetricSequence.tensorPowerSequence K) F

abbrev lift {F : SymmetricSequence C} (E : GeneralSymmetricSpectrum C K) (f : F ⟶ E.X) :
    freeObj K F ⟶ E :=
  MonoidalFreeModule.lift (SymmetricSequence.tensorPowerSequence K) F E f

abbrev freeHomEquiv (F : SymmetricSequence C) (E : GeneralSymmetricSpectrum C K) :
    (freeObj K F ⟶ E) ≃ (F ⟶ E.X) :=
  MonoidalFreeModule.freeHomEquiv (SymmetricSequence.tensorPowerSequence K) F E

abbrev freeForgetAdjunction : freeFunctor K ⊣ forget K :=
  MonoidalFreeModule.freeForgetAdjunction (SymmetricSequence.tensorPowerSequence K)

lemma generator_lift {F : SymmetricSequence C} (E : GeneralSymmetricSpectrum C K)
    (f : F ⟶ E.X) : generator K F ≫ (lift K E f).hom = f :=
  MonoidalFreeModule.generator_lift _ F E f

/-- The value on the generators determines a map from a free spectrum. -/
lemma lift_unique {F : SymmetricSequence C} (E : GeneralSymmetricSpectrum C K)
    (f : freeObj K F ⟶ E) (g : F ⟶ E.X) (h : generator K F ≫ f.hom = g) :
    f = lift K E g := by
  apply (freeHomEquiv K F E).injective
  exact h.trans (generator_lift K E g).symm

/-- Forgetting the action on a free spectrum gives left convolution. -/
lemma free_forget_eq_tensorLeft :
    freeFunctor K ⋙ forget K = tensorLeft (SymmetricSequence.tensorPowerSequence K) := rfl

end SerrePositivity.GeneralSymmetricSpectrum
