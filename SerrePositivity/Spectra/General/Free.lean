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

lemma free_underlying (F : SymmetricSequence C) :
    (freeObj K F).X = SymmetricSequence.tensorPowerSequence K ⊗ F := rfl

lemma generator_lift {F : SymmetricSequence C} (E : GeneralSymmetricSpectrum C K)
    (f : F ⟶ E.X) : generator K F ≫ (lift K E f).hom = f :=
  MonoidalFreeModule.generator_lift _ F E f

lemma lift_generator {F : SymmetricSequence C} (E : GeneralSymmetricSpectrum C K)
    (f : freeObj K F ⟶ E) : lift K E (generator K F ≫ f.hom) = f :=
  MonoidalFreeModule.lift_generator _ F E f

lemma free_unit (F : SymmetricSequence C) :
    (freeForgetAdjunction K).unit.app F = generator K F :=
  MonoidalFreeModule.free_unit _ F

lemma free_counit (E : GeneralSymmetricSpectrum C K) :
    ((freeForgetAdjunction K).counit.app E).hom = action E :=
  MonoidalFreeModule.free_counit _ E
end SerrePositivity.GeneralSymmetricSpectrum
