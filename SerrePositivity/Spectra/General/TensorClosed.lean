module

public import SerrePositivity.Spectra.General.Limits
public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHom
public import SerrePositivity.CategoryTheory.Monoidal.Mod.Symmetric

/-! # Tensor and internal Hom of general symmetric spectra

All operations use the already constructed closed symmetric monoidal category
of modules over a commutative monoid. No new tensor or category is introduced.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  {K : C}

abbrev tensor (E F : GeneralSymmetricSpectrum C K) : GeneralSymmetricSpectrum C K :=
  MonoidalBalancedTensor.moduleObj (SymmetricSequence.tensorPowerSequence K) E F

abbrev internalHom (E F : GeneralSymmetricSpectrum C K) : GeneralSymmetricSpectrum C K :=
  MonoidalModuleInternalHom.moduleObj (SymmetricSequence.tensorPowerSequence K) E F

abbrev internalHomFunctor (E : GeneralSymmetricSpectrum C K) :
    GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K :=
  MonoidalModuleInternalHom.internalHomFunctor (SymmetricSequence.tensorPowerSequence K) E

abbrev tensorHomEquiv (E X F : GeneralSymmetricSpectrum C K) :
    (tensor E X ⟶ F) ≃ (X ⟶ internalHom E F) :=
  MonoidalModuleInternalHom.tensorHomEquiv (SymmetricSequence.tensorPowerSequence K) E X F

abbrev tensorInternalHomAdjunction (E : GeneralSymmetricSpectrum C K) :
    tensorLeft E ⊣ internalHomFunctor E :=
  MonoidalModuleInternalHom.tensorInternalHomAdjunction (SymmetricSequence.tensorPowerSequence K) E

abbrev curry {E X F : GeneralSymmetricSpectrum C K} (f : tensor E X ⟶ F) :
    X ⟶ internalHom E F :=
  MonoidalModuleInternalHom.curryModule (SymmetricSequence.tensorPowerSequence K) E f

abbrev uncurry {E X F : GeneralSymmetricSpectrum C K} (f : X ⟶ internalHom E F) :
    tensor E X ⟶ F :=
  MonoidalModuleInternalHom.uncurryModule (SymmetricSequence.tensorPowerSequence K) E f

end SerrePositivity.GeneralSymmetricSpectrum
