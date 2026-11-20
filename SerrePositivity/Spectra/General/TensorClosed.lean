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

lemma tensor_eq (E F : GeneralSymmetricSpectrum C K) : tensor E F = E ⊗ F := rfl

lemma internalHom_eq (E F : GeneralSymmetricSpectrum C K) :
    internalHom E F = (ihom E).obj F := rfl

abbrev curry {E X F : GeneralSymmetricSpectrum C K} (f : tensor E X ⟶ F) :
    X ⟶ internalHom E F :=
  MonoidalModuleInternalHom.curryModule (SymmetricSequence.tensorPowerSequence K) E f

abbrev uncurry {E X F : GeneralSymmetricSpectrum C K} (f : X ⟶ internalHom E F) :
    tensor E X ⟶ F :=
  MonoidalModuleInternalHom.uncurryModule (SymmetricSequence.tensorPowerSequence K) E f

lemma uncurry_curry {E X F : GeneralSymmetricSpectrum C K} (f : tensor E X ⟶ F) :
    uncurry (curry f) = f := (tensorHomEquiv E X F).symm_apply_apply f

lemma curry_uncurry {E X F : GeneralSymmetricSpectrum C K} (f : X ⟶ internalHom E F) :
    curry (uncurry f) = f := (tensorHomEquiv E X F).apply_symm_apply f
/-- Maps out of the balanced tensor are determined on the quotient projection. -/
lemma tensor_hom_ext {E F H : GeneralSymmetricSpectrum C K} (f g : tensor E F ⟶ H)
    (h : MonoidalBalancedTensor.projection (SymmetricSequence.tensorPowerSequence K) E F ≫ f.hom =
      MonoidalBalancedTensor.projection (SymmetricSequence.tensorPowerSequence K) E F ≫ g.hom) :
    f = g :=
  Mod.hom_ext _ _ (MonoidalBalancedTensor.hom_ext _ f.hom g.hom h)

/-- The module map descending a balanced map is unique. -/
lemma tensorDesc_unique {E F H : GeneralSymmetricSpectrum C K}
    (f : MonoidalBalancedTensor.BalancedMap (SymmetricSequence.tensorPowerSequence K) E F H.X)
    (hf : (α_ (SymmetricSequence.tensorPowerSequence K) E.X F.X).inv ≫
        action E ▷ F.X ≫ f.val =
      SymmetricSequence.tensorPowerSequence K ◁ f.val ≫ action H)
    (g : tensor E F ⟶ H)
    (h : MonoidalBalancedTensor.projection (SymmetricSequence.tensorPowerSequence K) E F ≫
      g.hom = f.val) :
    g = MonoidalBalancedTensor.moduleDesc (SymmetricSequence.tensorPowerSequence K) f hf :=
  Mod.hom_ext _ _ (MonoidalBalancedTensor.desc_unique _ f g.hom h)

end SerrePositivity.GeneralSymmetricSpectrum
