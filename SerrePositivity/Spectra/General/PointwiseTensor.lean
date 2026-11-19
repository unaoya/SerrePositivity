module

public import SerrePositivity.Spectra.General.TensorClosed
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModuleUnit
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModuleAssociator
public import SerrePositivity.CategoryTheory.FunctorTransport

/-! # The action of C on general symmetric spectra

The pointwise tensor is a module with its actual transferred Sym(K) action.
Its free-zero comparison, unit and associator come from the existing general
coefficient-module constructions.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

abbrev pointwiseTensor (X : C) (E : GeneralSymmetricSpectrum C K) :
    GeneralSymmetricSpectrum C K :=
  SymmetricSequence.pointwiseTensorModule (SymmetricSequence.tensorPowerSequence K) X E

abbrev pointwiseTensorFunctor (X : C) :
    GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K :=
  SymmetricSequence.pointwiseTensorModuleFunctor (SymmetricSequence.tensorPowerSequence K) X

lemma pointwiseTensor_level (X : C) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    level (pointwiseTensor X E) n = X ⊗ level E n := rfl

/-- Permutations act on the spectrum factor of the pointwise tensor. -/
lemma pointwiseTensor_permutation (X : C) (E : GeneralSymmetricSpectrum C K)
    (q : ℕ) (σ : Equiv.Perm (Fin q)) :
    (pointwiseTensor X E).X.map (FiniteBijection.permutation q σ) =
      X ◁ E.X.map (FiniteBijection.permutation q σ) := rfl

abbrev tensorFreeZeroPointwiseIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    tensor ((freeAt (K := K) 0).obj X) E ≅ pointwiseTensor X E :=
  SymmetricSequence.freeZeroTensorPointwiseModuleIso (SymmetricSequence.tensorPowerSequence K) X E

abbrev tensorFreeZeroPointwiseNatIso (X : C) :
    tensorLeft ((freeAt (K := K) 0).obj X) ≅ pointwiseTensorFunctor X :=
  SymmetricSequence.freeZeroTensorPointwiseModuleNatIso (SymmetricSequence.tensorPowerSequence K) X

def pointwiseTensorBifunctor : C ⥤ GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K :=
  FunctorTransport.transport ((freeAt (K := K) 0) ⋙ curriedTensor (GeneralSymmetricSpectrum C K))
    pointwiseTensorFunctor tensorFreeZeroPointwiseNatIso

def tensorFreeZeroPointwiseBifunctorIso :
    (freeAt (K := K) 0) ⋙ curriedTensor (GeneralSymmetricSpectrum C K) ≅
      pointwiseTensorBifunctor :=
  FunctorTransport.iso ((freeAt (K := K) 0) ⋙ curriedTensor (GeneralSymmetricSpectrum C K))
    pointwiseTensorFunctor tensorFreeZeroPointwiseNatIso

lemma tensorFreeZeroPointwiseNatIso_app (X : C) (E : GeneralSymmetricSpectrum C K) :
    (tensorFreeZeroPointwiseNatIso X).app E = tensorFreeZeroPointwiseIso X E := rfl

lemma pointwiseTensorBifunctor_obj (X : C) :
    (pointwiseTensorBifunctor (K := K)).obj X = pointwiseTensorFunctor X := rfl

lemma tensorFreeZeroPointwiseBifunctorIso_app (X : C) (E : GeneralSymmetricSpectrum C K) :
    (tensorFreeZeroPointwiseBifunctorIso.app X).app E = tensorFreeZeroPointwiseIso X E := rfl

/-- The map of pointwise tensors induced by maps in both variables. -/
def pointwiseTensorMap {X Y : C} (f : X ⟶ Y) {E F : GeneralSymmetricSpectrum C K}
    (g : E ⟶ F) : pointwiseTensor X E ⟶ pointwiseTensor Y F :=
  (pointwiseTensorBifunctor.map f).app E ≫ (pointwiseTensorFunctor Y).map g

abbrev pointwiseTensorUnitNatIso : pointwiseTensorFunctor (K := K) (𝟙_ C) ≅
    𝟭 (GeneralSymmetricSpectrum C K) :=
  SymmetricSequence.pointwiseTensorModuleUnitNatIso (SymmetricSequence.tensorPowerSequence K)

abbrev pointwiseTensorAssociator (X Y : C) (E : GeneralSymmetricSpectrum C K) :
    pointwiseTensor (X ⊗ Y) E ≅ pointwiseTensor X (pointwiseTensor Y E) :=
  SymmetricSequence.pointwiseTensorModuleAssociator (SymmetricSequence.tensorPowerSequence K) X Y E
lemma pointwiseTensorAssociator_level (X Y : C) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    (pointwiseTensorAssociator X Y E).hom.hom.app (FiniteBijection.of n) =
      (α_ X Y (level E n)).hom :=
  SymmetricSequence.pointwiseTensorModuleAssociator_level
    (SymmetricSequence.tensorPowerSequence K) X Y E n

/-- Naturality in the spectrum variable is verified on every level. -/
lemma pointwiseTensorAssociator_naturality (X Y : C)
    {E F : GeneralSymmetricSpectrum C K} (f : E ⟶ F) :
    (pointwiseTensorFunctor (X ⊗ Y)).map f ≫ (pointwiseTensorAssociator X Y F).hom =
      (pointwiseTensorAssociator X Y E).hom ≫
        (pointwiseTensorFunctor X).map ((pointwiseTensorFunctor Y).map f) := by
  apply Mod.hom_ext
  apply SymmetricSequence.hom_ext
  intro n
  change _ ≫ _ = _ ≫ _
  rw [SymmetricSequence.pointwiseTensorModuleFunctor_map_app,
    SymmetricSequence.pointwiseTensorModuleAssociator_level,
    SymmetricSequence.pointwiseTensorModuleAssociator_level,
    SymmetricSequence.pointwiseTensorModuleFunctor_map_app,
    SymmetricSequence.pointwiseTensorModuleFunctor_map_app]
  exact associator_naturality_right X Y (levelMap f n)

/-- The action associator as a natural isomorphism in the spectrum. -/
def pointwiseTensorAssociatorNatIso (X Y : C) :
    pointwiseTensorFunctor (K := K) (X ⊗ Y) ≅
      pointwiseTensorFunctor Y ⋙ pointwiseTensorFunctor X :=
  NatIso.ofComponents (pointwiseTensorAssociator X Y)
    (fun f ↦ pointwiseTensorAssociator_naturality X Y f)
end SerrePositivity.GeneralSymmetricSpectrum
