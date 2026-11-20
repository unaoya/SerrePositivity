module

public import SerrePositivity.Spectra.General.PointwiseTensor
public import SerrePositivity.CategoryTheory.Monoidal.Mod.InternalHomFree
public import SerrePositivity.Spectra.SymmetricSequence.UnshiftedInternalHom

/-! # Pointwise cotensor of general symmetric spectra

The module action is transported through the free-zero Day-Hom comparison.
The underlying levels are the ordinary internal Hom objects in C. The functors
and adjunction use the actual module comparison, not merely levelwise objects.
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

abbrev homBySequenceCotensorIso (X : C) (E : GeneralSymmetricSpectrum C K) :=
  SymmetricSequence.freeInternalHomSequenceIso 0 X E.X ≪≫
    SymmetricSequence.zeroShiftInternalHomIso X E.X

def cotensor (X : C) (E : GeneralSymmetricSpectrum C K) : GeneralSymmetricSpectrum C K :=
  MonoidalModuleInternalHom.transportedObj (SymmetricSequence.tensorPowerSequence K)
    ((SymmetricSequence.freeAt 0).obj X) E (homBySequenceCotensorIso X E)

lemma cotensor_level (X : C) (E : GeneralSymmetricSpectrum C K) (n : ℕ) :
    level (cotensor X E) n = (ihom X).obj (level E n) := rfl

abbrev internalHomCotensorIso (X : C) (E : GeneralSymmetricSpectrum C K) :
    internalHom ((freeAt (K := K) 0).obj X) E ≅ cotensor X E :=
  MonoidalModuleInternalHom.freeHomModuleIso (SymmetricSequence.tensorPowerSequence K)
    ((SymmetricSequence.freeAt 0).obj X) E ≪≫
      MonoidalModuleInternalHom.transportedIso (SymmetricSequence.tensorPowerSequence K)
        ((SymmetricSequence.freeAt 0).obj X) E (homBySequenceCotensorIso X E)

def cotensorFunctor (X : C) : GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K :=
  FunctorTransport.transport (internalHomFunctor ((freeAt (K := K) 0).obj X))
    (cotensor X) (internalHomCotensorIso X)

def internalHomCotensorNatIso (X : C) :
    internalHomFunctor ((freeAt (K := K) 0).obj X) ≅ cotensorFunctor X :=
  FunctorTransport.iso (internalHomFunctor ((freeAt (K := K) 0).obj X))
    (cotensor X) (internalHomCotensorIso X)

abbrev internalHomBifunctor : (GeneralSymmetricSpectrum C K)ᵒᵖ ⥤
    GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K :=
  MonoidalModuleInternalHom.homBifunctor (SymmetricSequence.tensorPowerSequence K)

def cotensorBifunctor : Cᵒᵖ ⥤ GeneralSymmetricSpectrum C K ⥤ GeneralSymmetricSpectrum C K :=
  FunctorTransport.transport ((freeAt (K := K) 0).op ⋙ internalHomBifunctor)
    (fun X ↦ cotensorFunctor X.unop) (fun X ↦ internalHomCotensorNatIso X.unop)

def freeZeroTensorCotensorAdjunction (X : C) :
    tensorLeft ((freeAt (K := K) 0).obj X) ⊣ cotensorFunctor X :=
  (tensorInternalHomAdjunction ((freeAt (K := K) 0).obj X)).ofNatIsoRight
    (internalHomCotensorNatIso X)

def pointwiseTensorCotensorAdjunction (X : C) :
    pointwiseTensorFunctor (K := K) X ⊣ cotensorFunctor X :=
  (freeZeroTensorCotensorAdjunction X).ofNatIsoLeft (tensorFreeZeroPointwiseNatIso X)

abbrev pointwiseTensorHomEquiv (X : C) (E F : GeneralSymmetricSpectrum C K) :
    (pointwiseTensor X E ⟶ F) ≃ (E ⟶ cotensor X F) :=
  (pointwiseTensorCotensorAdjunction X).homEquiv E F
lemma pointwiseTensorHomEquiv_naturality_source (X : C)
    {E E' : GeneralSymmetricSpectrum C K} (a : E ⟶ E') (F : GeneralSymmetricSpectrum C K)
    (f : pointwiseTensor X E' ⟶ F) :
    pointwiseTensorHomEquiv X E F ((pointwiseTensorFunctor X).map a ≫ f) =
      a ≫ pointwiseTensorHomEquiv X E' F f :=
  (pointwiseTensorCotensorAdjunction X).homEquiv_naturality_left a f

end SerrePositivity.GeneralSymmetricSpectrum
