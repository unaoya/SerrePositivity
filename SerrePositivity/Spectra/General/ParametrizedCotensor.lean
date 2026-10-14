module

public import SerrePositivity.Spectra.General.Cotensor
public import SerrePositivity.CategoryTheory.ParametrizedAdjunctionTransport

/-! # The general spectrum tensor/cotensor adjunction with parameter

Both bifunctors are the existing transported module functors. The natural
free-zero comparisons transport the closed module adjunction and its parameter
compatibility, not just its objectwise adjunctions.
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

/-- The full contravariant parameter comparison for the cotensor. -/
def internalHomCotensorBifunctorIso :
    (freeAt (K := K) 0).op ⋙ internalHomBifunctor ≅ cotensorBifunctor :=
  FunctorTransport.iso ((freeAt (K := K) 0).op ⋙ internalHomBifunctor)
    (fun X ↦ cotensorFunctor X.unop) (fun X ↦ internalHomCotensorNatIso X.unop)

/-- Tensor/cotensor representability, including naturality in the C parameter. -/
def pointwiseTensorCotensorParametrizedAdjunction :
    pointwiseTensorBifunctor (K := K) ⊣₂ cotensorBifunctor :=
  ParametrizedAdjunctionTransport.left
    (ParametrizedAdjunctionTransport.right
      (ParametrizedAdjunctionTransport.restrict
        (MonoidalClosed.internalHomAdjunction₂ (C := GeneralSymmetricSpectrum C K))
        (freeAt 0)) internalHomCotensorBifunctorIso)
    tensorFreeZeroPointwiseBifunctorIso

/-- Parameter compatibility for the same tensor/cotensor Hom equivalence. -/
lemma pointwiseTensorHomEquiv_naturality_parameter {X Y : C} (f : X ⟶ Y)
    (E F : GeneralSymmetricSpectrum C K) (g : pointwiseTensor Y E ⟶ F) :
    pointwiseTensorHomEquiv X E F ((pointwiseTensorBifunctor.map f).app E ≫ g) =
      pointwiseTensorHomEquiv Y E F g ≫ (cotensorBifunctor.map f.op).app F :=
  pointwiseTensorCotensorParametrizedAdjunction.homEquiv_naturality_one f g

end SerrePositivity.GeneralSymmetricSpectrum
