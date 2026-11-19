module

public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorProduct
public import SerrePositivity.CategoryTheory.Monoidal.Action
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-! # 反復cotensorの比較のパラメータ自然性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 合成随伴による反復転置のパラメータ自然性の等式。 -/
def simplicialTensorCotensorProductPreLaw {K K' L L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (E F : SymmetricSpectrum.{u})
    (h : simplicialTensor K' (simplicialTensor L' E) ⟶ F) : Prop :=
  ActionComparisonNaturality.compositePreLaw
    (simplicialTensorCotensorAdjunction L) (simplicialTensorCotensorAdjunction L')
    (simplicialTensorCotensorAdjunction K) (simplicialTensorCotensorAdjunction K')
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map g))
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map f))
    (cotensorBifunctor.map (adjoinBasepointFunctor.map g).op)
    (cotensorBifunctor.map (adjoinBasepointFunctor.map f).op) E F h

/-- 各転置のパラメータ自然性から反復転置のパラメータ自然性を得る。 -/
lemma simplicialTensorCotensorProductHomEquiv_pre {K K' L L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (E F : SymmetricSpectrum.{u})
    (h : simplicialTensor K' (simplicialTensor L' E) ⟶ F) :
    simplicialTensorCotensorProductPreLaw f g E F h :=
  ActionComparisonNaturality.composite_pre
    (simplicialTensorCotensorAdjunction L) (simplicialTensorCotensorAdjunction L')
    (simplicialTensorCotensorAdjunction K) (simplicialTensorCotensorAdjunction K')
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map g))
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map f))
    (cotensorBifunctor.map (adjoinBasepointFunctor.map g).op)
    (cotensorBifunctor.map (adjoinBasepointFunctor.map f).op)
    (fun _ _ h => simplicialTensorCotensorHomEquiv_post g h)
    (fun _ _ h => simplicialTensorCotensorHomEquiv_post f h) E F h

/-- 反復cotensorの比較の単体的集合の両変数の自然性の等式。 -/
def simplicialCotensorProductParameterLaw {K K' L L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) : Prop :=
  ActionComparisonNaturality.parameterLaw
    (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorAdjunction (K' ⊗ L'))
    (simplicialTensorCotensorProductAdjunction K L)
    (simplicialTensorCotensorProductAdjunction K' L')
    (simplicialTensorProductNatIso K L) (simplicialTensorProductNatIso K' L')
    (fun F => simplicialCotensorPre (f ⊗ₘ g) F)
    (fun F => (simplicialCotensorFunctor L').map (simplicialCotensorPre f F) ≫
      simplicialCotensorPre g (simplicialCotensor K F)) E

/-- tensorの反復比較と転置の自然性から、cotensorの反復比較の自然性を得る。 -/
lemma simplicialCotensorProduct_parameter {K K' L L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) :
    simplicialCotensorProductParameterLaw f g E := by
  refine ActionComparisonNaturality.parameter_composite
    (simplicialTensorCotensorAdjunction L) (simplicialTensorCotensorAdjunction L')
    (simplicialTensorCotensorAdjunction K) (simplicialTensorCotensorAdjunction K')
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map g))
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map f))
    (cotensorBifunctor.map (adjoinBasepointFunctor.map g).op)
    (cotensorBifunctor.map (adjoinBasepointFunctor.map f).op)
    (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorAdjunction (K' ⊗ L'))
    (simplicialTensorProductNatIso K L) (simplicialTensorProductNatIso K' L')
    (fun F => simplicialTensorPost (f ⊗ₘ g) F)
    (fun F => simplicialCotensorPre (f ⊗ₘ g) F)
    ?_ ?_ ?_ E
  · intro F G h
    exact simplicialTensorCotensorHomEquiv_post (f ⊗ₘ g) h
  · intro F G h
    exact simplicialTensorCotensorProductHomEquiv_pre f g F G h
  · intro F
    exact ActionProductComparison.parameter adjoinBasepointFunctor.{u} pointwiseTensorBifunctor.{u}
      pointwiseTensorAssociatorNatIso.{u} adjoinBasepointProductIso.{u} f g F
      (adjoinBasepointProductIso_inv_naturality f g)
      (GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_naturality
        (adjoinBasepointFunctor.map f) (adjoinBasepointFunctor.map g) F)

end SerrePositivity.SymmetricSpectrum
