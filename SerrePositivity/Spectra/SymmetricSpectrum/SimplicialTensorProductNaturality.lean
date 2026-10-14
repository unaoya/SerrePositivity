module

public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorProduct
public import SerrePositivity.CategoryTheory.Monoidal.ActionProductComparison

/-! # 直積による反復作用のパラメータ自然性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 反復tensorの比較の単体的集合の両変数に関する自然性の等式。 -/
def simplicialTensorProductParameterLaw {K K' L L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) : Prop :=
  ActionProductComparison.parameterLaw adjoinBasepointFunctor.{u} pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} adjoinBasepointProductIso.{u} f g E

/-- 自由基点追加の直積比較と作用の結同比較の自然性を、反復tensorの比較へ送る。 -/
lemma simplicialTensorProduct_parameter {K K' L L' : SSet.{u}}
    (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) :
    simplicialTensorProductParameterLaw f g E :=
  ActionProductComparison.parameter adjoinBasepointFunctor.{u} pointwiseTensorBifunctor.{u}
    pointwiseTensorAssociatorNatIso.{u} adjoinBasepointProductIso.{u} f g E
    (adjoinBasepointProductIso_inv_naturality f g)
    (pointwiseTensorAssociator_parameter_naturality
      (adjoinBasepointFunctor.map f) (adjoinBasepointFunctor.map g) E)

end SerrePositivity.SymmetricSpectrum
