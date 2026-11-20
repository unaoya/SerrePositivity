module

public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAssociator
public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModuleAssociator

/-! # 各段のsmashによる作用の結同比較の各段 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (level)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- スペクトルの結同比較の順射は球面係数加群の結同比較に一致する。 -/
lemma pointwiseTensorAssociator_module_hom (X Y : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) :
    (pointwiseTensorAssociator X Y E).hom =
      (SymmetricSequence.pointwiseTensorModuleAssociator sphereSequence.{u} X Y E).hom := by
  change (TensorActionTransport.associatorNatIso (freeAt.{u} 0) pointwiseTensorBifunctor.{u}
    sphereTensorFreeZeroPointwiseBifunctorIso.{u} freeZeroTensorIso.{u} X Y).hom.app E = _
  rw [TensorActionTransport.associator_hom]
  exact SymmetricSequence.pointwiseTensorModuleAssociator_free_hom sphereSequence.{u} X Y E

/-- スペクトルの作用の結同比較の各段は通常のsmashの結合子。 -/
lemma pointwiseTensorAssociator_level (X Y : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorAssociator X Y E).hom.hom.app (FiniteBijection.of q) =
      (α_ X Y (level E q)).hom := by
  rw [pointwiseTensorAssociator_module_hom]
  exact SymmetricSequence.pointwiseTensorModuleAssociator_level sphereSequence.{u} X Y E q

/-- スペクトルの作用の逆結同比較の各段も通常の逆結合子。 -/
lemma pointwiseTensorAssociator_inv_level (X Y : PointedSimplicialSet.{u})
    (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorAssociator X Y E).inv.hom.app (FiniteBijection.of q) =
      (α_ X Y (level E q)).inv := by
  have h : pointwiseTensorAssociator X Y E =
      SymmetricSequence.pointwiseTensorModuleAssociator sphereSequence.{u} X Y E :=
    Iso.ext (pointwiseTensorAssociator_module_hom X Y E)
  rw [h]
  exact SymmetricSequence.pointwiseTensorModuleAssociator_inv_level sphereSequence.{u} X Y E q

end SerrePositivity.SymmetricSpectrum
