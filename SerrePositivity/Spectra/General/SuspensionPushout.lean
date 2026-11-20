module

public import SerrePositivity.Spectra.Pointed.CofiberPushout
public import SerrePositivity.Spectra.General.Zero
public import SerrePositivity.Spectra.General.MappingObject
public import SerrePositivity.Spectra.PointedSimplicialSet.Spheres
public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

/-! # The circle tensor as the actual quotient of the simplicial cylinder

For spectra over pointed simplicial sets and any coordinate K, parameter
tensor carries the defining quotient Δ[1]/∂Δ[1] to a pushout. The other
corner is proved zero. This is the underlying pushout calculation needed
for comparison with derived suspension; no homotopy-pushout conclusion is
assumed or asserted here.
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.GeneralSymmetricSpectrum

section Simplicial
open scoped Simplicial
variable {K : PointedSimplicialSet.{u}} (E : GeneralSymmetricSpectrum PointedSimplicialSet.{u} K)

abbrev intervalBoundaryTensorMap :=
  (mappingTensorFunctor E).map (PointedObject.adjoinFunctor.map (SSet.boundary.{u} 1).ι)

abbrev intervalBoundaryCollapse :=
  (mappingTensorFunctor E).map
    (PointedObject.toPoint (PointedObject.adjoin (SSet.boundary.{u} 1).toSSet))

abbrev circleTensorQuotient :=
  (mappingTensorFunctor E).map (PointedObject.cofiberProjection (SSet.boundary.{u} 1).ι)

abbrev circleTensorBasepoint :=
  (mappingTensorFunctor E).map (PointedObject.fromPoint PointedSimplicialSet.circle.{u})

lemma circleTensor_isPushout : IsPushout (intervalBoundaryTensorMap E)
    (intervalBoundaryCollapse E) (circleTensorQuotient E) (circleTensorBasepoint E) := by
  have := (mappingObjectAdjunction E).isLeftAdjoint
  exact PointedObject.map_cofiber_isPushout (SSet.boundary.{u} 1).ι (mappingTensorFunctor E)

lemma circleTensorPoint_isZero :
    IsZero ((mappingTensorFunctor E).obj PointedObject.point) := by
  have := (mappingObjectAdjunction E).isLeftAdjoint
  exact (PointedObject.point_isZero.isInitial.isInitialObj
    (mappingTensorFunctor E) PointedObject.point).isZero

lemma intervalBoundaryCollapse_eq_zero : intervalBoundaryCollapse E = 0 :=
  (circleTensorPoint_isZero E).eq_of_tgt _ _

lemma circleTensorQuotient_boundary :
    intervalBoundaryTensorMap E ≫ circleTensorQuotient E = 0 := by
  rw [(circleTensor_isPushout E).w, intervalBoundaryCollapse_eq_zero, zero_comp]

end Simplicial
end SerrePositivity.GeneralSymmetricSpectrum
