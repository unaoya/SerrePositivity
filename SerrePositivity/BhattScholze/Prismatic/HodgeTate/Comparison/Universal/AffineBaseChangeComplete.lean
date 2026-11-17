module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineModelsComplete
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元のaffine複体の通常係数拡大の被覆上の完備性

## 概要
元のaffine複体を基底へ制限して被覆へ通常係数拡大すると、元のpについて導来完備となる。

## 方針
元の基底生成元の作用が零であることを係数拡大で写し、像がpの単位倍であることを使う。

## 規約
元の複体のK-flat性や一般の結晶比較は使わない。ここでは通常係数拡大の完備性だけを述べる。

## 使われ方
元のηの始域の被覆模型から、同じ通常の係数拡大へ戻す完備化単位。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (r : ℕ)

/-- 元の基底生成元は、元のaffine複体の元の基底作用への制限を零化する。 -/
theorem affineComplexOnBase_generator_smulId_zero
    (K : Complex (affineAlgebra P r)) :
    SerrePositivity.smulId P.generator (affineComplexOnBase P r K) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  ext x
  change affineBaseToPolynomialMap P r P.generator • (show K.X i from x) = 0
  rw [affineBaseToPolynomialMap_generator, zero_smul]

/-- 元のaffine複体の通常の被覆への係数拡大は、pについて導来完備。 -/
theorem affineCoverBaseChange_complete_p (K : Complex (affineAlgebra P r)) :
    IsComplete (Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P)
      (DerivedCategory.Q.obj (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ)).obj (affineComplexOnBase P r K))) := by
  let B := Construction61.crystallineCoverRing P
  let f := (Construction61.crystallineCoverMap P).toRingHom
  let L := affineComplexOnBase P r K
  let E := (ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)
  have hd : SerrePositivity.smulId (f P.generator) (E.obj L) = 0 := by
    have h := congrArg E.map (affineComplexOnBase_generator_smulId_zero P r K)
    change ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
      (SerrePositivity.smulId P.generator L) = E.map 0 at h
    rw [SerrePositivity.baseChange_smulId, Functor.map_zero] at h
    exact h
  have hdQ : f P.generator • 𝟙 (DerivedCategory.Q.obj (E.obj L)) = 0 := by
    have h := congrArg DerivedCategory.Q.map hd
    simpa only [SerrePositivity.smulId, Functor.map_smul,
      CategoryTheory.Functor.map_id, Functor.map_zero] using h
  have hc : IsComplete B (coverImageCoordinates P 1) (DerivedCategory.Q.obj (E.obj L)) := by
    apply isComplete_of_scalar_pow_zero B _ _ 1
    simpa [pow_one, coverImageCoordinates] using hdQ
  exact (isComplete_associated_iff _ _ (coverImageCoordinates_associated P 1) _).mp hc

/-- 元の通常係数拡大への、同じ二つのp座標の完備化単位は擬同型。 -/
theorem affineCoverBaseChange_completionUnit_quasiIso (K : Complex (affineAlgebra P r)) :
    QuasiIso (finiteCompletionUnit (fun _ : Fin 2 => (p : Construction61.crystallineCoverRing P))
      (((ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ)).obj (affineComplexOnBase P r K))) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
  apply finiteCompletionUnit_isIso_of_isComplete
  intro j
  exact affineCoverBaseChange_complete_p P r K

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
