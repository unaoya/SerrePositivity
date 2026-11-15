module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelRefinement
public import SerrePositivity.AlgebraicGeometry.CoefficientModelColimit
public import Mathlib.CategoryTheory.Filtered.Final

/-!
概要：元の affine v 被覆の被覆模型の圏は filtered かつ全模型の圏で final。
方針：構成した実際の射を Mathlib の full/faithful な部分圏の判定へ渡す。
規約：元の環写像と同じ実際の cocone を余極限として保持する。
使われ方：B03・B04 の小さい有限型被覆模型の実際の filtered 余極限。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable (k : Type u) [CommRing k] [IsNoetherianRing k]
  {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C]
  (g : R →ₐ[k] C) (hv : IsAffineVCover g.toRingHom)
include hv

/-- 実際の v 被覆の被覆係数模型の圏は filtered。 -/
theorem isFiltered_coefficientVCoverModelCategory : IsFiltered (CoefficientVCoverModelCategory k g) :=
  IsFiltered.of_exists_of_isFiltered_of_fullyFaithful (coefficientVCoverModelProperty k g).ι
    (fun X ↦ exists_coefficientModel_to_vCover k g hv X)

/-- 被覆模型の全模型への包含は final。 -/
theorem coefficientVCoverModelInclusion_final : (coefficientVCoverModelProperty k g).ι.Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful (coefficientVCoverModelProperty k g).ι
    (fun X ↦ exists_coefficientModel_to_vCover k g hv X)

/-- 同じ宇宙の小さい被覆模型の添字も filtered。 -/
theorem isFiltered_coefficientVCoverModelIndex : IsFiltered (CoefficientVCoverModelIndex k g) := by
  letI := isFiltered_coefficientVCoverModelCategory k g hv
  exact IsFiltered.of_equivalence (equivSmallModel (CoefficientVCoverModelCategory k g))

/-- 被覆模型の実際の環写像の cocone は、元の環写像を余極限に持つ。 -/
def coefficientVCoverModelArrowCoconeIsColimit : IsColimit (coefficientVCoverModelArrowCocone k g) := by
  letI := coefficientVCoverModelInclusion_final k g hv
  exact (Functor.Final.isColimitWhiskerEquiv (coefficientVCoverModelProperty k g).ι
    (coefficientModelArrowCocone g)).symm (coefficientModelArrowCoconeIsColimit g)

/-- 元の v 被覆は、同じ宇宙の小さい被覆模型の実際の環写像の filtered colimit。 -/
def coefficientVCoverModelSmallArrowCoconeIsColimit :
    IsColimit (coefficientVCoverModelSmallArrowCocone k g) :=
  (coefficientVCoverModelArrowCoconeIsColimit k g hv).whiskerEquivalence
    (equivSmallModel (CoefficientVCoverModelCategory k g)).symm

end SerrePositivity.AlgebraicGeometry
