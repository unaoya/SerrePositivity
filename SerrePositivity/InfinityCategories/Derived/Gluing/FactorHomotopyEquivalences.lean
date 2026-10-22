module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CFactorComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.DFactorComparison
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology

/-! 同じ両制限射影を順関手に保つ、実充満因子と元の二圏の H⁰ 同値。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

def dgGluingCFactorHomotopyEquivalence (hD : IsDGPretriangulated R D) :
    HomotopyCategory R (DGGluingCFactor R C D M) ≌ HomotopyCategory R C := by
  let F := dgGluingCFactorProjection R C D M
  letI := F.onHomotopy_full_of_homQuasiIso
    (dgGluingCFactorProjection_homQuasiIso R C D M)
  letI := F.onHomotopy_faithful_of_homQuasiIso
    (dgGluingCFactorProjection_homQuasiIso R C D M)
  letI := dgGluingCFactorProjection_essSurj R C D M hD
  letI : F.onHomotopy.IsEquivalence := {}
  exact F.onHomotopy.asEquivalence

def dgGluingDFactorHomotopyEquivalence (hC : IsDGPretriangulated R C) :
    HomotopyCategory R (DGGluingDFactor R C D M) ≌ HomotopyCategory R D := by
  let F := dgGluingDFactorProjection R C D M
  letI := F.onHomotopy_full_of_homQuasiIso
    (dgGluingDFactorProjection_homQuasiIso R C D M)
  letI := F.onHomotopy_faithful_of_homQuasiIso
    (dgGluingDFactorProjection_homQuasiIso R C D M)
  letI := dgGluingDFactorProjection_essSurj R C D M hC
  letI : F.onHomotopy.IsEquivalence := {}
  exact F.onHomotopy.asEquivalence

lemma dgGluingCFactorHomotopyEquivalence_functor (hD : IsDGPretriangulated R D) :
    (dgGluingCFactorHomotopyEquivalence R C D M hD).functor =
      (dgGluingCFactorProjection R C D M).onHomotopy := rfl

omit [Small.{u} D] in
lemma dgGluingDFactorHomotopyEquivalence_functor (hC : IsDGPretriangulated R C) :
    (dgGluingDFactorHomotopyEquivalence R C D M hC).functor =
      (dgGluingDFactorProjection R C D M).onHomotopy := rfl

end SerrePositivity.InfinityCategories
