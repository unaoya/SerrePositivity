module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CFactorComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DFactorComparison
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! 同じ両制限射影を順関手に保つ、実充満因子と元の二圏の H⁰ 同値。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

def dgGluingCFactorHomotopyEquivalence (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M) ≌ HomotopyCategory R C := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M
  letI := F.onHomotopy_full_of_homQuasiIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection_homQuasiIso R C D M)
  letI := F.onHomotopy_faithful_of_homQuasiIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection_homQuasiIso R C D M)
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection_essSurj R C D M hD
  letI : F.onHomotopy.IsEquivalence := {}
  exact F.onHomotopy.asEquivalence

def dgGluingDFactorHomotopyEquivalence (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) ≌ HomotopyCategory R D := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection R C D M
  letI := F.onHomotopy_full_of_homQuasiIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection_homQuasiIso R C D M)
  letI := F.onHomotopy_faithful_of_homQuasiIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection_homQuasiIso R C D M)
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection_essSurj R C D M hC
  letI : F.onHomotopy.IsEquivalence := {}
  exact F.onHomotopy.asEquivalence

lemma dgGluingCFactorHomotopyEquivalence_functor (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (dgGluingCFactorHomotopyEquivalence R C D M hD).functor =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).onHomotopy := rfl

omit [Small.{u} D] in
lemma dgGluingDFactorHomotopyEquivalence_functor (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    (dgGluingDFactorHomotopyEquivalence R C D M hC).functor =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection R C D M).onHomotopy := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
