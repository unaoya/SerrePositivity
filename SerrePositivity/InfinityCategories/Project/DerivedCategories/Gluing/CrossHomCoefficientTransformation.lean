module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CrossHomCoefficientNaturality

/-! 元の M[-1] の係数比較を、両変数に全 dg 自然な同じ比較へ束ねる。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)

/-- 全次数自然な加群擬同型を成分に持つ、実制限 Hom への同じ係数比較。 -/
def dgGluingCrossHomCoefficientComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossCoefficientFunctor R C D M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomFunctor R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientModuleMap R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientModuleMap_naturality R C D M)

lemma dgGluingCrossHomCoefficientComparison_app
    (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M) :
    (dgGluingCrossHomCoefficientComparison R C D M).app Y =
      _root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCrossHomCoefficientModuleMap R C D M Y)) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
