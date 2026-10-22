module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficientNaturality

/-! 元の M[-1] の係数比較を、両変数に全 dg 自然な同じ比較へ束ねる。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 全次数自然な加群擬同型を成分に持つ、実制限 Hom への同じ係数比較。 -/
def dgGluingCrossHomCoefficientComparison :
    StrictNatTrans (dgGluingCrossCoefficientFunctor R C D M)
      (dgGluingCrossHomFunctor R C D M) :=
  dgModuleStrictNatTransOfHomNaturality R (DGGluingCFactor R C D M)
    (dgGluingCrossHomCoefficientModuleMap R C D M)
    (dgGluingCrossHomCoefficientModuleMap_naturality R C D M)

lemma dgGluingCrossHomCoefficientComparison_app
    (Y : DGGluingDFactor R C D M) :
    (dgGluingCrossHomCoefficientComparison R C D M).app Y =
      cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
        (dgGluingCrossHomCoefficientModuleMap R C D M Y)) := rfl

end SerrePositivity.InfinityCategories
