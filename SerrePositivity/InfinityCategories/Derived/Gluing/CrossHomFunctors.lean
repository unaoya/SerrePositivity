module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficient
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Module.ShiftHom

/-! 実充満因子間の制限 Hom と、同じ M[-1] を値に持つ加群値 dg 関手。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => DGGluingObject R C D M
local notation "A" => DGGluingCFactor R C D M
local notation "B" => DGGluingDFactor R C D M

/-- D 因子を C 因子上の全 Hom 右加群に送る、実 gluing dg 関手。 -/
def dgGluingCrossHomFunctor : DGFunctor R B (RightModule R A) :=
  ((dgGluingDFactorInclusion R C D M).comp (dgYoneda R G)).comp
    (dgModuleRestriction R A G (dgGluingCFactorInclusion R C D M).op)

/-- 元の双加群を両因子の射影で制限し、−1 シフトした同じ係数 dg 関手。 -/
def dgGluingCrossCoefficientFunctor : DGFunctor R B (RightModule R A) :=
  (((dgGluingDFactorProjection R C D M).comp M.toFunctor).comp
    (dgModuleRestriction R A C (dgGluingCFactorProjection R C D M).op)).comp
      (moduleShiftDG R A (-1))

lemma dgGluingCrossHomFunctor_value
    (X : DGGluingCFactor R C D M) (Y : DGGluingDFactor R C D M) :
    ((dgGluingCrossHomFunctor R C D M).obj Y).obj (op X) =
      homObject R G X.val Y.val := rfl

lemma dgGluingCrossCoefficientFunctor_value
    (X : DGGluingCFactor R C D M) (Y : DGGluingDFactor R C D M) :
    ((dgGluingCrossCoefficientFunctor R C D M).obj Y).obj (op X) =
      (M.value X.val.left Y.val.right)⟦(-1 : ℤ)⟧ := rfl

/-- 同じ二 dg 関手の各評価間の実比較。全 dg 自然性は別途証明する。 -/
def dgGluingCrossHomFunctorComparisonComponent
    (X : DGGluingCFactor R C D M) (Y : DGGluingDFactor R C D M) :
    ((dgGluingCrossCoefficientFunctor R C D M).obj Y).obj (op X) ⟶
      ((dgGluingCrossHomFunctor R C D M).obj Y).obj (op X) :=
  dgGluingCrossHomCoefficientMap R C D M X Y

lemma dgGluingCrossHomFunctorComparisonComponent_quasiIso
    (X : DGGluingCFactor R C D M) (Y : DGGluingDFactor R C D M) :
    QuasiIso (dgGluingCrossHomFunctorComparisonComponent R C D M X Y) :=
  dgGluingCrossHomCoefficientMap_quasiIso R C D M X Y

end SerrePositivity.InfinityCategories
