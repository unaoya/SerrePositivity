module
public import SerrePositivity.DifferentialGraded.Verdier.ScalarQuotientSourceSquare
public import SerrePositivity.DifferentialGraded.Verdier.CompletionSquareShift

/-! # 直接局所化した係数変更の Karoubi 完備化と局所 perfect 比較 -/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

/-- 元の係数変更を先に Verdier 局所化した関手の、実際の Karoubi 延長。 -/
def sourceScalarCompletedFunctor :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A' (DGBaseChange φ D) S :=
  (functorExtension₂ _ _).obj (sourceScalarVerdierFunctor φ D S)

instance sourceScalarCompletedFunctorCommShift :
    (sourceScalarCompletedFunctor φ D S).CommShift ℤ := by
  dsimp [sourceScalarCompletedFunctor]
  infer_instance
instance sourceScalarCompletedFunctorIsTriangulated :
    (sourceScalarCompletedFunctor φ D S).IsTriangulated := by
  dsimp [sourceScalarCompletedFunctor]
  infer_instance

/-- 未完備の指定商からの標準包含と、直接局所化の完備化との正方形。 -/
def sourceScalarCompletedFactors :
    toKaroubi (TriaQuotient A D S) ⋙ sourceScalarCompletedFunctor φ D S ≅
      sourceScalarVerdierFunctor φ D S ⋙ toKaroubi (TriaQuotient A' (DGBaseChange φ D) S) :=
  karoubiFactor (sourceScalarVerdierFunctor φ D S)

instance sourceScalarCompletedFactorsCommShift :
    NatTrans.CommShift (sourceScalarCompletedFactors φ D S).hom ℤ :=
  karoubiFactorCommShift _

def sourceScalarCompletedFactorsTriangle :=
  Functor.mapTriangleIso (sourceScalarCompletedFactors φ D S)

variable (h : localKFlat A D S) (h' : localKFlat A' (DGBaseChange φ D) S)

/-- 直接局所化と局所同値による輸送の比較を、実際の Karoubi 延長で完備化する。 -/
def sourceScalarCompletedTransportIso :
    sourceScalarCompletedFunctor φ D S ≅ scalarCompletedTriaFunctor φ D S h h' :=
  (functorExtension₂ _ _).mapIso (sourceScalarLocalTransportIso φ D S h h')

/-- 完備化した直接局所化と、明示的 dg 商側の tria の係数変更との正方形。 -/
def sourceScalarCompletedTriaSquare :
    sourceScalarCompletedFunctor φ D S ⋙
        (localCompletedQuotientEquivalence A' (DGBaseChange φ D) S h').functor ≅
      (localCompletedQuotientEquivalence A D S h).functor ⋙
        (functorExtension₂ _ _).obj (quotientScalarTriaFunctor φ S) :=
  karoubiFunctorSquare _ _ (sourceScalarLocalQuotientSquare φ D S)

/-- 全 tria–Perf 比較を用いた、直接局所化の完備化と実際の Perf 係数変更の正方形。 -/
def sourceScalarCompletedPerfectSquare :
    sourceScalarCompletedFunctor φ D S ⋙
        (graphCompletedPerfectComparison A' (DGBaseChange φ D) S h').functor ≅
      (graphCompletedPerfectComparison A D S h).functor ⋙ quotientScalarPerfectFunctor φ D S :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight (sourceScalarCompletedTriaSquare φ D S h h') _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft _ (quotientScalarKaroubiPerfectSquare φ S) ≪≫ (associator _ _ _).symm

/-- 直接局所化の完備化は、既存の局所 perfect enhancement 比較とも可換する。 -/
def sourceScalarCompletedLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙ sourceScalarCompletedFunctor φ D S ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor :=
  isoWhiskerLeft _ (sourceScalarCompletedTransportIso φ D S h h') ≪≫
    scalarCompletedLocalPerfectSquare φ D S h h'

/-- 直接局所化した完備係数変更と、以前の完備 perfect 輸送経路の同定。 -/
def sourceScalarCompletionComparisonIso :
    sourceScalarCompletedFunctor φ D S ≅ completedScalarExtension φ D S h h' :=
  sourceScalarCompletedTransportIso φ D S h h' ≪≫ scalarCompletionComparisonIso φ D S h h'
end SerrePositivity.DifferentialGraded.DGQuotient
