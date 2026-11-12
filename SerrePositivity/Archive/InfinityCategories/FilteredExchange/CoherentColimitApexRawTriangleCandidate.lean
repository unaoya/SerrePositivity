module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawBoundaryNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueToReflection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulFunctorIsoCoherence

/-!
概要：元の三辺・指定 path の境界比較候補を fiber へ戻し、元の普遍比較との照合を値で判定。
方針：同じ固定値射の充満忠実性で、元の四因子の指定値の逆像を取る。
規約：元の普遍比較への一致は未仮定。使われ方：残る全族の三角形整合の明示した判定式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
local notation "V" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)

/-- 元の四因子の境界指定値を同じ raw fiber の実二辺・長辺終点へ戻した比較候補。 -/
def coherentColimitApexRawTriangleCandidate :
    FunctorIso ((f ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b)
      (f ≫ coherentColimitRawFiberTransport B d) :=
  IsFullyFaithful.preimageFunctorIso
    (pointedFiberValueTo_isQCatEquivalence (coherentColimitApex_raw_two_vertex B T)).isFullyFaithful
    (coherentColimitApexRawTriangleBoundaryAt B T f)

/-- 同じ候補の固定値への像は、元の三辺と指定 path の四因子の境界比較そのもの。 -/
lemma coherentColimitApexRawTriangleCandidate_value :
    (coherentColimitApexRawTriangleCandidate B T f).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T f :=
  IsFullyFaithful.preimageFunctorIso_postcomp _ _

/-- 元の普遍比較への一致は、同じ固定値の四因子式への一致と同値。未証明の整合を分離する。 -/
lemma coherentColimitApexRawTriangleCandidate_eq_universal_iff :
    coherentColimitApexRawTriangleCandidate B T f =
      coherentColimitRawUniversalTriangleComparison B T f ↔
    (coherentColimitRawUniversalTriangleComparison B T f).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T f := by
  constructor
  · intro h
    exact (congrArg (fun e => FunctorIso.postcomp e V) h).symm.trans
      (coherentColimitApexRawTriangleCandidate_value B T f)
  · intro h
    apply pointedFiberValueTo_postcompose_functorIso_injective K
      (coherentColimitApex_raw_two_vertex B T)
    exact (coherentColimitApexRawTriangleCandidate_value B T f).trans h.symm

end SerrePositivity.InfinityCategories.F2
