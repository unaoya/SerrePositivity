module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawBoundaryReflection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedLongEndpointEquality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の四因子境界式との整合を、同じ全 pointed 族の実終点と実長辺の値で判定する。
方針：同じ全比較の終点像を左から合成し、元の普遍長辺比較との厳密な合成則を使う。
規約：元の指定因子を保持。使われ方：右 Hom 成分との値の照合の具体的な残り。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "V" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "E" => coherentColimitApexPointedTargetEndpointIso B T
local notation "U" => coherentColimitRawUniversalTriangleComparison B T q
local notation "L" => coherentColimitApexPointedLongComparison B T

/-- 元の全係数での四因子式は、同じ全比較の終点像と実長辺の値の指定式と同値。 -/
lemma coherentColimitApexRawUniversalBoundary_iff_long_value :
    FunctorIso.postcomp U V = coherentColimitApexRawTriangleBoundaryAt B T q ↔
      FunctorIso.postcomp E V ≪≫ coherentColimitApexRawTriangleBoundaryAt B T q =
        FunctorIso.postcomp L V := by
  have h := congrArg (fun e => FunctorIso.postcomp e V)
    (coherentColimitApexPointedTargetEndpointIso_trans_universal B T)
  rw [functorIso_postcomp_trans] at h
  constructor
  · intro hu
    rw [hu] at h
    exact h
  · intro he
    have hc := congrArg (fun e => (FunctorIso.postcomp E V).symm ≪≫ e) (h.trans he.symm)
    simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using hc

/-- 同じ実長辺での値の照合が済めば、任意の全初期値で元の四因子式へ反映できる。 -/
lemma coherentColimitApexRawUniversalBoundary_of_long_value
    (h : FunctorIso.postcomp E V ≪≫ coherentColimitApexRawTriangleBoundaryAt B T q =
      FunctorIso.postcomp L V) {K : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex) :
    (coherentColimitRawUniversalTriangleComparison B T f).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T f :=
  coherentColimitApexRawUniversalBoundary_of_identity B T
    ((coherentColimitApexRawUniversalBoundary_iff_coefficient B T).mpr
      ((coherentColimitApexRawUniversalBoundary_iff_long_value B T).mpr h)) f

end SerrePositivity.InfinityCategories.F2
