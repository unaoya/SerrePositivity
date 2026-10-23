module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLongValueCriterion
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexRawTriangleCandidate

/-!
概要：任意の全初期値での候補と元の普遍比較の一致を、元の実長辺の値で忠実に判定する。
方針：同じ値射への反映判定と、全反転 Hom の係数同値の反映を合成する。
規約：元の候補・指定普遍比較・四因子を保持。使われ方：残る値照合の正確な完了条件。
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

/-- 全初期値での指定比較の一致は、同じ全 pointed 族の実長辺の具体的な値式と同値。 -/
lemma coherentColimitApexRawTriangleCandidate_eq_universal_iff_long_value :
    (∀ (K : SSet.{u + 1})
      (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex),
      coherentColimitApexRawTriangleCandidate B T f =
        coherentColimitRawUniversalTriangleComparison B T f) ↔
      (coherentColimitApexPointedTargetEndpointIso B T).postcomp V ≪≫
          coherentColimitApexRawTriangleBoundaryAt B T q =
        (coherentColimitApexPointedLongComparison B T).postcomp V := by
  constructor
  · intro h
    exact (coherentColimitApexRawUniversalBoundary_iff_long_value B T).mp
      ((coherentColimitApexRawTriangleCandidate_eq_universal_iff B T q).mp (h _ q))
  · intro h K f
    exact (coherentColimitApexRawTriangleCandidate_eq_universal_iff B T f).mpr
      (coherentColimitApexRawUniversalBoundary_of_long_value B T h f)

end SerrePositivity.InfinityCategories.F2
