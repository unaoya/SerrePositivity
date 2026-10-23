module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawValueBoundaryReindex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexCoefficientMap
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoValueReindex

/-!
概要：元の普遍比較と四因子境界式の整合を、全反転 Hom 係数で忠実に判定する。
方針：元の二比較の係数自然性と、同じ初点係数同値の前合成の忠実性を使う。
規約：元の指定比較と四因子を保持。使われ方：全係数の値照合から元の全族への反映。
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
  (T : FunctorCompositionTriangle a b d)
local notation "X" => vertexFiber pointedSpaceProjection
  (JoinCocone.vertex (coherentDiagramTotalCocone F))
local notation "V" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "q" => coherentColimitApexCoefficientMap B T

/-- 恒等初期値での四因子式の整合は、任意の全初期値で同じ指定式へ移る。 -/
lemma coherentColimitApexRawUniversalBoundary_of_identity
    (h : (coherentColimitRawUniversalTriangleComparison B T (𝟙 X)).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T (𝟙 X))
    {K : SSet.{u + 1}} (f : K ⟶ X) :
    (coherentColimitRawUniversalTriangleComparison B T f).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T f :=
  coherentColimitRawUniversalBoundary_precomp B T (𝟙 X) f h

/-- 元の恒等初期値での指定式は、元の全反転 Hom の係数同値で忠実に判定できる。 -/
lemma coherentColimitApexRawUniversalBoundary_iff_coefficient :
    (coherentColimitRawUniversalTriangleComparison B T (𝟙 X)).postcomp V =
        coherentColimitApexRawTriangleBoundaryAt B T (𝟙 X) ↔
      (coherentColimitRawUniversalTriangleComparison B T q).postcomp V =
        coherentColimitApexRawTriangleBoundaryAt B T q :=
  coherentColimitRawUniversalBoundary_iff_precomp B T (𝟙 X) q
    (coherentColimitApexCoefficientMap_isQCatEquivalence B T)

end SerrePositivity.InfinityCategories.F2
