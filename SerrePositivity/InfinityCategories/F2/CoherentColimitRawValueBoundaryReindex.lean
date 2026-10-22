module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUniversalTriangleReindex
public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexRawBoundaryNaturality
public import SerrePositivity.InfinityCategories.F2.FunctorIsoValueReindex

/-!
概要：元の四因子値比較の等式を、全初期値の任意の再制限へ移す。
方針：元の普遍比較と境界比較の指定自然性を、抽象的な値比較の移送に入力する。
規約：元の全図式と指定因子を保持。使われ方：恒等初期値での計算の反映。
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
  (T : FunctorCompositionTriangle a b d) {K L : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
  (r : L ⟶ K)
local notation "V" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)

/-- 元の指定普遍比較と四因子境界式の等式は、任意の初期値制限で保持される。 -/
lemma coherentColimitRawUniversalBoundary_precomp
    (h : (coherentColimitRawUniversalTriangleComparison B T f).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T f) :
    (coherentColimitRawUniversalTriangleComparison B T (r ≫ f)).postcomp V =
      coherentColimitApexRawTriangleBoundaryAt B T (r ≫ f) :=
  functorIso_value_eq_of_precomp_heq
    (coherentColimitRawUniversalTriangleComparison B T f) V
    (coherentColimitApexRawTriangleBoundaryAt B T f) r
    (coherentColimitRawUniversalTriangleComparison B T (r ≫ f))
    (coherentColimitApexRawTriangleBoundaryAt B T (r ≫ f)) rfl rfl
    (coherentColimitRawUniversalTriangleComparison_precomp B T f r)
    (coherentColimitApexRawTriangleBoundaryAt_precomp B T f r) h

/-- 同値な係数制限なら、元の四因子値比較の等式を忠実に反映する。 -/
lemma coherentColimitRawUniversalBoundary_iff_precomp
    [Quasicategory K] [Quasicategory L] (hr : IsQCatEquivalence r) :
    (coherentColimitRawUniversalTriangleComparison B T f).postcomp V =
        coherentColimitApexRawTriangleBoundaryAt B T f ↔
      (coherentColimitRawUniversalTriangleComparison B T (r ≫ f)).postcomp V =
        coherentColimitApexRawTriangleBoundaryAt B T (r ≫ f) :=
  functorIso_value_eq_iff_precomp_heq
    (coherentColimitRawUniversalTriangleComparison B T f) V
    (coherentColimitApexRawTriangleBoundaryAt B T f) r hr
    (coherentColimitRawUniversalTriangleComparison B T (r ≫ f))
    (coherentColimitApexRawTriangleBoundaryAt B T (r ≫ f)) rfl rfl
    (coherentColimitRawUniversalTriangleComparison_precomp B T f r)
    (coherentColimitApexRawTriangleBoundaryAt_precomp B T f r)

end SerrePositivity.InfinityCategories.F2
