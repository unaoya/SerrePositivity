module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexRawEdgeValues
public import SerrePositivity.InfinityCategories.F2.FunctorIsoTriangleValueBoundary
public import SerrePositivity.InfinityCategories.F2.FunctorIsoUliftRecovery

/-!
概要：元の余極限二単体の三辺比較と指定三角形同型を、同じ実輸送の値比較へ束ねる。
方針：同じ二単体の指定同型を持ち上げ、四つの元の指定因子を合成する。
規約：元の指定 path と三辺を保持。使われ方：普遍三角形残余の同じ値との照合候補。
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
local notation "s" => coherentColimitApexTriangle B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)

/-- 元の同じ二単体の指定三角形同型を、三つの元の辺の Kan 射の持ち上げで読む。 -/
def coherentColimitApexTriangleLiftIso :=
  functorIsoOfEq ((spaceInfinityTriangleIso s).ulift.{u, u + 1}) rfl
    ((SSet.uliftFunctor.{u + 1, u}).map_comp (coherentEdgeHom (SpaceInfinity.δ 2 s))
      (coherentEdgeHom (SpaceInfinity.δ 0 s)))

/-- 元の四因子を保つ、実二辺輸送と長辺輸送の固定値での境界比較候補。 -/
def coherentColimitApexRawTriangleBoundaryIso :
    FunctorIso ((coherentColimitRawFiberTransport B a ≫
      coherentColimitRawFiberTransport B b) ≫ V₂) (coherentColimitRawFiberTransport B d ≫ V₂) :=
  functorIsoTriangleValueBoundary
    (coherentColimitRawFiberTransport B a) (coherentColimitRawFiberTransport B b)
    (coherentColimitRawFiberTransport B d) V₀ V₁ V₂
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 2 s)))
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 0 s)))
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 1 s)))
    (coherentColimitApexRawFirstValueIso B T) (coherentColimitApexRawLastValueIso B T)
    (coherentColimitApexRawLongValueIso B T) (coherentColimitApexTriangleLiftIso B T)

/-- 同じ境界比較候補は、任意の全初期値で同じ実両端に前合成できる。 -/
def coherentColimitApexRawTriangleBoundaryAt {K : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex) :
    FunctorIso (((f ≫ coherentColimitRawFiberTransport B a) ≫
      coherentColimitRawFiberTransport B b) ≫ V₂)
      ((f ≫ coherentColimitRawFiberTransport B d) ≫ V₂) :=
  functorIsoOfEq ((coherentColimitApexRawTriangleBoundaryIso B T).precomp f)
    (by simp only [Category.assoc]) (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.F2
