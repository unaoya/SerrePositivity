module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoTwoEdgeValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexRawTriangleBoundary
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedEndpointComparisons

/-!
概要：元の Apex 三角形の二 raw 辺の値比較を、同じ指定二因子として保持する。
方針：元の最後辺・第一辺の指定値をその順に束ね、同じ全初期値へ前合成する。
規約：元の raw 値比較と中間比較を変更しない。
使われ方：Ncomp の具体式と元の四因子境界式を接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₁" => pointedFiberValueTo (coherentColimitApex_raw_one_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "f" => coherentEdgeHom (SpaceInfinity.δ 2 s)
local notation "g" => coherentEdgeHom (SpaceInfinity.δ 0 s)
local notation "uf" => CategoryTheory.Functor.map SSet.uliftFunctor f
local notation "ug" => CategoryTheory.Functor.map SSet.uliftFunctor g

/-- 概要：元の二 raw 辺の指定値の合成。方針：同じ二因子を束ねる。
規約：元の値比較を保持。使われ方：Ncomp の実二辺の値。 -/
def coherentColimitApexRawCompositeValueIso :
    FunctorIso ((coherentColimitRawFiberTransport B a ≫ coherentColimitRawFiberTransport B b) ≫ V₂)
      (V₀ ≫ (uf ≫ ug)) :=
  functorIsoTwoEdgeValue (coherentColimitRawFiberTransport B a)
    (coherentColimitRawFiberTransport B b) V₀ V₁ V₂ uf ug
    (coherentColimitApexRawFirstValueIso B T) (coherentColimitApexRawLastValueIso B T)

/-- 概要：同じ全初期値で二辺の指定値を読む。方針：前合成と結合表示の正規化。
規約：元の初期値を保持。使われ方：全反転 Hom 係数での二辺値照合。 -/
def coherentColimitApexRawCompositeValueAt {K : SSet.{u + 1}}
    (q : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex) :
    FunctorIso (((q ≫ coherentColimitRawFiberTransport B a) ≫
      coherentColimitRawFiberTransport B b) ≫ V₂) (q ≫ (V₀ ≫ (uf ≫ ug))) :=
  functorIsoOfEq ((coherentColimitApexRawCompositeValueIso B T).precomp q)
    (by simp only [Category.assoc]) rfl

/-- 概要：元の終点比較と raw 二辺値の指定合成。方針：同じ実終点で合成する。
規約：元の三角形の全比較を保持。使われ方：零面値に続く Ncomp の二因子。 -/
def coherentColimitApexCompositeValueComposite :=
  (coherentColimitApexPointedTargetEndpointIso B T).postcomp V₂ ≪≫
    coherentColimitApexRawCompositeValueAt B T (coherentColimitApexCoefficientMap B T)

/-- 概要：元の境界式の長辺値を消去する。方針：同じ二辺因子の消去式を代入。
規約：元の三値と三角形を保持。使われ方：Nlong と Ncomp の値の照合。 -/
lemma coherentColimitApexRawTriangleBoundaryIso_long_cancel :
    coherentColimitApexRawTriangleBoundaryIso B T ≪≫ coherentColimitApexRawLongValueIso B T =
      coherentColimitApexRawCompositeValueIso B T ≪≫
        FunctorIso.precomp (coherentColimitApexTriangleLiftIso B T).symm V₀ := by
  unfold coherentColimitApexRawTriangleBoundaryIso coherentColimitApexRawCompositeValueIso
  exact functorIsoTriangleValueBoundary_twoEdge_cancel
    (coherentColimitRawFiberTransport B a) (coherentColimitRawFiberTransport B b)
    V₀ V₁ V₂ uf ug (coherentColimitApexRawFirstValueIso B T)
    (coherentColimitApexRawLastValueIso B T) (coherentColimitRawFiberTransport B d)
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentEdgeHom (SpaceInfinity.δ 1 s)))
    (coherentColimitApexRawLongValueIso B T) (coherentColimitApexTriangleLiftIso B T)

end SerrePositivity.InfinityCategories.F2
