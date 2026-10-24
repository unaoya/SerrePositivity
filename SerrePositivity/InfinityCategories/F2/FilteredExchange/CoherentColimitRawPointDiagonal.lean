module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexLastConstantComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalPointPrismDiagonal
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalPrismBoundaryValue

/-!
概要：同じ raw 余極限辺の指定点普遍比較を、元の実 prism の指定対角比較へ戻す。
方針：元の指定点と全初期値を一般の一点 prism の比較へ代入する。
規約：元の raw 辺・指定点・実両端と値を保持する。
使われ方：Ncomp の最後辺の正方形の raw 普遍因子を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (b : SSet.Homotopy G J)
  {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone G).vertex)
local notation "p" => pointedSpaceProjection
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "v" => (SSet.const (coherentColimitRawIntervalVertex B b) : K ⟶ _)
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v

/-- 概要：元の raw 輸送 prism の指定対角比較。方針：同じ全初期値と実両端を固定。
規約：指定比較を再選択しない。使われ方：最後辺の自然性正方形の raw 因子。 -/
def coherentColimitRawPointDiagonalComparison :=
  leftFibrationPrism_diagonalTransportIso p f (f ≫ coherentColimitRawFiberTransport B b)
    β h₀ h₁ (coherentColimitRawTransportPointPrism B b f)
    (coherentColimitRawTransportPointPrism_start B b f)
    (coherentColimitRawTransportPointPrism_finish B b f)
    (coherentColimitRawTransportPointPrism_projection_constant B b f)

/-- 概要：元の同じ全初期値の一点普遍比較は raw 実 prism の指定比較。
方針：同じ実 prism から底と実両端の一致を反映する。
規約：元の指定値を保持。使われ方：raw 因子の値への代入。 -/
lemma coherentColimitRawUniversalIso_precomp_heq_point_diagonal :
    HEq ((pointedIntervalTransportAt_universalIso A l).precomp f)
      (coherentColimitRawPointDiagonalComparison B b f) := by
  refine (pointedIntervalTransportAt_universalIso_precomp_heq_point_diagonal A l f).trans ?_
  apply diagonalTransportIso_heq_of_boundary
  · rfl
  · rfl
  · rfl

/-- 概要：同じ raw 普遍比較の値は同じ実 prism の指定対角値。
方針：同じ実両端・prism・値射を保持して後合成する。
規約：全初期値を保持。使われ方：Ncomp の元の raw 値因子の照合。 -/
lemma coherentColimitRawUniversalIso_precomp_postcomp_heq_point_diagonal
    {Z : SSet.{u + 1}} (V : vertexFiber p (coherentDiagramTotalCocone J).vertex ⟶ Z) :
    HEq (((pointedIntervalTransportAt_universalIso A l).precomp f).postcomp V)
      ((coherentColimitRawPointDiagonalComparison B b f).postcomp V) := by
  refine (pointedIntervalTransportAt_universalIso_precomp_postcomp_heq_point_diagonal
    A l f V).trans ?_
  apply diagonalTransportIso_postcomp_heq_of_boundary
  · rfl
  · rfl
  · rfl
  · rfl

/-- 概要：raw 実 prism の native 終点は同じ指定点の普遍輸送の前合成。
方針：同じ定値区間を curry し、固定区間の対角輸送を計算する。
規約：全初期値と元の区間頂点を保持。使われ方：raw 値の比の終点表示。 -/
lemma coherentColimitRawPointDiagonal_native :
    diagonalFiberTransport p f (intervalMappingCurryOfEndpoints β h₀ h₁) =
      f ≫ (functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport p (coherentDiagramTotalCocone G).vertex
          (coherentDiagramTotalCocone J).vertex).app (Opposite.op ⦋0⦌)
            (coherentColimitRawIntervalVertex B b)) := by
  have hc : intervalMappingCurryOfEndpoints β h₀ h₁ = v := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints β h₀ h₁
  rw [hc, diagonalFiberTransport_constant_interval]

end SerrePositivity.InfinityCategories.F2
