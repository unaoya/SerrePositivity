module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransportAlgebra

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalUniversalSourceEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportPointDiagonalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportPointPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismBoundaryEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTransportConstantInterval
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
/-!
概要：元の全初期値上の一点普遍比較を、同じ実 pointed prism の指定対角比較へ戻す。
方針：初期係数制限後の同じ二輸送の比較と実 prism の一致を合成する。
規約：元の区間・指定点・全初期値・指定値を保持する。
使われ方：Ncomp の raw 最後辺の普遍比較と元の値因子の照合。
-/

@[expose] public section
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

noncomputable section
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C K : SSet.{u + 1}} [Quasicategory C]
  {x y : SpaceInfinity.{u} _⦋0⦌} (a : C ⟶ intervalMappingSpace x y)
  (l : C _⦋0⦌) (f : K ⟶ vertexFiber pointedSpaceProjection x)
local notation "p" => pointedSpaceProjection
local notation "v" => (SSet.const (a.app (Opposite.op ⦋0⦌) l) : K ⟶ intervalMappingSpace x y)
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v
local notation "P" => pointedIntervalTransportPointPrism a l f
/-- 概要：同じ全初期値の一点普遍比較は同じ実 prism の指定対角比較。
方針：初期値と一点の制限順序を照合し、同じ実境界を保持する。
規約：指定値を保持。使われ方：raw 最後辺の指定比較の回収。 -/
lemma pointedIntervalTransportAt_universalIso_precomp_heq_point_diagonal :
    HEq ((pointedIntervalTransportAt_universalIso a l).precomp f)
      (leftFibrationPrism_diagonalTransportIso p f (f ≫ pointedIntervalTransportAt a l)
        β h₀ h₁ P (pointedIntervalTransportPointPrism_start a l f)
        (pointedIntervalTransportPointPrism_finish a l f)
        ((pointedIntervalTransportPointPrism_projection a l f).trans
          (intervalMappingPoint_uncurry a l))) := by
  have hs := pointedIntervalTransportAt_universalIso_precomp_heq_source_endpoint a l f
  have hd := fiberTransportPointComparison_heq_diagonal p (f ≫ 𝟙 _) a
    ((pointedIntervalTransport a).precomposeSource f) l
  have h : HEq ((pointedIntervalTransportAt_universalIso a l).precomp f)
      (leftFibrationPrism_diagonalTransportIso p (f ≫ 𝟙 _)
        (lift (𝟙 K) (SSet.const l) ≫ ((pointedIntervalTransport a).precomposeSource f).endpoint)
        β h₀ h₁
        ((Δ[1] ◁ lift (𝟙 K) (SSet.const l)) ≫
          ((pointedIntervalTransport a).precomposeSource f).prism)
        (fiberTransportFamily_point_prism_start p (f ≫ 𝟙 _) (intervalMappingUncurry a)
          ((pointedIntervalTransport a).precomposeSource f) l)
        (fiberTransportFamily_point_prism_finish p (f ≫ 𝟙 _) (intervalMappingUncurry a)
          ((pointedIntervalTransport a).precomposeSource f) l)
        ((fiberTransportFamily_point_prism_projection p (f ≫ 𝟙 _) (intervalMappingUncurry a)
          ((pointedIntervalTransport a).precomposeSource f) l).trans
          (intervalMappingPoint_uncurry a l))) := by
    convert hs.trans hd using 1
  refine h.trans ?_
  apply diagonalTransportIso_heq_of_boundary
  · rfl
  · rfl
  · rfl
/-- 概要：同じ指定比較の値も同じ実 prism の指定対角値。
方針：固定区間の native 終点を照合して同じ値射へ後合成する。
規約：元の全初期値と値射を保持。使われ方：Ncomp の raw 値因子の照合。 -/
lemma pointedIntervalTransportAt_universalIso_precomp_postcomp_heq_point_diagonal
    {Z : SSet.{u + 1}} (V : vertexFiber p y ⟶ Z) :
    HEq (((pointedIntervalTransportAt_universalIso a l).precomp f).postcomp V)
      ((leftFibrationPrism_diagonalTransportIso p f (f ≫ pointedIntervalTransportAt a l)
        β h₀ h₁ P (pointedIntervalTransportPointPrism_start a l f)
        (pointedIntervalTransportPointPrism_finish a l f)
        ((pointedIntervalTransportPointPrism_projection a l f).trans
          (intervalMappingPoint_uncurry a l))).postcomp V) := by
  refine functorIso_postcomp_heq_of_heq _ _ rfl ?_
    (pointedIntervalTransportAt_universalIso_precomp_heq_point_diagonal a l f) V
  have hc : intervalMappingCurryOfEndpoints β h₀ h₁ = v := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints β h₀ h₁
  rw [hc, diagonalFiberTransport_constant_interval]
end SerrePositivity.InfinityCategories.F2
