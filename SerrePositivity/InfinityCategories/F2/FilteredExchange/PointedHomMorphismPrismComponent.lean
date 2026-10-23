module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedHomMorphismReverseComponent
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberTransportDiagonalComparisonPresentation

/-!
概要：元の固定射の全値比較を、同じ元の実二 prism の指定比較へ一致させる。
方針：固定成分の回収と、全対角比較の実 prism 表示を合成する。
規約：元の指定比較・全係数を保持。使われ方：元の実長辺の普遍比較との値照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom K L))
local notation "r" => lift (𝟙 A) (SSet.const (ULift.up (SSet.opObjEquiv.symm (functorVertex f))))
local notation "x" => fst A H ≫ Iso.hom
  (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K))
local notation "y" => snd A H ≫ Iso.hom (uliftOppositeIso (SimplicialCategory.sHom K L))
local notation "p" => pointedSpaceProjection
local notation "c" => pointedReverseKanFiberComparison K
local notation "γ" => pointedReverseKanHomInterval K L
local notation "h₀" => pointedReverseKanHomInterval_zero K L
local notation "h₁" => pointedReverseKanHomInterval_one K L
local notation "T" => pointedReverseKanCompositionTransportFamily K L
local notation "v" => y ≫ intervalMappingCurryOfEndpoints γ h₀ h₁
local notation "V" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))

/-- 元の固定射の値比較は、同じ全対角の実二 prism の指定比較の値の同じ制限。 -/
lemma pointedHomMorphismValueComparison_heq_prism :
    HEq (pointedHomMorphismValueComparison f)
      (((leftFibrationPrism_diagonalTransportIso p (x ≫ c)
        (lift x y ≫ FiberTransportFamily.endpoint T)
        (intervalMappingUncurry v) (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
        ((Δ[1] ◁ lift x y) ≫ FiberTransportFamily.prism T)
        (fiberTransportDiagonalPrism_start p c γ T x y)
        (fiberTransportDiagonalPrism_finish p c γ T x y)
        (fiberTransportDiagonalPrism_projection p c γ h₀ h₁ T x y)).postcomp V).precomp r) := by
  exact (pointedHomMorphismValueComparison_heq_reverse f).trans
    (fiberTransportDiagonalIso_postcomp_precomp_heq_prism p c γ h₀ h₁ T x y V r)

end SerrePositivity.InfinityCategories.F2
