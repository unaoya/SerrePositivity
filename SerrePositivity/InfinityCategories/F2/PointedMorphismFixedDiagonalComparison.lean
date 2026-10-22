module

public import SerrePositivity.InfinityCategories.F2.PointedHomMorphismPrismComponent
public import SerrePositivity.InfinityCategories.F2.DiagonalPrismPrecompValue

/-!
概要：元の固定射の全値比較を、同じ固定射への制限後の実 prism の対角比較へ戻す。
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
/-- 元の反転 Hom の全係数を、pointed space の同じ宇宙へ持ち上げた単体集合。 -/
abbrev pointedReverseHomCoefficients (K L : KanObject.{u}) : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op

variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => pointedReverseHomCoefficients pointKanObject K
local notation "H" => pointedReverseHomCoefficients K L
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

local notation "β" => (Δ[1] ◁ r) ≫ intervalMappingUncurry v
local notation "P" => (Δ[1] ◁ lift x y) ≫ FiberTransportFamily.prism T

/-- 元の固定射への同じ係数制限後の実 prism による指定対角比較。 -/
def pointedMorphismFixedDiagonalComparison :=
  leftFibrationPrism_diagonalTransportIso p (r ≫ (x ≫ c))
    (r ≫ (lift x y ≫ FiberTransportFamily.endpoint T)) β
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      intervalMappingUncurry_zero, SSet.comp_const])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      intervalMappingUncurry_one, SSet.comp_const])
    ((Δ[1] ◁ r) ≫ P)
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      fiberTransportDiagonalPrism_start p c γ T x y]
        simp only [Category.assoc])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      fiberTransportDiagonalPrism_finish p c γ T x y]
        simp only [Category.assoc])
    (by rw [Category.assoc, fiberTransportDiagonalPrism_projection p c γ h₀ h₁ T x y])

/-- 元の固定射値比較は、同じ制限後の実 prism の指定対角比較の値と一致。 -/
lemma pointedHomMorphismValueComparison_heq_fixed_diagonal :
    HEq (pointedHomMorphismValueComparison f)
      ((pointedMorphismFixedDiagonalComparison f).postcomp V) := by
  refine (pointedHomMorphismValueComparison_heq_prism f).trans ?_
  exact leftFibrationPrism_diagonalTransportIso_precomp_postcomp_heq p (x ≫ c)
    (lift x y ≫ FiberTransportFamily.endpoint T)
    (intervalMappingUncurry v) (intervalMappingUncurry_zero v) (intervalMappingUncurry_one v)
    P (fiberTransportDiagonalPrism_start p c γ T x y)
    (fiberTransportDiagonalPrism_finish p c γ T x y)
    (fiberTransportDiagonalPrism_projection p c γ h₀ h₁ T x y) r
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      intervalMappingUncurry_zero, SSet.comp_const])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      intervalMappingUncurry_one, SSet.comp_const]) V

end SerrePositivity.InfinityCategories.F2
