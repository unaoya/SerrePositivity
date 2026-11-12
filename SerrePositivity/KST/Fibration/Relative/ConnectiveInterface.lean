module
public import SerrePositivity.KST.Fibration.Relative.AdditivityFiber
public import SerrePositivity.KST.Fibration.QuotientSKernelPositiveStages
public import SerrePositivity.KST.Fibration.StableBoundaryKanComparison

/-!
概要：元の相対 S• 実現の fiber 性と、K-B c の二比較による指定四角形への接続。
方針：加法性の実核四角形を Kan 化し、商比較と全関手同型で輸送する。
規約：c の未供給入力は明示する。局所化圏値図式から高次整合性を推論しない。
使われ方：厳密 dg 未完備列の同じ全 S• 四角形を K-B d へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の相対 S• 核四角形の全単体を Kan 化する。
方針：元の厳密四角形へ既存 Ex∞ coherent 構成を適用。
規約：商比較は不要。使われ方：加法性からの相対実現の実四角形。 -/
def relativeRealizationInfinitySquare {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  exInfinityCommSqInfinitySquare (relativeSKernelRealizationSquare i q)

/-- 概要：元の相対 S• 実現四角形の無条件の fiber 性。
方針：加法性・全 W 列の Segal 実現による核四角形を Kan 化する。
規約：同じ四辺・二胞体を保持。使われ方：商比較前の K-6 b 本体。 -/
theorem relativeRealizationInfinitySquare_isPullback
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (relativeRealizationInfinitySquare i q) :=
  exInfinityCommSqInfinitySquare_isPullback _
    (relativeSKernelRealizationSquare_homotopyPullback h)

/-- 概要：c の商実現比較と全四角形比較を同じ型で保持。
方針：元の比較射の可逆性と指定全関手同型を記録。
規約：存在は c の供給境界。使われ方：未完備実列の d の仮定を供給。 -/
structure SingleRelativeComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) where
  quotientComparison : IsIso (AnodyneHomotopy.anodyneQ.map
    (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap d.projection)))
  squareComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
    (quotientSKernelInfinitySquare d.inclusion d.projection)

/-- 概要：正段商比較と指定全図式同型による供給境界の構成。
方針：既証の零段を使い元の商実現比較を得る。
規約：正段入力・全図式入力の存在は主張しない。使われ方：c4・c5 の直接消費。 -/
def SingleRelativeComparison.ofPositiveStages (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeSQuotientMap d.projection (n + 1))))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0))
      (quotientSKernelInfinitySquare d.inclusion d.projection)) :
    SingleRelativeComparison d where
  quotientComparison := relativeSQuotientRealization_localized_isIso_of_positive_stages
    d.projection hq
  squareComparison := e

/-- 概要：二比較から元の指定全 S• 四角形の引き戻し性を得る。
方針：実相対核四角形を元の商比較で移し、全関手同型で戻す。
規約：点別同値・辺だけの比較は入力にしない。使われ方：K-B d の単回仮定。 -/
theorem SingleRelativeComparison.isPullback (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (c : SingleRelativeComparison d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  (quotientSKernelInfinitySquare_isPullback d.inclusion d.projection d.isVerdier
    c.quotientComparison).of_functorIso c.squareComparison.symm

end SerrePositivity.KST.Fibration.Relative
