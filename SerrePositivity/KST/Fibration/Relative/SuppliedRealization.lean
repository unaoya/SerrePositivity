module
public import SerrePositivity.KST.Fibration.Relative.CanonicalRealization
public import SerrePositivity.KST.LocalizingInvariants.VerdierFirstRowSimplexLocalization

/-!
概要：Sp の実 c5 を同じ元の相対実現と指定全四角形へ代入する。
方針：元の Verdier 列の射影を使う全次数局所化供給を canonical 比較へ渡す。
規約：n=0 を含め、追加の供給仮定を取らない。NonConnective は import しない。
使われ方：Fibration 主集約における K-6 b・c の無条件な実現界面。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：同じ指定全四角形と元の商実現の二比較を無条件で構成する。
方針：Sp の全次数 c5 を完成した c4 の消費側へ代入する。
規約：hIso・hc5・hcofinal の入力を残さない。
使われ方：元の単回相対実現を無条件で消費する公開入口。 -/
def SingleRelativeComparison.supplied (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) : SingleRelativeComparison h :=
  SingleRelativeComparison.ofCanonicalFirstRowSimplices h
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso h.toVerdierSequence)

/-- 概要：元の指定全 S• 四角形は無条件に引き戻し。
方針：同じ実供給二比較を相対核実現の判定へ渡す。
規約：固定連結 K の Sp 四角形の引き戻し性とは区別する。
使われ方：K-6 d の単回 BF 検出の実入力。 -/
theorem suppliedSingleS_isPullback (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (h.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  (SingleRelativeComparison.supplied h).isPullback h

/-- 概要：元の核の実現と元の商射の指定 fiber は無条件に局所化同型。
方針：Sp の同じ c5 を元の射影付き fiber 比較へ代入する。
規約：包含・商・指定基点を保つ。
使われ方：無条件 K-6 b の実 fiber 同型。 -/
def suppliedQuotientRealizationFiberIso (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj (sInputModel h.left)) ≅
      AnodyneHomotopy.anodyneQ.obj (quotientSFibrationFiber h.isVerdier) :=
  canonicalQuotientRealizationFiberIso h
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso h.toVerdierSequence)

/-- 概要：同じ無条件 fiber 同型の射影は元の核包含の実現射を回収する。
方針：実 c5 を同じ元の射影公式に代入する。
規約：対象別の抽象同型へ置き換えない。
使われ方：K-B3 に渡す元の包含の照合。 -/
theorem suppliedQuotientRealizationFiberIso_projection (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (suppliedQuotientRealizationFiberIso h).hom ≫
        AnodyneHomotopy.anodyneQ.map (quotientSFibrationFiberProjection h.isVerdier) =
      AnodyneHomotopy.anodyneQ.map
        (simplicialDiagonalFunctor.map (coreSExactMap h.inclusion)) :=
  canonicalQuotientRealizationFiberIso_projection h
    (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso h.toVerdierSequence)

end SerrePositivity.KST.Fibration.Relative
