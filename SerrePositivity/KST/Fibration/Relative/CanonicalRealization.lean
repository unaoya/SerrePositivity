module
public import SerrePositivity.KST.Fibration.Relative.CanonicalComparison
public import SerrePositivity.KST.Fibration.Relative.FibrationSupply
public import SerrePositivity.KST.Fibration.RelativeQuotientFiberComparison

/-!
概要：相対加法性と完成した c4 を、元の商の実 fiber と native 引き戻しへ統合する。
方針：同じ商実現比較を既存の fiber 同型へ渡し、S1 四角形を関手的 Kan 化する。
規約：商側は c5 の標準単体比較だけに条件付き。閉部分圏側は追加入力なし。
使われ方：K-6 b の元の包含・商・指定基点を保持した d への受け渡し。
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

/-- 概要：S1 の元の閉部分圏四角形を Ex∞ の native 四角形として保持する。
方針：同じ厳密四角形へ関手的 Kan 化を適用する。
規約：元の四辺・二胞体を選び直さない。
使われ方：相対核実現と同じ値域で無条件 S1 を消費する。 -/
def closedRelativeInfinitySquare {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  exInfinityCommSqInfinitySquare (closedRelativeSquare P)

/-- 概要：閉部分圏の同じ native 四角形は無条件に引き戻し。
方針：S-1 (c) の実四角形の引き戻し性を Kan 化へ渡す。
規約：有限旗自然性・商比較・共終性の入力なし。
使われ方：K-6 b の無条件な相対実現部分。 -/
theorem closedRelativeInfinitySquare_isPullback
    {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (closedRelativeInfinitySquare P) :=
  exInfinityCommSqInfinitySquare_isPullback _
    (closedRelativeSquare_homotopyPullback_unconditional P)

variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
  (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
    (relativeFirstRowSimplexQuotient d.projection n)))

/-- 概要：元の核の core S 実現を、元の商射の指定基点上の実 fiber へ同定する。
方針：c5 だけを残す相対実現比較を既存の fiber 同型へ代入する。
規約：同じ実商・実包含・基点を保持し、商比較の存在は主張しない。
使われ方：K-6 b から d へ渡す射影付き実 fiber 同型。 -/
def canonicalQuotientRealizationFiberIso :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj (sInputModel d.left)) ≅
      AnodyneHomotopy.anodyneQ.obj (quotientSFibrationFiber d.isVerdier) :=
  quotientSFibrationFiberIsoOfComparison d.isVerdier
    (SingleRelativeComparison.ofCanonicalFirstRowSimplices d hq).quotientComparison

/-- 概要：同じ商 fiber 同型の射影は、元の核包含の実現射を回収する。
方針：元の同じ fiber 比較の射影公式を使う。
規約：抽象的な対象同型だけで代用しない。
使われ方：d の第一射と b の包含を照合する。 -/
theorem canonicalQuotientRealizationFiberIso_projection :
    (canonicalQuotientRealizationFiberIso d hq).hom ≫
        AnodyneHomotopy.anodyneQ.map (quotientSFibrationFiberProjection d.isVerdier) =
      AnodyneHomotopy.anodyneQ.map
        (simplicialDiagonalFunctor.map (coreSExactMap d.inclusion)) :=
  quotientSFibrationFiberIsoOfComparison_hom_projection d.isVerdier
    (SingleRelativeComparison.ofCanonicalFirstRowSimplices d hq).quotientComparison

include hq in
/-- 概要：元の指定全 S• 四角形は c5 の標準単体商比較だけで引き戻し。
方針：無条件 c4 と同じ相対核の引き戻しを合成する。
規約：全正反復や固定 K の Sp 引き戻し性は要求しない。
使われ方：d の単回 BF 第一段検出へ渡す入力。 -/
theorem canonicalSingleS_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) :=
  (SingleRelativeComparison.ofCanonicalFirstRowSimplices d hq).isPullback d

end SerrePositivity.KST.Fibration.Relative
