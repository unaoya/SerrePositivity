module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityLaxCompletedComparison
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityZeroBoundary
public import SerrePositivity.KST.SConstruction.PerfectStableArrowSquareComparison

/-!
概要：D2 の全比較から恒等実右面の指定包含・商・零角の三境界比較を構成する。
方針：元の固定 ν 辺と絶対恒等列の辺を回収し、可逆二成分付き区間全比較を取る。
規約：D2 の入力存在は未証明。三境界を全四角形や全長方形の比較と数えない。
使われ方：実右面の VerdierSquareDiagramIso に指定する全境界の接続準備。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => dgKInputStableValue R (dgOdotMilnorIdentityBaseInput R d)
local notation "L" => dgKInputStableValue R (dgOdotMilnorIdentityGluingInput R d)
local notation "D" => dgKInputStableValue R (dgOdotMilnorIdentityDifferenceInput R d)
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Λ" => laxCategory (𝟙 (Q)) (𝟙 (Q))
local notation "hC" => dgKInputStableValue_isIdempotentComplete R _
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
local notation "hΛ" => perfectLaxCategory_isIdempotentComplete (𝟙 (Q)) (𝟙 (Q)) (hQ) (hQ)

/-- 概要：実恒等零化面の Cat^perf 下辺は元の固定 ν 対角辺そのもの。
方針：元四辺固定式と同じ ν 全一単体回収を使う。
規約：元対角を保持。使われ方：右面の包含境界の型照合。 -/
lemma dgOdotMilnorIdentityNullSquare_perfect_diagonal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorIdentityDiagonalInputMap R d)).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgOdotMilnorIdentityDiagonalInputMap R d))

/-- 概要：実恒等零化面の Cat^perf 右辺は元の固定 ν 差辺そのもの。
方針：元四辺固定式と同じ ν 全一単体回収を使う。
規約：実 cone 差を保持。使われ方：右面の商境界の型照合。 -/
lemma dgOdotMilnorIdentityNullSquare_perfect_difference :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotMilnorIdentityDifferenceInputMap R d)).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgOdotMilnorIdentityDifferenceInputMap R d))

/-- 概要：同じ元基底値同値を右面始域の指定完全射にする。
方針：元の順方向とその同値完全性を束ねる。規約：同じ比較を保持。
使われ方：四辺比較で共通に使う始域成分。 -/
def dgOdotMilnorIdentityBaseComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (C) (Q) :=
  ⟨(dgOdotMilnorIdentityBaseValueEquivalence R d).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence⟩

namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：同じ供給中央同値を指定完全射にする。
方針：元の順方向の完全性を束ねる。規約：二境界で同じ成分を使う。
使われ方：実右面の共有中央頂点成分。 -/
def completedMiddleMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (L) (Λ) :=
  ⟨v.completedGluing.hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence v.completedGluing.isQCatEquivalence⟩

/-- 概要：同じ供給終域同値を元商への指定完全射にする。
方針：元基底値同値を後合成する。規約：差と零上辺で同じ成分を使う。
使われ方：実右面の共有終域頂点成分。 -/
def completedTargetMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (D) (Q) :=
  ⟨(v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)).hom,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
      (v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)).isQCatEquivalence⟩

/-- 概要：元包含辺の全比較と指定二頂点経路を同じ証人に保持する。
方針：同じ全対角比較を四辺の実ホモトピーへ移す。
規約：端点式を公開。使われ方：上下二胞体の共有境界の貼り合わせ。 -/
def diagonalWitness : PerfectStableArrowSquareWitness
    (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d))
    (IdentityLax.exactDiagonal (Q)) (dgOdotMilnorIdentityBaseComparison R d)
    v.completedMiddleMap (hC) (hC) (hQ) (hΛ) :=
  perfectStableArrowSquareWitness
    (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d))
    (IdentityLax.exactDiagonal (Q)) (dgOdotMilnorIdentityBaseComparison R d)
    v.completedMiddleMap (hC) (hC) (hQ) (hΛ) v.completedDiagonal

/-- 概要：元差辺の全比較と指定二頂点経路を同じ証人に保持する。
方針：同じ全 cone 比較を四辺の実ホモトピーへ移す。
規約：包含辺と同じ中央経路を使用。使われ方：上下二胞体の共有境界の貼り合わせ。 -/
def differenceWitness : PerfectStableArrowSquareWitness
    (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d))
    (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))) v.completedMiddleMap v.completedTargetMap
    (hC) (hC) (hΛ) (hQ) :=
  perfectStableArrowSquareWitness
    (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d))
    (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))) v.completedMiddleMap v.completedTargetMap
    (hC) (hC) (hΛ) (hQ) v.completedDifference.symm

/-- 概要：供給された全対角比較は元実対角辺と絶対恒等対角辺の区間全比較を与える。
方針：元基底値同値と供給中央同値を二成分に使う。
規約：D2 入力に条件付き。使われ方：実右面の指定包含全比較。 -/
def diagonalArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow
      (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)) (hC) (hC)).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (IdentityLax.exactDiagonal (Q))
      (hQ) (hΛ)).edge) :=
  v.diagonalWitness.comparisonOfEquivalences
    (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence
    v.completedGluing.isQCatEquivalence

/-- 概要：供給された全 cone 比較は元実差辺と絶対恒等 lax 差辺の区間全比較を与える。
方針：同じ供給中央同値と指定終域同値を二成分に使う。
規約：D2 入力に条件付き。使われ方：実右面の指定商全比較。 -/
def differenceArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow
      (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)) (hC) (hC)).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (exactLaxDifference (𝟙 (Q)) (𝟙 (Q)))
      (hΛ) (hQ)).edge) :=
  v.differenceWitness.comparisonOfEquivalences v.completedGluing.isQCatEquivalence
    (v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)).isQCatEquivalence

/-- 概要：絶対恒等提示から同じ実右零化面への三つの指定全境界比較。
方針：元四辺回収と構成した包含・商・零角比較を同じ向きで束ねる。
規約：全四角形比較の存在は別工程。使われ方：Sp 正本の右面全比較の境界引数。 -/
def squareBoundary (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.VerdierSquareBoundaryIso
    (dgOdotMilnorActualRightDiagram R d h).square
    (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) where
  inclusion := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (diagonalArrowComparison R d v)
    (dgOdotMilnorIdentityNullSquare_perfect_diagonal R d).symm
    (PerfectVerdierSequence.presentation_bottom (perfectIdentityLaxSequence (Q) (hQ))).symm).symm
  quotient := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (differenceArrowComparison R d v)
    (dgOdotMilnorIdentityNullSquare_perfect_difference R d).symm (by
      change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square
      rw [PerfectVerdierSequence.presentation_right, perfectIdentityLaxSequence_projection]
      rfl)).symm
  zero := dgOdotMilnorIdentityNullSquareZeroBoundary R d h
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
