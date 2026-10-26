module
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
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants F2.Idempotent
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
    squareBottomEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (coherentNerveEdge (dgOdotMilnorIdentityDiagonalInputMap R d)).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgOdotMilnorIdentityDiagonalInputMap R d))

/-- 概要：実恒等零化面の Cat^perf 右辺は元の固定 ν 差辺そのもの。
方針：元四辺固定式と同じ ν 全一単体回収を使う。
規約：実 cone 差を保持。使われ方：右面の商境界の型照合。 -/
lemma dgOdotMilnorIdentityNullSquare_perfect_difference :
    squareRightEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).2.1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (coherentNerveEdge (dgOdotMilnorIdentityDifferenceInputMap R d)).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgOdotMilnorIdentityDifferenceInputMap R d))

namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：供給された全対角比較は元実対角辺と絶対恒等対角辺の区間全比較を与える。
方針：元基底値同値と供給中央同値を二成分に使う。
規約：D2 入力に条件付き。使われ方：実右面の指定包含全比較。 -/
def diagonalArrowComparison : FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow
      (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d)) (hC) (hC)).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (IdentityLax.exactDiagonal (Q))
      (hQ) (hΛ)).edge) := by
  let a : ExactMap (C) (Q) := ⟨(dgOdotMilnorIdentityBaseValueEquivalence R d).hom,
    isExactFunctor_of_isQCatEquivalence
      (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence⟩
  let b : ExactMap (L) (Λ) := ⟨v.completedGluing.hom,
    isExactFunctor_of_isQCatEquivalence v.completedGluing.isQCatEquivalence⟩
  exact (nonempty_perfectStableArrowFunctorIso_of_equivalences
    (dgKInputNuMap R (dgOdotMilnorIdentityDiagonalInputMap R d))
    (IdentityLax.exactDiagonal (Q)) a b (hC) (hC) (hQ) (hΛ) v.completedDiagonal
    (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence
    v.completedGluing.isQCatEquivalence).some

/-- 概要：供給された全 cone 比較は元実差辺と絶対恒等 lax 差辺の区間全比較を与える。
方針：同じ供給中央同値と指定終域同値を二成分に使う。
規約：D2 入力に条件付き。使われ方：実右面の指定商全比較。 -/
def differenceArrowComparison : FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow
      (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)) (hC) (hC)).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (exactLaxDifference (𝟙 (Q)) (𝟙 (Q)))
      (hΛ) (hQ)).edge) := by
  let a : ExactMap (L) (Λ) := ⟨v.completedGluing.hom,
    isExactFunctor_of_isQCatEquivalence v.completedGluing.isQCatEquivalence⟩
  let E := v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)
  let b : ExactMap (D) (Q) := ⟨E.hom, isExactFunctor_of_isQCatEquivalence E.isQCatEquivalence⟩
  exact (nonempty_perfectStableArrowFunctorIso_of_equivalences
    (dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d))
    (exactLaxDifference (𝟙 (Q)) (𝟙 (Q))) a b (hC) (hC) (hΛ) (hQ)
    v.completedDifference.symm v.completedGluing.isQCatEquivalence E.isQCatEquivalence).some

/-- 概要：絶対恒等提示から同じ実右零化面への三つの指定全境界比較。
方針：元四辺回収と構成した包含・商・零角比較を同じ向きで束ねる。
規約：全四角形比較の存在は別工程。使われ方：Sp 正本の右面全比較の境界引数。 -/
def squareBoundary (h : DGGluingMilnorSquare R d) : VerdierSquareBoundaryIso
    (dgOdotMilnorActualRightDiagram R d h).square
    (dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R) where
  inclusion := by
    change FunctorIso
      (squareBottomEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) _
    rw [PerfectVerdierSequence.presentation_bottom,
      dgOdotMilnorIdentityNullSquare_perfect_diagonal]
    exact v.diagonalArrowComparison.symm
  quotient := by
    change FunctorIso
      (squareRightEdge ≫ (perfectIdentityLaxSequence (Q) (hQ)).presentation.square) _
    rw [PerfectVerdierSequence.presentation_right, perfectIdentityLaxSequence_projection,
      dgOdotMilnorIdentityNullSquare_perfect_difference]
    exact v.differenceArrowComparison.symm
  zero := dgOdotMilnorIdentityNullSquareZeroBoundary R d h
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
