module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalTransition
public import SerrePositivity.KST.DerivedBlowup.ExceptionalSemilinearChartSquare

/-!
概要：KST v4 Def 3.1・Lemma 3.6（pp.11–14）の例外因子の局所射を有限重なりへ接続する。
方針：実際の環射の係数・規格化座標公式を半線形 dg 可換四角形へ適用する。
規約：既存の blowup チャート dg 遷移を保持し、係数制限を明示する。
使われ方：例外因子の有限重なり図式と blowup への局所閉埋め込みの整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 二つの局所化環の dg 関手の係数制限と豊穣 Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：実際の有限重なりの blowup 遷移と例外因子の局所 dg 射は可換。
方針：半線形の可換四角形へ、局所化環射が係数を保ち座標を規格化する式を渡す。
規約：KST Def 3.1・Lemma 3.6、元の指定チャート遷移と実際の環射を使う。
使われ方：例外因子の全有限重なり上での局所射の整合性。 -/
theorem finiteOverlapExceptionalInclusionDGFunctor_transition (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) :
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapDGTransition R a i k h hi)
        (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
          (finiteOverlapExceptionalInclusionDGFunctor R a k U)) =
      EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapExceptionalInclusionDGFunctor R a i T)
        (finiteOverlapExceptionalDGTransition R a i k h hi) :=
  exceptionalSemilinearDGFunctor_chart_square (finiteOverlapChartMap R i k h hi).toRingHom
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T)
    (fun j => algebraMap R (FiniteOverlapRing R k U) (a j)) (finiteOverlapCoordinates R k U) i k
    (finiteOverlapUnit R k U i (h hi))
    (by funext j; exact (finiteOverlapChartMap R i k h hi).commutes (a j))
    (finiteOverlapChartMap_coordinates R i k h hi)
    (by simp [finiteOverlapCoordinates]) (finiteOverlapUnit_val R k U i (h hi))

end SerrePositivity.KST.DerivedBlowup
