module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalSemilinearTransition
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGTransition

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子を実際の有限重なり環に装備する。
方針：局所化環の係数・比座標を全生成元の Koszul 模型へ代入し、半線形 dg 遷移を使う。
規約：関係式による通常の商に置き換えず、Cartier 生成元を含む全 Koszul 微分を保持する。
使われ方：例外因子の大域係数図式と blowup チャートへの接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なり環上の例外因子の Koszul dg 対象型。
方針：pivot に Cartier 方程式、他にチャート関係式を置く全添字表示を使う。
規約：KST Lemma 3.6。使われ方：例外因子の有限重なり図式の局所対象。 -/
abbrev FiniteOverlapExceptionalKoszulObject (a : I → R) (i : I) (T : Finset I) :=
  ExteriorKoszulObject (Finsupp.linearCombination (FiniteOverlapRing R i T)
    (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i))

/-- 概要：有限重なりの blowup チャートから例外因子への局所 dg 係数射。
方針：Cartier 生成元を追加する指定包含を実際の局所化環へ適用する。
規約：KST Lemma 3.6、幾何の射と反変。使われ方：例外因子の局所制限。 -/
def finiteOverlapExceptionalInclusionDGFunctor (a : I → R) (i : I) (T : Finset I) :
    DGFunctor (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T)
      (FiniteOverlapExceptionalKoszulObject R a i T) :=
  exceptionalChartInclusionDGFunctor
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T) i

/-- 概要：実際の有限重なり環射と pivot 変更に沿う例外因子の dg 遷移。
方針：局所化環の代数射が基底係数を保つ式を半線形例外因子遷移へ渡す。
規約：KST Lemma 3.6、行先は始点の係数環へ制限する。
使われ方：例外因子の全有限重なりの係数図式。 -/
def finiteOverlapExceptionalDGTransition (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    DGFunctor (FiniteOverlapRing R i T) (FiniteOverlapExceptionalKoszulObject R a i T)
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (FiniteOverlapExceptionalKoszulObject R a k U)) :=
  exceptionalSemilinearDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T)
    (fun j => algebraMap R (FiniteOverlapRing R k U) (a j)) (finiteOverlapCoordinates R k U) i k
    (by funext j; exact (finiteOverlapChartMap R i k h hi).commutes (a j))

set_option maxHeartbeats 1000000 in
-- 局所化環の係数制限と外積 Hom の各次数を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの例外因子 dg 遷移の全次数の元の公式。
方針：実際の代数射の係数変更後、行先環上の可逆基底変換を適用する。
規約：KST Lemma 3.6。使われ方：重なりの整合性・合成則の計算。 -/
theorem finiteOverlapExceptionalDGTransition_inclusion (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T)
    (v w : FiniteOverlapExceptionalKoszulObject R a i T) (q : ℤ)
    (z : (exteriorKoszulCochain (Finsupp.linearCombination (FiniteOverlapRing R i T)
      (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
        (finiteOverlapCoordinates R i T) i))).X q) :
    exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R k U)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R k U) (a j))
          (finiteOverlapCoordinates R k U) k)) q
        (((finiteOverlapExceptionalDGTransition R a i k h hi).map v w).f q z) =
      ExteriorAlgebra.map (exceptionalTransitionEquiv k i (finiteOverlapCoordinates R k U)
        ((finiteOverlapChartMap R i k h hi).toRingHom ∘ finiteOverlapCoordinates R i T)).toLinearMap
        (freeExteriorScalarMap (finiteOverlapChartMap R i k h hi).toRingHom
          (exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R i T)
            (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
              (finiteOverlapCoordinates R i T) i)) q z)) :=
  exceptionalSemilinearDGFunctor_inclusion (finiteOverlapChartMap R i k h hi).toRingHom
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T)
    (fun j => algebraMap R (FiniteOverlapRing R k U) (a j)) (finiteOverlapCoordinates R k U) i k
    (by funext j; exact (finiteOverlapChartMap R i k h hi).commutes (a j)) v w q z

end SerrePositivity.KST.DerivedBlowup
