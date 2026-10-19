module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalComponents
public import SerrePositivity.KST.DerivedBlowup.BaseRestrictionDGFunctor

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の有限重なり遷移を共通基底環上で扱う。
方針：実際の局所化環の代数射と半線形 dg 遷移を標準比較で基底制限する。
規約：新しい dg 構造を導入せず、既存の係数制限を使う。
使われ方：例外因子の全有限重なりの dg 代数図式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：例外因子の有限重なりの局所 dg 模型を共通基底環へ制限する。
方針：局所化環の構造射に沿う既存の dg 制限を適用する。
規約：KST Lemma 3.6。使われ方：係数図式の各頂点。 -/
abbrev FiniteOverlapExceptionalBaseObject (a : I → R) (i : I) (T : Finset I) :=
  DGRestriction (algebraMap R (FiniteOverlapRing R i T))
    (FiniteOverlapExceptionalKoszulObject R a i T)

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と共通基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の有限重なりの共通基底環上の dg 遷移。
方針：実際の半線形 dg 遷移を既存の基底制限構成へ渡す。
規約：KST Lemma 3.6。使われ方：全有限重なりの係数図式の射。 -/
def finiteOverlapExceptionalBaseDGTransition (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    DGFunctor R (FiniteOverlapExceptionalBaseObject R a i T)
      (FiniteOverlapExceptionalBaseObject R a k U) :=
  baseRestrictionDGFunctor (finiteOverlapChartMap R i k h hi)
    (finiteOverlapExceptionalDGTransition R a i k h hi)

set_option maxHeartbeats 2000000 in
-- 局所化環と共通基底環での Hom の各次数を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と共通基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の基底制限後の dg 遷移は元の Hom の像を保つ。
方針：標準係数制限比較の成分公式を使う。
規約：KST Lemma 3.6。使われ方：共通基底環での恒等・合成則。 -/
theorem finiteOverlapExceptionalBaseDGTransition_apply (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T)
    (v w : FiniteOverlapExceptionalKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T)
      (FiniteOverlapExceptionalKoszulObject R a i T) v w).X q) :
    (((finiteOverlapExceptionalBaseDGTransition R a i k h hi).map v w).f q) z =
      (((finiteOverlapExceptionalDGTransition R a i k h hi).map v w).f q) z :=
  baseRestrictionDGFunctor_exterior_apply (finiteOverlapChartMap R i k h hi)
    _ (finiteOverlapExceptionalDGTransition R a i k h hi) v w q z

set_option maxHeartbeats 1000000 in
-- 局所化環の dg 対象と基底制限後の対象を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と共通基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の基底制限は遷移の対象の像を保つ。
方針：標準係数制限比較の対象公式を使う。
規約：KST Lemma 3.6。使われ方：反復遷移の Hom の対象をそろえる。 -/
theorem finiteOverlapExceptionalBaseDGTransition_obj (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T)
    (v : FiniteOverlapExceptionalKoszulObject R a i T) :
    (finiteOverlapExceptionalBaseDGTransition R a i k h hi).obj v =
      (finiteOverlapExceptionalDGTransition R a i k h hi).obj v :=
  baseRestrictionDGFunctor_obj _ _ v

end SerrePositivity.KST.DerivedBlowup
