module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalProductComponents

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の基底 Ko(A;a) から各共通表示への係数射。
方針：基底の自由 Koszul dg 代数を各有限重なり環へ係数変更する。
規約：原典の射影を係数 dg 代数の反変な射として再構成する。
使われ方：例外因子から導来零点スキームへの射の係数図式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：基底の全 a_j の列に対する Koszul dg 代数。
方針：既存一対象外積 dg 圏の自己 Hom をモノイド対象にする。
規約：KST Lemma 3.6。使われ方：導来零点スキームの係数。 -/
def baseKoszulDGAlgebra (a : I → R) : Mon (Complex R) :=
  dgEndMonoid R (ExteriorKoszulObject (Finsupp.linearCombination R a)) .point

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：基底 Koszul dg 模型から有限重なりの共通表示への指定 dg 関手。
方針：局所化環の構造射に自由 Koszul の係数変更を適用する。
規約：KST Lemma 3.6。使われ方：係数代数射の単位・積保存。 -/
def finiteOverlapExceptionalProductBaseDGFunctor (a : I → R) (i : I) (T : Finset I) :
    DGFunctor R (ExteriorKoszulObject (Finsupp.linearCombination R a))
      (FiniteOverlapExceptionalProductObject R a i T) :=
  freeKoszulScalarDGFunctor (algebraMap R (FiniteOverlapRing R i T)) a

set_option maxHeartbeats 2000000 in
-- 局所化環への dg 係数変更とモノイド対象の構造射を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：基底 Koszul dg 代数から有限重なりの共通 Koszul dg 代数への指定射。
方針：自由 Koszul 係数変更の全 Hom 写像と単位・積保存を使う。
規約：KST Lemma 3.6。使われ方：基底から共通表示図式への自然変換。 -/
def finiteOverlapExceptionalProductBaseMap (a : I → R) (i : I) (T : Finset I) :
    baseKoszulDGAlgebra R a ⟶ finiteOverlapExceptionalProductAlgebra R a i T :=
  Mon.Hom.mk' ((finiteOverlapExceptionalProductBaseDGFunctor R a i T).map .point .point)
    ((finiteOverlapExceptionalProductBaseDGFunctor R a i T).map_id .point)
    ((finiteOverlapExceptionalProductBaseDGFunctor R a i T).map_comp .point .point .point)

set_option maxHeartbeats 1000000 in
-- 局所化環への係数変更と Hom の各次数を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：基底から共通表示への射の像は標準外積係数変更。
方針：既存の自由 Koszul dg 関手の全次数の包含公式を使う。
規約：KST Lemma 3.6。使われ方：全有限重なりでの自然性の計算。 -/
theorem finiteOverlapExceptionalProductBaseMap_inclusion (a : I → R) (i : I)
    (T : Finset I) (q : ℤ) (z : (exteriorKoszulCochain (Finsupp.linearCombination R a)).X q) :
    exteriorCochainInclusion (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))) q
        (((finiteOverlapExceptionalProductBaseMap R a i T).hom.f q) z) =
      freeExteriorScalarMap (algebraMap R (FiniteOverlapRing R i T))
        (exteriorCochainInclusion (Finsupp.linearCombination R a) q z) :=
  freeKoszulScalarDGFunctor_inclusion (algebraMap R (FiniteOverlapRing R i T))
    a .point .point q z

end SerrePositivity.KST.DerivedBlowup
