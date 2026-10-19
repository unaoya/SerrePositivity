module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraDiagram
public import SerrePositivity.KST.DerivedBlowup.ChartDGFunctors

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の有限重なりでの例外因子と共通 Ko(A;a) 表示の同型。
方針：自己逆 Koszul 基底変換を共通基底環へ制限し、モノイド対象の同型として束ねる。
規約：単なる underlying 複体の比較ではなく、単位と積も保つ。
使われ方：例外因子の係数図式を共通 Koszul 表示へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：有限重なりの係数環上の全 a_j による共通 Koszul dg 模型。
方針：基底係数の像を微分とする全生成元の外積模型を基底制限する。
規約：KST Lemma 3.6。使われ方：Ko(A;a) の局所多項式・局所化表示。 -/
abbrev FiniteOverlapExceptionalProductObject (a : I → R) (i : I) (T : Finset I) :=
  DGRestriction (algebraMap R (FiniteOverlapRing R i T))
    (ExteriorKoszulObject (Finsupp.linearCombination (FiniteOverlapRing R i T)
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))))

/-- 概要：共通 Koszul 表示を共通基底環上の dg 代数にする。
方針：基底制限した一対象 dg 圏の自己 Hom を使う。
規約：KST Lemma 3.6。使われ方：比較図式の各頂点。 -/
def finiteOverlapExceptionalProductAlgebra (a : I → R) (i : I) (T : Finset I) :
    Mon (Complex R) := dgEndMonoid R (FiniteOverlapExceptionalProductObject R a i T) .point

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環と基底環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子から共通 Koszul 表示への基底制限された dg 比較。
方針：既存の自己逆基底変換 dg 関手を構造射に沿って制限する。
規約：KST Lemma 3.6。使われ方：係数代数同型の単位・積保存。 -/
def finiteOverlapExceptionalProductDGFunctor (a : I → R) (i : I) (T : Finset I) :
    DGFunctor R (FiniteOverlapExceptionalBaseObject R a i T)
      (FiniteOverlapExceptionalProductObject R a i T) :=
  restrictDGFunctor (algebraMap R (FiniteOverlapRing R i T))
    (exceptionalExteriorDGFunctor (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i)

set_option maxHeartbeats 2000000 in
-- 局所化環と基底環での Koszul 複体同型と単位・積を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子と共通 Koszul 表示の指定 dg 代数同型。
方針：指定 cochain 同型を係数制限し、dg 比較の単位・積保存で束ねる。
規約：KST Lemma 3.6、原典の局所同定を明示基底変換で再構成する。
使われ方：全有限重なり図式の比較の成分。 -/
def finiteOverlapExceptionalProductIso (a : I → R) (i : I) (T : Finset I) :
    finiteOverlapExceptionalDGAlgebra R a i T ≅ finiteOverlapExceptionalProductAlgebra R a i T :=
  Mon.mkIso ((restriction (algebraMap R (FiniteOverlapRing R i T))).mapIso
    (exceptionalExteriorCochainIso (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i))
    ((finiteOverlapExceptionalProductDGFunctor R a i T).map_id .point)
    ((finiteOverlapExceptionalProductDGFunctor R a i T).map_comp .point .point .point)

/-- 概要：共通 Koszul 表示への代数同型の順射は指定 dg 比較の Hom 写像。
方針：モノイド同型の定義を読む。
規約：KST Lemma 3.6。使われ方：図式の比較を全次数の元で計算する。 -/
theorem finiteOverlapExceptionalProductIso_hom (a : I → R) (i : I) (T : Finset I) :
    (finiteOverlapExceptionalProductIso R a i T).hom.hom =
      (finiteOverlapExceptionalProductDGFunctor R a i T).map .point .point := rfl

end SerrePositivity.KST.DerivedBlowup
