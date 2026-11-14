module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilyBase
import all SerrePositivity.BhattScholze.Perfectoidization.Construction.RootAdjunction

/-!
# 根付き変数族の基底の perfectoid 性

## 概要
根付き変数の実 p 完備化 H⁰ は perfectoid 係数上で perfectoid になる。
## 方針
既存 RootAdjunction の単項式完備化の古典的な補題を再利用する。
指数の p 倍の同型を有限台関数へ移し、実完備化と古典的完備化の比較を通す。
## 規約
BS 著者版 Proposition 7.10。零環を含み、変数の個数は任意。
## 使われ方
有限 T と S′ の完全基底 A_inf の構成。
-/

public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type v)

/-- 根付き変数族の指数の p 倍は加法同型。 -/
def rootFamilyExponentScale :
    (J →₀ _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p (Fact.out : p.Prime).pos) ≃+
      (J →₀ _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p (Fact.out : p.Prime).pos) :=
  Finsupp.mapRange.addEquiv (_root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentPrimeScaleEquiv p)

/-- 指数の同型の順方向は p 倍そのものである。 -/
theorem rootFamilyExponentScale_apply (x : J →₀ _root_.SerrePositivity.BhattScholze.Semiperfectoid.powerRootExponentMonoid p (Fact.out : p.Prime).pos) :
    rootFamilyExponentScale p J x = p • x := by
  ext j
  rfl

/-- 概要：根付き変数族の基底は整 perfectoid。
方針：既存の単項式完備化の perfectoid 性を比較同型で移す。
規約：BS 著者版 Proposition 7.10。係数環も変数族も非空とは仮定しない。
使われ方：有限 T を表示する perfectoid 環 R′。 -/
theorem rootFamilyBase_isIntegralPerfectoid (hR : IsIntegralPerfectoid R p) :
    IsIntegralPerfectoid (rootFamilyBase p R J) p := by
  have h := _root_.SerrePositivity.BhattScholze.Perfectoidization.Construction.monomialAdicCompletionPerfectoid p R hR
    (rootFamilyExponentScale p J) (rootFamilyExponentScale_apply p J)
  exact isIntegralPerfectoid_of_ringEquiv p (rootFamilyBaseAdicEquiv p R J hR).symm h

end SerrePositivity.BhattScholze.Semiperfectoid
