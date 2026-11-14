module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDColumnCompletedBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamDerivedSpan
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDColumnCompletedBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PDDeRham.PDDeRhamDerivedSpan

/-!
# 分冪 de Rham の総複体と第 0 行の完備導来底変換

## 概要
第 0 列の自由模型で計算した底変換を、総複体と第 0 行へ移す。

## 方針
総複体から出る二つの射影を有界導来圏で反転し、導来底変換と完備化を施す。

## 規約
両基底は p 正則。比較には実際の射影を使う。

## 使われ方
BS 著者版 Theorem 6.4 の Witt の係数変更の有限分冪模型。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p r : ℕ) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable (hA : Function.Injective (fun x : A => (p : A) * x))
variable (hB : Function.Injective (fun x : B => (p : B) * x))

local notation "F" => derivedComplexCompletionFunctor B (p : B)
local notation "L" => boundedAboveDerivedBaseChange (algebraMap A B) ⋙
  DerivedCategory.Minus.ι (C := ModuleCat B)

/-- 総複体の完備導来底変換を、第 0 列への射影とその自由模型で計算する。 -/
def pdDeRhamTotalCompletedBaseChangeIso :
    (F).obj ((L).obj (pdDeRhamTotalDerived p A r)) ≅
      (pdDeRhamTotalDerived p B r).obj := by
  let eA : pdDeRhamTotalDerived p A r ≅ pdCompletedColumnZeroDerived p A r :=
    ObjectProperty.isoMk _ (pdDeRhamDerivedColumnIso p A r)
  exact (F).mapIso ((L).mapIso eA) ≪≫
    pdColumnZeroCompletedBaseChangeIso p r A B hA hB ≪≫
    (pdDeRhamDerivedColumnIso p B r).symm

/-- 第 0 行の完備導来底変換を、総複体の二射影と第 0 列の自由模型で計算する。 -/
def pdDeRhamRowCompletedBaseChangeIso :
    (F).obj ((L).obj (pdDeRhamRowDerived p A r)) ≅
      (pdDeRhamRowDerived p B r).obj := by
  let eA : pdDeRhamRowDerived p A r ≅ pdCompletedColumnZeroDerived p A r :=
    ObjectProperty.isoMk _ (pdDeRhamDerivedColumnRowIso p A r).symm
  exact (F).mapIso ((L).mapIso eA) ≪≫
    pdColumnZeroCompletedBaseChangeIso p r A B hA hB ≪≫
    pdDeRhamDerivedColumnRowIso p B r

end SerrePositivity.BhattScholze.Prismatic
