module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BaseChangeHomologyUnit

/-!
# 通常係数拡大のホモロジー比較の純テンソル

## 概要
随伴で定めたホモロジー比較の、一と元の純テンソルでの値を記録する。

## 方針
元の加群随伴のhomEquivの評価式を使う。

## 規約
平坦性もホモロジー比較の同型性も仮定しない。

## 使われ方
元のHT写像の基底での値を、同じ係数拡大の単位に沿って比較する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元のホモロジー比較の一との純テンソルは、元の複体のホモロジー単位である。 -/
theorem complexBaseChangeHomologyComparison_one_tmul (f : R →+* S)
    (K : Complex R) (i : ℤ) (x : K.homology i) :
    complexBaseChangeHomologyComparison f K i ((1 : S) ⊗ₜ[R,f] x) =
      complexBaseChangeHomologyUnit f K i x := by
  have h := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (complexBaseChangeHomologyComparison f K i) x
  rw [complexBaseChangeHomologyComparison, Equiv.apply_symm_apply] at h
  exact h.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
