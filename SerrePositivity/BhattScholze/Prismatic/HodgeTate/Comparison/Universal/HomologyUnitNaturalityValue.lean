module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BaseChangeHomologyUnit

/-!
# 元の通常ホモロジー単位の自然性の純テンソルでの値

## 概要
元の複体の射への通常ホモロジー比較の自然性を、一と元の純テンソルで評価する。

## 方針
元の自然性の等式と元のテンソル関手の純テンソルの式を使う。

## 規約
係数拡大関手の完全性を仮定しない。

## 使われ方
元のηの実現の値を、同じ元の通常係数拡大の射へ渡す。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の通常ホモロジー比較の自然性は、一との純テンソルでも同じ射を保つ。 -/
theorem complexBaseChangeHomologyComparison_naturality_one_tmul (f : R →+* S)
    {K L : Complex R} (g : K ⟶ L) (i : ℤ) (x : K.homology i) :
    homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g) i
        (complexBaseChangeHomologyComparison f K i ((1 : S) ⊗ₜ[R,f] x)) =
      complexBaseChangeHomologyComparison f L i ((1 : S) ⊗ₜ[R,f] homologyMap g i x) := by
  have h := ConcreteCategory.congr_hom (complexBaseChangeHomologyComparison_naturality f g i)
    ((1 : S) ⊗ₜ[R,f] x)
  change complexBaseChangeHomologyComparison f L i
      ((ModuleCat.extendScalars f).map (homologyMap g i) ((1 : S) ⊗ₜ[R,f] x)) = _ at h
  rw [ModuleCat.ExtendScalars.map_tmul] at h
  exact h.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
