module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.HomologyUnitPureTensor

/-!
# 元の随伴単位の正方形からのホモロジー評価

## 概要
通常係数拡大の後の鎖写像を、一と元の純テンソルのホモロジー類で評価する。

## 方針
元のホモロジー単位と、完全な係数制限の自然同型を使う。

## 規約
平坦性も任意のホモロジー同型の選択も入力にしない。

## 使われ方
元のsingle行の通常Tot比較の単位の正方形を、同じ元のコホモロジー類へ戻す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
open scoped TensorProduct ChangeOfRings
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の随伴単位の正方形は、元のホモロジー単位の同じ正方形を与える。 -/
theorem complexBaseChangeHomologyUnit_comp (f : R →+* S) (K : Complex R) (L : Complex S)
    (g : baseChange f K ⟶ L)
    (h : K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj L)
    (hu : complexBaseChangeUnit f K ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g = h) (i : ℤ) :
    complexBaseChangeHomologyUnit f K i ≫
        (ModuleCat.restrictScalars f).map (homologyMap g i) =
      homologyMap h i ≫ ((restrictCochainHomologyIso f i).app L).hom := by
  have hn := (restrictCochainHomologyIso f i).hom.naturality g
  change homologyMap (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g) i ≫
      ((restrictCochainHomologyIso f i).app L).hom =
    ((restrictCochainHomologyIso f i).app (baseChange f K)).hom ≫
      (ModuleCat.restrictScalars f).map (homologyMap g i) at hn
  dsimp only [complexBaseChangeHomologyUnit]
  rw [Category.assoc, ← hn,
    ← Category.assoc, ← homologyMap_comp, hu]

/-- 同じ正方形は、元のホモロジー比較の一との純テンソル上の値を指定する。 -/
theorem complexBaseChangeHomologyComparison_one_tmul_comp (f : R →+* S)
    (K : Complex R) (L : Complex S) (g : baseChange f K ⟶ L)
    (h : K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj L)
    (hu : complexBaseChangeUnit f K ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g = h)
    (i : ℤ) (x : K.homology i) :
    homologyMap g i (complexBaseChangeHomologyComparison f K i ((1 : S) ⊗ₜ[R,f] x)) =
      ((restrictCochainHomologyIso f i).app L).hom (homologyMap h i x) := by
  rw [complexBaseChangeHomologyComparison_one_tmul]
  exact ConcreteCategory.congr_hom (complexBaseChangeHomologyUnit_comp f K L g h hu i) x

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
