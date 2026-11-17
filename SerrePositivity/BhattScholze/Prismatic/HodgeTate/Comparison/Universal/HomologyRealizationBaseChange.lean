module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BaseChangeHomologyUnit

/-!
# 元のホモロジー実現の係数制限と通常係数拡大

## 概要
元の鎖写像が指定されたホモロジー写像を実現する等式は、元の制限同型と通常拡大の単位の図式へ移る。

## 方針
係数制限の標準ホモロジー同型と、元の通常拡大のホモロジー単位の自然性を使う。

## 規約
鎖写像自体の係数変更についての自然性は入力にしない。

## 使われ方
元のηのH₀・H₁の実現の等式を、元の被覆上の正方形へ渡す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の実現の等式は、元の完全な係数制限のホモロジー同型で保たれる。 -/
theorem restrictedHomology_realization (f : R →+* S) {F K : Complex S}
    (η : F ⟶ K) (i : ℤ) {M : ModuleCat.{u} S}
    (a : M ⟶ F.homology i) (b : M ⟶ K.homology i)
    (h : a ≫ homologyMap η i = b) :
    (ModuleCat.restrictScalars f).map a ≫
        ((restrictCochainHomologyIso f i).app F).inv ≫
        homologyMap (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map η) i =
      (ModuleCat.restrictScalars f).map b ≫ ((restrictCochainHomologyIso f i).app K).inv := by
  have hn := (restrictCochainHomologyIso f i).inv.naturality η
  change (ModuleCat.restrictScalars f).map (homologyMap η i) ≫
      ((restrictCochainHomologyIso f i).app K).inv =
    ((restrictCochainHomologyIso f i).app F).inv ≫
      homologyMap (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map η) i at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp, h]

/-- 元の通常ホモロジー単位の転置も、同じ元の実現の等式を保つ。 -/
theorem ordinaryHomology_realization (f : R →+* S) {F K : Complex R}
    (η : F ⟶ K) (i : ℤ) {M : ModuleCat.{u} R}
    (a : M ⟶ F.homology i) (b : M ⟶ K.homology i)
    (h : a ≫ homologyMap η i = b) :
    (ModuleCat.extendScalars f).map a ≫ complexBaseChangeHomologyComparison f F i ≫
        homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map η) i =
      (ModuleCat.extendScalars f).map b ≫ complexBaseChangeHomologyComparison f K i := by
  rw [← complexBaseChangeHomologyComparison_naturality, ← Category.assoc,
    ← Functor.map_comp, h]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
