module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineFormalCoverAugmentation

/-!
# 元の通常係数拡大のホモロジー単位

## 概要
平坦性を仮定せず、元の複体の随伴単位からホモロジーの係数拡大の射を作る。

## 方針
完全な係数制限のホモロジー同型で単位を運び、元の加群随伴で転置する。

## 規約
この射を一般に同型とは主張しない。元の複体と元の鎖写像への自然性を保持する。

## 使われ方
元のηの零次・一次の実現の等式を、通常係数拡大後の同じ射へ移す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の係数制限の、整数次数の標準ホモロジー自然同型。 -/
def restrictCochainHomologyIso (f : R →+* S) (i : ℤ) :
    (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ) ⋙
        homologyFunctor (ModuleCat.{u} R) (.up ℤ) i ≅
      homologyFunctor (ModuleCat.{u} S) (.up ℤ) i ⋙ ModuleCat.restrictScalars f :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso (ModuleCat.restrictScalars f))
    (fun g => ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ _ i).map g) (ModuleCat.restrictScalars f))

/-- 元の複体の単位を同じ整数次数のホモロジーへ移した射。 -/
def complexBaseChangeHomologyUnit (f : R →+* S) (K : Complex R) (i : ℤ) :
    K.homology i ⟶ (ModuleCat.restrictScalars f).obj ((baseChange f K).homology i) :=
  homologyMap (complexBaseChangeUnit f K) i ≫
    ((restrictCochainHomologyIso f i).app (baseChange f K)).hom

/-- 元のホモロジー単位は、元の任意の鎖写像について自然。 -/
@[reassoc] theorem complexBaseChangeHomologyUnit_naturality (f : R →+* S)
    {K L : Complex R} (g : K ⟶ L) (i : ℤ) :
    homologyMap g i ≫ complexBaseChangeHomologyUnit f L i =
      complexBaseChangeHomologyUnit f K i ≫ (ModuleCat.restrictScalars f).map
        (homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g) i) := by
  have hn := congrArg (fun h => homologyMap h i) (complexBaseChangeUnit_naturality f g)
  simp only [homologyMap_comp] at hn
  have hu := (restrictCochainHomologyIso f i).hom.naturality
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g)
  dsimp only [complexBaseChangeHomologyUnit]
  rw [← Category.assoc, hn, Category.assoc]
  exact congrArg (fun k => homologyMap (complexBaseChangeUnit f K) i ≫ k) hu

/-- 元のホモロジー単位を元の加群随伴で転置した係数拡大の射。 -/
def complexBaseChangeHomologyComparison (f : R →+* S) (K : Complex R) (i : ℤ) :
    (ModuleCat.extendScalars f).obj (K.homology i) ⟶ (baseChange f K).homology i :=
  ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
    (complexBaseChangeHomologyUnit f K i)

/-- 元のホモロジーの通常係数拡大の射も、同じ元の鎖写像について自然。 -/
@[reassoc] theorem complexBaseChangeHomologyComparison_naturality (f : R →+* S)
    {K L : Complex R} (g : K ⟶ L) (i : ℤ) :
    (ModuleCat.extendScalars f).map (homologyMap g i) ≫
        complexBaseChangeHomologyComparison f L i =
      complexBaseChangeHomologyComparison f K i ≫
        homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g) i := by
  exact (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right_square
    (homologyMap g i) (complexBaseChangeHomologyUnit f L i)
    (complexBaseChangeHomologyUnit f K i)
    (homologyMap (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g) i)
    (complexBaseChangeHomologyUnit_naturality f g i)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
