module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ScalarRestrictionTotal

/-!
# 元の S 線形係数拡大と指定積全複体の比較

## 概要
通常の係数拡大と指定積全複体の間の標準 S 線形比較を、元の加群随伴の単位で指定する。

## 方針
R 側で各行の係数拡大の単位を Tot に施し、係数制限の同型で移してから各次数で転置する。

## 規約
可逆性や K-flat 性はこの定義に仮定しない。任意に選んだ同型で標準射を置き換えない。

## 使われ方
BS 著者版 Lemma 4.22 の、指定 S 線形底変換模型の元の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 通常の複体の係数拡大の元の単位。 -/
def complexBaseChangeUnit (f : R →+* S) (K : Complex R) :
    K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj (baseChange f K) where
  f q := (ModuleCat.extendRestrictScalarsAdj f).unit.app (K.X q)
  comm' i j _ := ((ModuleCat.extendRestrictScalarsAdj f).unit.naturality (K.d i j)).symm

/-- 各項の元の単位は、複体の鎖写像について自然である。 -/
@[reassoc] theorem complexBaseChangeUnit_naturality (f : R →+* S)
    {K M : Complex R} (g : K ⟶ M) :
    g ≫ complexBaseChangeUnit f M = complexBaseChangeUnit f K ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map g) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact (ModuleCat.extendRestrictScalarsAdj f).unit.naturality (g.f q)

/-- 各行の元の単位からなる、元の横図式の射。 -/
def rowsBaseChangeUnit (f : R →+* S) (K : CochainComplex (Complex R) ℕ) :
    K ⟶ restrictedRows f
      ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℕ)).obj K) where
  f n := complexBaseChangeUnit f (K.X n)
  comm' i j _ := (complexBaseChangeUnit_naturality f (K.d i j)).symm

/-- 元の単位と行射影で指定する、通常の底変換–Tot 比較の R 線形転置。 -/
def baseChangeTotalTranspose (f : R →+* S) (K : CochainComplex (Complex R) ℕ) :
    total K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      (total ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℕ)).obj K)) :=
  (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (rowsBaseChangeUnit f K) ≫
    (restrictionTotalIso f _).inv

/-- 同じ単位を元の加群随伴で転置した、標準 S 線形の比較鎖写像。 -/
def baseChangeTotalComparison (f : R →+* S) (K : CochainComplex (Complex R) ℕ) :
    baseChange f (total K) ⟶
      total ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℕ)).obj K) where
  f q := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
    ((baseChangeTotalTranspose f K).f q)
  comm' i j hij := by
    exact ((ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right_square
      ((total K).d i j) ((baseChangeTotalTranspose f K).f j)
      ((baseChangeTotalTranspose f K).f i)
      ((total ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℕ)).obj K)).d i j)
      ((baseChangeTotalTranspose f K).comm i j).symm).symm

/-- 単位との合成は、元の行の単位を Tot に施した射そのものである。 -/
@[reassoc] theorem complexBaseChangeUnit_comp_totalComparison
    (f : R →+* S) (K : CochainComplex (Complex R) ℕ) :
    complexBaseChangeUnit f (total K) ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (baseChangeTotalComparison f K) = baseChangeTotalTranspose f K := by
  apply HomologicalComplex.Hom.ext
  funext q
  change (ModuleCat.extendRestrictScalarsAdj f).unit.app ((total K).X q) ≫
    (ModuleCat.restrictScalars f).map
      (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
        ((baseChangeTotalTranspose f K).f q)) = _
  exact ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).apply_symm_apply _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
