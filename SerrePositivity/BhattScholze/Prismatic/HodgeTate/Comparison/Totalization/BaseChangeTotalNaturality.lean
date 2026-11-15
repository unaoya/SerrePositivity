module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComparison

/-!
# 標準 S 線形 Tot 比較の自然性

## 概要
各行の係数拡大の単位から指定した比較は、元の厳密な図式の鎖写像について自然である。

## 方針
係数制限の比較を自然同型にまとめ、その逆の自然性と元の随伴の転置を使う。

## 規約
標準単位と行射影を保つ。

## 使われ方
BS 著者版 Lemma 4.22 の標準 S 線形の脚の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 通常の係数拡大を内部複体と横図式へ施す、元の関手。 -/
abbrev baseChangeRowsFunctor (f : R →+* S) :
    CochainComplex (Complex R) ℕ ⥤ CochainComplex (Complex S) ℕ :=
  (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ))

/-- 元の指定成分の係数制限比較を自然同型としてまとめる。 -/
def restrictionTotalNatIso (f : R →+* S) :
    cochainProductTotalizationFunctor (ModuleCat.{u} S) ⋙
        (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ) ≅
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ)) ⋙
        cochainProductTotalizationFunctor (ModuleCat.{u} R) :=
  NatIso.ofComponents (restrictionTotalIso f)
    (fun g => restrictionTotalComparison_naturality f g)

/-- 行ごとの係数拡大の元の単位は、横図式の射についても自然である。 -/
@[reassoc] theorem rowsBaseChangeUnit_naturality (f : R →+* S)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    g ≫ rowsBaseChangeUnit f M = rowsBaseChangeUnit f K ≫
      ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
        (.up ℕ)).map ((baseChangeRowsFunctor f).map g)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact complexBaseChangeUnit_naturality f (g.f n)

/-- 元の単位と指定行射影からなる転置は、図式の射について自然である。 -/
@[reassoc] theorem baseChangeTotalTranspose_naturality (f : R →+* S)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g ≫ baseChangeTotalTranspose f M =
      baseChangeTotalTranspose f K ≫ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map ((baseChangeRowsFunctor f).map g)) := by
  dsimp only [baseChangeTotalTranspose]
  rw [← Category.assoc, ← Functor.map_comp, rowsBaseChangeUnit_naturality, Functor.map_comp,
    Category.assoc]
  have hn : (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
          (.up ℕ)).map ((baseChangeRowsFunctor f).map g)) ≫
      (restrictionTotalIso f ((baseChangeRowsFunctor f).obj M)).inv =
    (restrictionTotalIso f ((baseChangeRowsFunctor f).obj K)).inv ≫
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map ((baseChangeRowsFunctor f).map g)) :=
    (restrictionTotalNatIso f).inv.naturality ((baseChangeRowsFunctor f).map g)
  simpa only [Category.assoc] using congrArg
    (fun t => (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (rowsBaseChangeUnit f K) ≫ t) hn

/-- 元の S 線形係数拡大の比較は、厳密な横図式の射について自然である。 -/
@[reassoc] theorem baseChangeTotalComparison_naturality (f : R →+* S)
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).map
        ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g) ≫ baseChangeTotalComparison f M =
      baseChangeTotalComparison f K ≫ (cochainProductTotalizationFunctor (ModuleCat.{u} S)).map
        ((baseChangeRowsFunctor f).map g) := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hc := congrArg (fun h => h.f q) (baseChangeTotalTranspose_naturality f g)
  simp only [HomologicalComplex.comp_f] at hc
  exact (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right_square
    (((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g).f q)
    ((baseChangeTotalTranspose f M).f q) ((baseChangeTotalTranspose f K).f q)
    (((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map ((baseChangeRowsFunctor f).map g)).f q) hc

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
