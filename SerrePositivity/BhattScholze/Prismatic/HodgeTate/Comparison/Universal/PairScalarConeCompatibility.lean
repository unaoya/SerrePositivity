module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoverTerms
public import SerrePositivity.HomologicalAlgebra.DerivedScalarConeBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-!
# 元の二座標完備底変換とスカラー錐

## 概要
元の上に有界な導来対象の二座標完備底変換は、元のスカラー錐と可換となる。

## 方針
元の導来底変換の錐比較と、各完備化の標準単位を保つ錐比較を合成する。

## 規約
環写像の平坦性やスカラーの正則性を追加しない。上に有界なのは行の対象である。

## 使われ方
元の full envelope の項の比較から、生成元による元の剰余行の比較へ進む。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B]

/-- 元の二座標完備底変換は、元のスカラー錐をそのスカラーの像の錐へ移す。 -/
def pairCompletedScalarConeIso (φ : R →+* B) (a : R) (c d : B)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (pairCompletedBaseChange φ c d ((boundedAboveDerivedScalarCone R a).obj X)).obj ≅
      (derivedScalarConeFunctor B (φ a)).obj (pairCompletedBaseChange φ c d X).obj := by
  let Y := (boundedAboveDerivedBaseChange φ).obj X
  let e : (boundedAboveDerivedBaseChange φ).obj ((boundedAboveDerivedScalarCone R a).obj X) ≅
      (boundedAboveDerivedScalarCone B (φ a)).obj Y :=
    ObjectProperty.isoMk _ (boundedAboveDerivedBaseChangeScalarConeIso φ a X)
  exact DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedCompletionFunctor B d).mapIso
        ((boundedAboveDerivedCompletionFunctor B c).mapIso e)) ≪≫
    (derivedComplexCompletionFunctor B d).mapIso (completionScalarConeIso B c (φ a) Y) ≪≫
    completionScalarConeIso B d (φ a) ((boundedAboveDerivedCompletionFunctor B c).obj Y)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
