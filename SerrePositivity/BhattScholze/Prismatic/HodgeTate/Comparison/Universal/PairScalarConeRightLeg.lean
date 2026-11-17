module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PairScalarConeCompatibility
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BoundedScalarConeRightLeg
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CompletionScalarConeRightLeg
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PairScalarConeCompatibility

/-!
# 元の二座標完備底変換の錐比較の右脚

## 概要
元の二座標完備底変換とスカラー錐の指定比較は、元の右脚を保つ。

## 方針
元の導来底変換と二回の完備化で右脚の式を順に合成する。

## 規約
既存のpairCompletedScalarConeIsoの法則であり、比較を選び直さない。

## 使われ方
元のfull envelopeから生成元による剰余への商射の比較に使う。
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

/-- 元の二座標完備導来底変換の錐比較は、同じ右脚を保つ。 -/
theorem pairCompletedScalarConeIso_rightLeg (φ : R →+* B) (a : R) (c d : B)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedCompletionFunctor B c ⋙
      boundedAboveDerivedCompletionFunctor B d).map (boundedScalarConeRightLeg a X)).hom ≫
        (pairCompletedScalarConeIso φ a c d X).hom =
      (derivedScalarConeRightLeg B (φ a)).app (pairCompletedBaseChange φ c d X).obj := by
  let Y := (boundedAboveDerivedBaseChange φ).obj X
  let C := derivedComplexCompletionFunctor B c
  let D := derivedComplexCompletionFunctor B d
  have hb := boundedAboveDerivedBaseChangeScalarConeIso_rightLeg φ a X
  have hc := completionScalarConeIso_rightLeg B c (φ a) Y
  have hd := completionScalarConeIso_rightLeg B d (φ a)
    ((boundedAboveDerivedCompletionFunctor B c).obj Y)
  change D.map (C.map (((boundedAboveDerivedBaseChange φ).map
    (boundedScalarConeRightLeg a X)).hom)) ≫ _ = _
  simp only [pairCompletedScalarConeIso, Iso.trans_hom, Functor.mapIso_hom]
  change D.map (C.map (((boundedAboveDerivedBaseChange φ).map
    (boundedScalarConeRightLeg a X)).hom)) ≫
      D.map (C.map (boundedAboveDerivedBaseChangeScalarConeIso φ a X).hom) ≫
      D.map (completionScalarConeIso B c (φ a) Y).hom ≫
      (completionScalarConeIso B d (φ a)
        ((boundedAboveDerivedCompletionFunctor B c).obj Y)).hom = _
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, hb]
  erw [hc, hd]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
