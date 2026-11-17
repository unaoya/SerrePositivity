module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.DerivedScalarConeRightLeg
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-!
# 元の完備化とスカラー錐の比較の右脚

## 概要
元の完備化・スカラー錐の比較は、同じ元の導来右脚を保つ。

## 方針
元の完備化単位の正方形、元の右脚の自然性、完備対象への射の一意性を使う。

## 規約
完備化比較を選び直さず、元のcompletionScalarConeIsoの法則を示す。

## 使われ方
二座標完備底変換の元の錐比較を、元の商射と照合する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R]

/-- 元の単位で定義した完備化・錐比較は、元の右脚を保つ。 -/
theorem completionScalarConeIso_rightLeg (a b : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (derivedComplexCompletionFunctor R a).map ((derivedScalarConeRightLeg R b).app X.obj) ≫
        (completionScalarConeIso R a b X).hom =
      (derivedScalarConeRightLeg R b).app ((derivedComplexCompletionFunctor R a).obj X.obj) := by
  let C := derivedComplexCompletionFunctor R a
  let T := derivedScalarConeFunctor R b
  let δ := derivedScalarConeRightLeg R b
  let u := (derivedComplexCompletionUnit R a).app X.obj
  have htarget := derivedScalarCone_isComplete R a b (C.obj X.obj)
    (derivedComplexCompletionFunctor_isComplete R a X.obj)
  apply derivedComplexCompletionHom_ext R a htarget
  have hu := (derivedComplexCompletionUnit R a).naturality (δ.app X.obj)
  simp only [Functor.id_map] at hu
  have hc : (derivedComplexCompletionUnit R a).app (T.obj X.obj) ≫
      (completionScalarConeIso R a b X).hom = T.map u :=
    completionScalarConeComparison_unit R a b X
  have hδ := δ.naturality u
  simp only [Functor.id_map] at hδ
  calc
    _ = δ.app X.obj ≫ (derivedComplexCompletionUnit R a).app (T.obj X.obj) ≫
        (completionScalarConeIso R a b X).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ (completionScalarConeIso R a b X).hom) hu.symm
    _ = δ.app X.obj ≫ T.map u := by rw [hc]
    _ = _ := hδ.symm

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
