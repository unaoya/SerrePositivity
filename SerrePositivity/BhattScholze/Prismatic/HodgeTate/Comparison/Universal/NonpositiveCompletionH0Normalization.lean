module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NonpositiveH0LiftNormalization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 非正次数増大の完備化の元の単位

## 概要
指定したH⁰写像を非正次数増大で実現して完備化したときの単位を計算する。

## 方針
実完備化単位の自然性と元のH⁰の正規化を合成する。

## 規約
射をH⁰から選び直さず、指定された元の増大を用いる。

## 使われ方
元の二座標完備導来底変換のH⁰同型を同じ係数単位で正規化する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の完備化単位の後の増大の像は、元の指定されたH⁰写像を保つ。 -/
theorem nonpositiveCompletion_homology_unit (a : R)
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] (M : ModuleCat.{u} R)
    (f : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X ⟶ M) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionUnit R a).app X) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionFunctor R a).map
          (derivedNonpositiveAugmentation X ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map f)) =
      f ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app M ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
          ((derivedComplexCompletionUnit R a).app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let g := derivedNonpositiveAugmentation X ≫ S.map f
  have hn := (derivedComplexCompletionUnit R a).naturality g
  simp only [Functor.id_map] at hn
  have hf := nonpositiveAugmentation_postcomp_homology X M f
  have hf' : H.map g = f ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app M := by
    apply (cancel_mono
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app M)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id, H, S, g] using hf
  rw [← Functor.map_comp, ← hn, Functor.map_comp, hf', Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
