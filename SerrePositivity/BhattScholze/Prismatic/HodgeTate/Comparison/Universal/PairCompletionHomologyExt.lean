module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NonpositiveH0LiftNormalization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 元の二回完備化から離散完備対象への射の外延性

## 概要
非正次数の対象の二回完備化からの射は、元の二つの単位上のH⁰写像で決まる。

## 方針
二つの元の単位による外延性と非正次数から離散対象へのH⁰の忠実性を使う。

## 規約
通常の環写像の平坦性や、完備化の完全性は要求しない。

## 使われ方
元のfull envelopeの指定同型と、元の係数の増大の完備延長を照合する。
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

/-- 元の二つの単位上でH⁰の正規化が同じなら、二つの元の射は等しい。 -/
theorem pairCompletionHomology_ext (a b : R)
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] (M : ModuleCat.{u} R)
    (ha : IsComplete R a ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))
    (hb : IsComplete R b ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))
    {f g : (derivedComplexCompletionFunctor R b).obj
      ((derivedComplexCompletionFunctor R a).obj X) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M}
    (h : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        (((derivedComplexCompletionUnit R a).app X ≫
          (derivedComplexCompletionUnit R b).app
            ((derivedComplexCompletionFunctor R a).obj X)) ≫ f) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app M =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        (((derivedComplexCompletionUnit R a).app X ≫
          (derivedComplexCompletionUnit R b).app
            ((derivedComplexCompletionFunctor R a).obj X)) ≫ g) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app M) :
    f = g := by
  apply derivedComplexCompletionHom_ext R b hb
  apply derivedComplexCompletionHom_ext R a ha
  dsimp only [Functor.id_obj]
  apply (derivedNonpositiveHomologyZero_map_bijective).injective
  apply (cancel_mono
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app M)).mp
  simpa only [Category.assoc] using h

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
