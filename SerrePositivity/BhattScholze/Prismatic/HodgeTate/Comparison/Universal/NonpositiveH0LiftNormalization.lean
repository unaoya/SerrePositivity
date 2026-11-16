module

public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom

/-!
# 元の非正次数対象のH⁰への増大の正規化

## 概要
元の標準増大の後にH⁰の線形写像を合成すると、指定された同じH⁰写像になる。

## 方針
標準増大の正規化と、単一対象の元のH⁰同型の自然性を使う。

## 規約
元の増大と元の単一対象の同型を選び直さない。

## 使われ方
二回完備底変換のH⁰同型が、同じ元の係数の単位を保つことを照合する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の非正次数増大の後のH⁰写像は、同じ元の指定された線形写像である。 -/
theorem nonpositiveAugmentation_postcomp_homology
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsLE 0] (M : ModuleCat.{u} R)
    (f : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X ⟶ M) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        (derivedNonpositiveAugmentation X ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map f) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).hom.app M = f := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  have hn := e.hom.naturality f
  change H.map (S.map f) ≫ e.hom.app M = e.hom.app (H.obj X) ≫ f at hn
  dsimp only [H, S, e] at hn
  have hu := derivedNonpositiveAugmentation_homology X
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, hu, Category.id_comp]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
