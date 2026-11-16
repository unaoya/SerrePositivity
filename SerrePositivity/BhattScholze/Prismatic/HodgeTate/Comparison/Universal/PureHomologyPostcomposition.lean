module

public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# 元の純ホモロジー同型の後の線形射

## 概要
元の正規化された純ホモロジー同型の後の線形射は、同じホモロジー写像を誘導する。

## 方針
元の単一対象のホモロジー同型の自然性と正規化を合成する。

## 規約
正規化された指定同型の選択を変えない。

## 使われ方
元のfull envelopeの完備導来底変換同型を元のH⁰同型で計算する。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 純ホモロジー同型と指定された線形射の合成は、その同じ線形射を誘導する。 -/
theorem normalizedPureHomologyIso_postcomp (i : ℤ)
    (X : DerivedCategory (ModuleCat.{u} R)) [X.IsGE i] [X.IsLE i]
    (M : ModuleCat.{u} R)
    (f : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X ⟶ M) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
        ((normalizedPureHomologyIso X i).hom ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) i).map f) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).hom.app M = f := by
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).hom.naturality f
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) i).map f) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).hom.app M =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) i).hom.app _ ≫ f at hn
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    normalizedPureHomologyIso_homology, Category.id_comp]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
