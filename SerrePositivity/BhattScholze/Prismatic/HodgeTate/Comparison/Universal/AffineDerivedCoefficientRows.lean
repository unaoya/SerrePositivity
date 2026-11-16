module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoefficientRows
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule

/-!
# 元の標準導来係数増大と商射

## 概要
元のfull・剰余行の標準導来底変換から元の通常係数射への増大を指定する。

## 方針
元の標準加群増大と元の単一対象への係数射を合成し、同じ商射の正方形を保つ。

## 規約
環写像の通常の平坦性は仮定しない。

## 使われ方
元の指定被覆同型を、標準係数増大の完備延長と比較する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元のfull行の標準導来係数増大。 -/
def affineDerivedFullCoefficientMap (n : SimplexCategory) :
    ((boundedAboveDerivedBaseChange f.toRingHom).obj
      (boundedAboveDerivedSingleFunctor.obj ((affineFullBaseModules P hP r).obj n))).obj ⟶
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj ((affineFullBaseModules Q hQ r).obj n) :=
  (boundedAboveDerivedBaseChangeModuleAugmentation f.toRingHom).app _ ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
      ((affineFullAnyOrdinaryMap f hP hQ r).app n)

/-- 元の剰余行の標準導来係数増大。 -/
def affineDerivedReducedCoefficientMap (n : SimplexCategory) :
    ((boundedAboveDerivedBaseChange f.toRingHom).obj
      (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj ⟶
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj ((affineBaseModules Q hQ r).obj n) :=
  (boundedAboveDerivedBaseChangeModuleAugmentation f.toRingHom).app _ ≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
      ((affineBaseAnyOrdinaryCoefficientMap f hP hQ r).app n)

/-- 元のfull・剰余の標準導来係数増大は、同じ元の商射と可換。 -/
theorem affineDerivedCoefficientMap_projection (n : SimplexCategory) :
    ((boundedAboveDerivedBaseChange f.toRingHom).map
      (boundedAboveDerivedSingleFunctor.map ((affineFullBaseProjection P hP r).app n))).hom ≫
        affineDerivedReducedCoefficientMap f hP hQ r n =
    affineDerivedFullCoefficientMap f hP hQ r n ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
        ((affineFullBaseProjection Q hQ r).app n) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} B) 0
  let π := (affineFullBaseProjection P hP r).app n
  have hn : ((boundedAboveDerivedBaseChange f.toRingHom).map
      (boundedAboveDerivedSingleFunctor.map π)).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation f.toRingHom).app
          ((affineBaseModules P hP r).obj n) =
      (boundedAboveDerivedBaseChangeModuleAugmentation f.toRingHom).app
          ((affineFullBaseModules P hP r).obj n) ≫
        S.map ((ModuleCat.extendScalars f.toRingHom).map π) :=
    (boundedAboveDerivedBaseChangeModuleAugmentation f.toRingHom).naturality π
  simp only [affineDerivedReducedCoefficientMap, affineDerivedFullCoefficientMap]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    affineFullBaseProjection_ordinary, Functor.map_comp, Category.assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
