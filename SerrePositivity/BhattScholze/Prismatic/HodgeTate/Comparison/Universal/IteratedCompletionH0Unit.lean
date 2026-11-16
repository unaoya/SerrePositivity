module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.NonpositiveCompletionH0Normalization

/-!
# 元の二回完備化のH⁰の単位

## 概要
二つの指定されたH⁰写像を用いた二回完備化の計算が元の単位を保つことを示す。

## 方針
各完備化単位の自然性を、同じ標準単一対象のH⁰同型で正規化する。

## 規約
完備化や単位を選び直さず、仮定した指定された射の等式だけを用いる。

## 使われ方
既存の二座標完備テンソル積の同型を係数の単位と照合する。
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

/-- 二回の元の完備化のH⁰計算は、両方の元の単位で正規化される。 -/
theorem iteratedCompletionH0_unit (a b : R)
    (X : DerivedCategory (ModuleCat.{u} R)) (M N W : ModuleCat.{u} R)
    (f : X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
    (g : (derivedComplexCompletionFunctor R a).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)
    (k : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
        ((derivedComplexCompletionFunctor R b).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) ⟶ W) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
    let C := derivedComplexCompletionFunctor R a
    let D := derivedComplexCompletionFunctor R b
    H.map ((derivedComplexCompletionUnit R a).app X ≫
      (derivedComplexCompletionUnit R b).app (C.obj X)) ≫
      (H.map (D.map (C.map f)) ≫ H.map (D.map g) ≫ k) =
      H.map f ≫ H.map ((derivedComplexCompletionUnit R a).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≫
        H.map g ≫ H.map ((derivedComplexCompletionUnit R b).app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≫ k := by
  dsimp only
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let C := derivedComplexCompletionFunctor R a
  let D := derivedComplexCompletionFunctor R b
  let SM := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  let SN := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N
  have ha : f ≫ (derivedComplexCompletionUnit R a).app SM =
      (derivedComplexCompletionUnit R a).app X ≫ C.map f := by
    exact (derivedComplexCompletionUnit R a).naturality f
  have hb : C.map f ≫ (derivedComplexCompletionUnit R b).app (C.obj SM) =
      (derivedComplexCompletionUnit R b).app (C.obj X) ≫ D.map (C.map f) := by
    exact (derivedComplexCompletionUnit R b).naturality (C.map f)
  have hg : g ≫ (derivedComplexCompletionUnit R b).app SN =
      (derivedComplexCompletionUnit R b).app (C.obj SM) ≫ D.map g := by
    exact (derivedComplexCompletionUnit R b).naturality g
  have ht : ((derivedComplexCompletionUnit R a).app X ≫
      (derivedComplexCompletionUnit R b).app (C.obj X)) ≫
      D.map (C.map f) ≫ D.map g =
      f ≫ (derivedComplexCompletionUnit R a).app SM ≫ g ≫
        (derivedComplexCompletionUnit R b).app SN := by
    calc
      _ = (derivedComplexCompletionUnit R a).app X ≫
          C.map f ≫ (derivedComplexCompletionUnit R b).app (C.obj SM) ≫ D.map g := by
        simpa only [Category.assoc] using congrArg
          (fun q => (derivedComplexCompletionUnit R a).app X ≫ q ≫ D.map g) hb.symm
      _ = f ≫ (derivedComplexCompletionUnit R a).app SM ≫
          (derivedComplexCompletionUnit R b).app (C.obj SM) ≫ D.map g := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ (derivedComplexCompletionUnit R b).app (C.obj SM) ≫ D.map g) ha.symm
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun q => f ≫ (derivedComplexCompletionUnit R a).app SM ≫ q) hg.symm
  simpa only [Functor.map_comp, Category.assoc, H, C, D, SM, SN, Functor.id_obj] using
    congrArg (fun q => H.map q ≫ k) ht

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
