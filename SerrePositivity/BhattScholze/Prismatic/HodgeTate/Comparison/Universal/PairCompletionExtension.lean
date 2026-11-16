module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-!
# 元の二回完備化単位に沿う指定された射の延長

## 概要
二座標について完備な終域への射を、二つの元の完備化単位に沿って延長する。

## 方針
既存の実完備化のHom同値を、元の順序で二回適用する。

## 規約
延長の定義は元の射と元の完備化単位だけを使う。

## 使われ方
元のfull envelopeと剰余行の指定比較を、同じ元の係数増大から特徴づける。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

/-- 元の二つの完備化単位に沿う同じ指定された射の延長。 -/
def pairCompletionExtension (a b : R) (X Y : DerivedCategory (ModuleCat.{u} R))
    (ha : IsComplete R a Y) (hb : IsComplete R b Y) (f : X ⟶ Y) :
    (derivedComplexCompletionFunctor R b).obj ((derivedComplexCompletionFunctor R a).obj X) ⟶ Y :=
  (derivedComplexCompletionHomEquiv R b ((derivedComplexCompletionFunctor R a).obj X) Y hb).symm
    ((derivedComplexCompletionHomEquiv R a X Y ha).symm f)

/-- 元の延長は元の二つの単位上で同じ元の射になる。 -/
theorem pairCompletionExtension_unit (a b : R) (X Y : DerivedCategory (ModuleCat.{u} R))
    (ha : IsComplete R a Y) (hb : IsComplete R b Y) (f : X ⟶ Y) :
    ((derivedComplexCompletionUnit R a).app X ≫
      (derivedComplexCompletionUnit R b).app ((derivedComplexCompletionFunctor R a).obj X)) ≫
      pairCompletionExtension a b X Y ha hb f = f := by
  have hb' := (derivedComplexCompletionHomEquiv R b
    ((derivedComplexCompletionFunctor R a).obj X) Y hb).apply_symm_apply
      ((derivedComplexCompletionHomEquiv R a X Y ha).symm f)
  change (derivedComplexCompletionUnit R b).app _ ≫
    pairCompletionExtension a b X Y ha hb f = _ at hb'
  have ha' := (derivedComplexCompletionHomEquiv R a X Y ha).apply_symm_apply f
  change (derivedComplexCompletionUnit R a).app X ≫ _ = f at ha'
  rw [Category.assoc, hb']
  exact ha'

/-- 元の二つの単位上で一致する延長は等しい。 -/
theorem pairCompletionExtension_ext (a b : R) (X Y : DerivedCategory (ModuleCat.{u} R))
    (ha : IsComplete R a Y) (hb : IsComplete R b Y)
    {f g : (derivedComplexCompletionFunctor R b).obj ((derivedComplexCompletionFunctor R a).obj X) ⟶ Y}
    (h : ((derivedComplexCompletionUnit R a).app X ≫
        (derivedComplexCompletionUnit R b).app ((derivedComplexCompletionFunctor R a).obj X)) ≫ f =
      ((derivedComplexCompletionUnit R a).app X ≫
        (derivedComplexCompletionUnit R b).app ((derivedComplexCompletionFunctor R a).obj X)) ≫ g) :
    f = g := by
  apply derivedComplexCompletionHom_ext R b hb
  apply derivedComplexCompletionHom_ext R a ha
  simpa only [Category.assoc] using h

/-- 二つの元の単位の合成は、同じ元の射について自然。 -/
theorem pairCompletionUnits_naturality (a b : R)
    {X X' : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ X') :
    ((derivedComplexCompletionUnit R a).app X ≫
        (derivedComplexCompletionUnit R b).app ((derivedComplexCompletionFunctor R a).obj X)) ≫
      (derivedComplexCompletionFunctor R b).map ((derivedComplexCompletionFunctor R a).map f) =
    f ≫ (derivedComplexCompletionUnit R a).app X' ≫
      (derivedComplexCompletionUnit R b).app ((derivedComplexCompletionFunctor R a).obj X') := by
  have ha := (derivedComplexCompletionUnit R a).naturality f
  have hb := (derivedComplexCompletionUnit R b).naturality
    ((derivedComplexCompletionFunctor R a).map f)
  simp only [Functor.id_map] at ha hb
  rw [Category.assoc, ← hb, ← Category.assoc, ← ha, Category.assoc]

/-- 元の延長は、始域の同じ元の射について自然。 -/
theorem pairCompletionExtension_precomp (a b : R)
    {X X' Y : DerivedCategory (ModuleCat.{u} R)}
    (ha : IsComplete R a Y) (hb : IsComplete R b Y) (g : X ⟶ X') (f : X' ⟶ Y) :
    (derivedComplexCompletionFunctor R b).map ((derivedComplexCompletionFunctor R a).map g) ≫
      pairCompletionExtension a b X' Y ha hb f =
    pairCompletionExtension a b X Y ha hb (g ≫ f) := by
  apply pairCompletionExtension_ext a b X Y ha hb
  rw [← Category.assoc, pairCompletionUnits_naturality]
  rw [Category.assoc, Category.assoc,
    ← Category.assoc ((derivedComplexCompletionUnit R a).app X')]
  rw [pairCompletionExtension_unit, pairCompletionExtension_unit]

/-- 元の延長は、完備な終域への同じ元の射について自然。 -/
theorem pairCompletionExtension_postcomp (a b : R)
    {X Y Z : DerivedCategory (ModuleCat.{u} R)}
    (haY : IsComplete R a Y) (hbY : IsComplete R b Y)
    (haZ : IsComplete R a Z) (hbZ : IsComplete R b Z) (f : X ⟶ Y) (k : Y ⟶ Z) :
    pairCompletionExtension a b X Y haY hbY f ≫ k =
    pairCompletionExtension a b X Z haZ hbZ (f ≫ k) := by
  apply pairCompletionExtension_ext a b X Z haZ hbZ
  rw [← Category.assoc, pairCompletionExtension_unit, pairCompletionExtension_unit]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
