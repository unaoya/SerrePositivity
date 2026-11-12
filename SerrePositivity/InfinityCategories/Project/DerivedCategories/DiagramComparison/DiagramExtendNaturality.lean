module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZTargetDiagram

/-!
概要：指定された図式交換・零延長の比較を、全図式射に自然な形へまとめる。
方針：元の単位・余単位と pointwiseExtendIso の全自然同型を合成する。
規約：negativeDiagramExchangeIso の成分を取り替えない。
使われ方：HA 1.2.4、G10 の図式 EZ の各点の指定 AW・shuffle との照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (J : Type v) [Category.{w} J] (A : Type u) [CommRing A]

/-- 元の零延長・図式交換の比較の全自然同型。 -/
def negativeDiagramExchangeNatIso :
    functorToComplexOfFunctors J (ModuleCat A) (.down ℕ) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (J ⥤ ModuleCat A) ≅
    (Functor.whiskeringRight J _ _).obj (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)) ⋙
      functorToComplexOfFunctors J (ModuleCat A) (.up ℤ) :=
  (Functor.isoWhiskerLeft
    (functorToComplexOfFunctors J (ModuleCat A) (.down ℕ) ⋙
      ComplexShape.embeddingDownNat.extendFunctor (J ⥤ ModuleCat A))
    (functorComplexExchangeCounitIso J (ModuleCat A) (.up ℤ))).symm ≪≫
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft
    (functorToComplexOfFunctors J (ModuleCat A) (.down ℕ))
    (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat))
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)) ≪≫
  Functor.isoWhiskerRight (Functor.isoWhiskerRight
    (functorComplexExchangeUnitIso J (ModuleCat A) (.down ℕ)).symm
    ((Functor.whiskeringRight J _ _).obj (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))))
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ))

/-- その各成分は元の指定同型である。 -/
theorem negativeDiagramExchangeNatIso_app (K : J ⥤ ChainComplex (ModuleCat A) ℕ) :
    (negativeDiagramExchangeNatIso J A).app K = negativeDiagramExchangeIso K := rfl

/-- 元の比較射は任意の複体値図式射に自然。 -/
@[reassoc]
theorem negativeDiagramExchangeIso_naturality
    {K L : J ⥤ ChainComplex (ModuleCat A) ℕ} (f : K ⟶ L) :
    extendMap ((functorToComplexOfFunctors J (ModuleCat A) (.down ℕ)).map f)
        ComplexShape.embeddingDownNat ≫ (negativeDiagramExchangeIso L).hom =
      (negativeDiagramExchangeIso K).hom ≫
        (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).map
          (Functor.whiskerRight f (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))) :=
  (negativeDiagramExchangeNatIso J A).hom.naturality f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
