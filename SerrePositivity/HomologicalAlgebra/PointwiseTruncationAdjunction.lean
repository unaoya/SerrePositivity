module
public import SerrePositivity.HomologicalAlgebra.PointwiseExtendComplex
public import SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationAdjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：図式圏の smart 切断と点ごとの切断を随伴の一意性で比較する。
方針：零延長の指定評価比較を左随伴側で移し、右随伴の指定 mate を取る。
規約：比較は余単位と両立する全自然同型として保持する。
使われ方：HA 1.2.4、G10 の図式圏の Hom と点ごとの Hom 空間の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]

/-- 図式圏の切断を右随伴に持つ指定随伴。 -/
def diagramTruncationAdjunction :=
  ((negativeExtendTruncationAdjunction (J ⥤ C)).comp
    (functorComplexExchangeEquivalence J C (ComplexShape.up ℤ)).symm.toAdjunction).ofNatIsoLeft
      (pointwiseExtendIso J C ComplexShape.embeddingDownNat)

/-- 点ごとの切断を右随伴に持つ指定随伴。 -/
def pointwiseTruncationAdjunction :=
  (functorComplexExchangeEquivalence J C (ComplexShape.down ℕ)).symm.toAdjunction.comp
    (Adjunction.whiskerRight J (negativeExtendTruncationAdjunction C))

/-- 指定延長比較の右 mate による、二つの切断の全自然同型。 -/
def truncationExchangeMate :=
  Adjunction.rightAdjointUniq (diagramTruncationAdjunction J C)
    (pointwiseTruncationAdjunction J C)

/-- 比較後の切断包含は、元の図式圏の切断包含と一致する。 -/
@[reassoc]
theorem truncationExchangeMate_counit (X : J ⥤ CochainComplex C ℤ) :
    (complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (CochainComplex C ℤ)).obj
        (ComplexShape.embeddingDownNat.extendFunctor C)).map
          ((truncationExchangeMate J C).hom.app X) ≫
      (pointwiseTruncationAdjunction J C).counit.app X =
        (diagramTruncationAdjunction J C).counit.app X :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ X

end SerrePositivity.HomologicalAlgebra
