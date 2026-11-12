module
public import SerrePositivity.HomologicalAlgebra.PointwiseTruncationAdjunction

/-!
概要：smart 切断と図式の点ごとの評価を交換する全自然同型。
方針：指定余単位と切断の mate を合成し、成分交換の単位で戻す。
規約：元の図式の対象と全射を保ち、複体に関しても自然。
使われ方：HA 1.2.4、G10 の Dold–Kan Hom 図式を点ごとに照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]

/-- 図式圏で切断してから評価する関手と、各点を切断する関手の指定同型。 -/
def pointwiseTruncationIso :
    (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (J ⥤ C) ⋙
      complexOfFunctorsToFunctorToComplex ≅
    complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (CochainComplex C ℤ) (ChainComplex C ℕ)).obj
        ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor C) := by
  let T := (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (J ⥤ C)
  let P := (Functor.whiskeringRight J (CochainComplex C ℤ) (ChainComplex C ℕ)).obj
    ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor C)
  let E := functorComplexExchangeEquivalence J C (ComplexShape.up ℤ)
  let D := functorComplexExchangeEquivalence J C (ComplexShape.down ℕ)
  exact isoWhiskerRight
    ((Functor.leftUnitor T).symm ≪≫ isoWhiskerRight E.counitIso.symm T ≪≫
      Functor.associator E.inverse E.functor T ≪≫
      isoWhiskerLeft E.inverse (truncationExchangeMate J C) ≪≫
      (Functor.associator E.inverse P D.functor).symm) D.inverse ≪≫
    Functor.associator (E.inverse ⋙ P) D.functor D.inverse ≪≫
    isoWhiskerLeft (E.inverse ⋙ P) D.unitIso.symm ≪≫ Functor.rightUnitor _

end SerrePositivity.HomologicalAlgebra
