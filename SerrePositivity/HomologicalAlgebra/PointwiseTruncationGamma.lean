module
public import SerrePositivity.HomologicalAlgebra.PointwiseTruncation
public import SerrePositivity.HomologicalAlgebra.DoldKanGammaDiagram

/-!
概要：図式圏の切断と Γ の合成を、各対象の Dold–Kan 空間と比較する。
方針：切断の指定 mate と Γ の指定余積比較を全関手の同型として合成する。
規約：複体射、添字圏の射、単体作用素のすべてについて自然。
使われ方：HA 1.2.4、G10 の集合的 BK 錐を点ごとの Hom 図式へ渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type*) [Category* J] (C : Type*) [Category* C] [Abelian C]

/-- 図式圏の切断から取った Γ と、各点の切断から取った Γ の全自然同型。 -/
def pointwiseTruncationGammaIso :
    (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (J ⥤ C) ⋙
      diagramGammaFunctor J C ≅
    (complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight J (CochainComplex C ℤ) (ChainComplex C ℕ)).obj
        ((ComplexShape.embeddingUpIntLE 0).truncLE'Functor C)) ⋙
      (Functor.whiskeringRight J (ChainComplex C ℕ) (SimplicialObject C)).obj
        Abelian.DoldKan.Γ :=
  isoWhiskerLeft _ (pointwiseGammaIso J C).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (pointwiseTruncationIso J C) _

end SerrePositivity.HomologicalAlgebra
