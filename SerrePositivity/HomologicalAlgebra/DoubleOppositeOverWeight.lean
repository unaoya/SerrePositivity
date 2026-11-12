module
public import SerrePositivity.HomologicalAlgebra.OverNerveCoefficientWeight

/-!
概要：BK の over 重みを二重反対圏へ移し、元の bar 鎖重みと同じ底で比べる。
方針：二重反対圏の前合成と交代面複体の交換を、係数付き under/over の鎖同型に合成する。
規約：元の bar を選び直さない。over 側だけを明示的に前合成する。
使われ方：HA 1.2.4、G10 の構成済み線形 end と BK 重みを接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type) [SmallCategory J]
variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{0} C]

/-- BK の over 係数重みを、既存 bar と同じ二重反対圏の底へ前合成する。 -/
def doubleOppositeOverWeight (P : C) : SimplicialObject (Jᵒᵖᵒᵖ ⥤ C) :=
  coefficientOverWeight J P ⋙
    (Functor.whiskeringLeft Jᵒᵖᵒᵖ J C).obj (opOpEquivalence J).functor

/-- 元の bar 鎖重みと、底を二重反対圏へ移した BK over 鎖重みとの指定同型。 -/
def barDoubleOppositeOverChainIso (P : C) :
    (alternatingFaceMapComplex (Jᵒᵖᵒᵖ ⥤ C)).obj (coefficientBarWeight Jᵒᵖ P) ≅
      (alternatingFaceMapComplex (Jᵒᵖᵒᵖ ⥤ C)).obj (doubleOppositeOverWeight J P) :=
  ((alternatingFaceMapComplexCompMapHomologicalComplexIso
      ((Functor.whiskeringLeft Jᵒᵖᵒᵖ J C).obj (opOpEquivalence J).functor)).app
        (reindexedCoefficientBarWeight J P)).symm ≪≫
    (((Functor.whiskeringLeft Jᵒᵖᵒᵖ J C).obj (opOpEquivalence J).functor).mapHomologicalComplex
      (.down ℕ)).mapIso (reindexedBarOverChainIso J P) ≪≫
    (alternatingFaceMapComplexCompMapHomologicalComplexIso
      ((Functor.whiskeringLeft Jᵒᵖᵒᵖ J C).obj (opOpEquivalence J).functor)).app
        (coefficientOverWeight J P)

end SerrePositivity.HomologicalAlgebra
