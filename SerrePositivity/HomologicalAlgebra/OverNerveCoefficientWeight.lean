module
public import SerrePositivity.HomologicalAlgebra.UnderOppositeOverNerve
public import SerrePositivity.HomologicalAlgebra.AlternatingFaceReverse

/-!
概要：BK の over nerve の各単体を線形化し、反対 under の線形重みと比較する。
方針：集合的重みの自然同型を係数の余積と二変数の交換で移し、鎖複体では反転符号を用いる。
規約：底の全射と単体作用素を保持する。順序反転の符号は省略しない。
使われ方：HA 1.2.4、G10 の bar と BK の線形 end 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type) [SmallCategory J]
variable {C : Type*} [Category* C] [HasCoproducts.{0} C]

/-- BK の共変 over nerve 重みを、各単体の係数余積で線形化する。 -/
def coefficientOverWeight (P : C) : SimplicialObject (J ⥤ C) :=
  (SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight J ⋙
    (SimplicialObject.whiskering (Type 0) C).obj (copowerFunctor P)).flip

/-- 二重反対圏を戻した、元の反対 under 重みの係数版。 -/
def reindexedCoefficientBarWeight (P : C) : SimplicialObject (J ⥤ C) :=
  ((opOpEquivalence J).inverse ⋙ underNerveWeight Jᵒᵖ ⋙
    (SimplicialObject.whiskering (Type 0) C).obj (copowerFunctor P)).flip

/-- 反対 under の係数重みは、BK の係数重みを単体的に順序反転したものと自然同型。 -/
def reindexedCoefficientBarWeightIso (P : C) :
    reindexedCoefficientBarWeight J P ≅ SimplicialObject.opFunctor.obj (coefficientOverWeight J P) :=
  (flipFunctor J SimplexCategoryᵒᵖ C).mapIso
    (Functor.isoWhiskerRight (underOppositeBousfieldKanWeightIso J)
      ((SimplicialObject.whiskering (Type 0) C).obj (copowerFunctor P)))

/-- 同じ係数付き under/over 重みの比較を、順序反転の符号を付けて鎖複体へ移す。 -/
def reindexedBarOverChainIso [Preadditive C] (P : C) :
    (alternatingFaceMapComplex (J ⥤ C)).obj (reindexedCoefficientBarWeight J P) ≅
      (alternatingFaceMapComplex (J ⥤ C)).obj (coefficientOverWeight J P) :=
  (alternatingFaceMapComplex (J ⥤ C)).mapIso (reindexedCoefficientBarWeightIso J P) ≪≫
    alternatingFaceReverseIso (coefficientOverWeight J P)

end SerrePositivity.HomologicalAlgebra
