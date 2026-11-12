module
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalParameters
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
概要：線形重みの非正規化 end と Moore 正規化後の end の積全複体を比較する。
方針：Dold–Kan の指定包含の鎖ホモトピー同値を、反変 end と積全複体へ移す。
規約：内部次数は非有界。前向き射は Moore 包含の前合成であり、全係数図式に自然。
使われ方：HA 1.2.4、G10 の線形 bar 計算から正規化された錐成分への移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- Moore 包含の前合成で、非正規化重みの end から正規化重みの end へ移る。 -/
def linearWeightEndNormalizationMap (X : Jᵒᵖ ⥤ Complex A)
    (W : SimplicialObject (Jᵒᵖ ⥤ ModuleCat.{u} A)) :
    (linearWeightEndTotalFunctor A X).obj (op ((alternatingFaceMapComplex _).obj W)) ⟶
      (linearWeightEndTotalFunctor A X).obj (op ((normalizedMooreComplex _).obj W)) :=
  (linearWeightEndTotalFunctor A X).map (inclusionOfMooreComplexMap W).op

/-- 指定 Moore 包含から得る同じ比較は、非有界な内部次数に対しても鎖ホモトピー同値。 -/
def linearWeightEndNormalizationHomotopyEquiv (X : Jᵒᵖ ⥤ Complex A)
    (W : SimplicialObject (Jᵒᵖ ⥤ ModuleCat.{u} A)) :
    HomotopyEquiv
      ((linearWeightEndTotalFunctor A X).obj (op ((alternatingFaceMapComplex _).obj W)))
      ((linearWeightEndTotalFunctor A X).obj (op ((normalizedMooreComplex _).obj W))) :=
  linearWeightEndTotalHomotopyEquiv A X
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := W))

/-- 鎖ホモトピー同値の前向き射は指定包含の前合成そのもの。 -/
theorem linearWeightEndNormalizationHomotopyEquiv_hom (X : Jᵒᵖ ⥤ Complex A)
    (W : SimplicialObject (Jᵒᵖ ⥤ ModuleCat.{u} A)) :
    (linearWeightEndNormalizationHomotopyEquiv A X W).hom =
      linearWeightEndNormalizationMap A X W := rfl

/-- 同じ正規化比較は係数図式の全射と可換。 -/
theorem linearWeightEndNormalizationMap_naturality {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y)
    (W : SimplicialObject (Jᵒᵖ ⥤ ModuleCat.{u} A)) :
    linearWeightEndNormalizationMap A X W ≫
        (linearWeightEndTotalMap A f).app (op ((normalizedMooreComplex _).obj W)) =
      (linearWeightEndTotalMap A f).app (op ((alternatingFaceMapComplex _).obj W)) ≫
        linearWeightEndNormalizationMap A Y W :=
  linearWeightEndTotalMap_naturality A f (inclusionOfMooreComplexMap W)

end SerrePositivity.HomologicalAlgebra
