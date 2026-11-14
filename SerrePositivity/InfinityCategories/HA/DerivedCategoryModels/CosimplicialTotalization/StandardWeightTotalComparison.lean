module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardWeightEnd
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductTotal
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalization
public import SerrePositivity.HomologicalAlgebra.AlternatingFaceOpposite
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex

/-!
概要：標準単体重みの鎖複体からの線形 end の積全複体を、元の余単体図式の積 Tot と比べる。
方針：反対化・加法的関手との交代余面複体の交換・自由 Yoneda 評価を順に合成する。
規約：各横次数の比較は恒等射の生成元での 1 の評価。内部次数の有界性は不要。
使われ方：HA 1.2.4、G10 の射影分解比較と元の指定積全複体をつなぐ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 標準重みの鎖複体からの線形 end と元の交代余面二重複体との指定同型。 -/
def standardWeightEndCochainIso (X : CosimplicialObject (Complex A)) :
    (linearWeightEndCochainFunctor A (doubleOppositeDiagram X)).obj
      (op (AlternatingFaceMapComplex.obj (standardSimplexWeight (ModuleCat.of A A)))) ≅
        AlternatingCofaceMapComplex.obj X :=
  ((linearWeightEnd A (doubleOppositeDiagram X)).mapHomologicalComplex (.up ℕ)).mapIso
      (alternatingFaceOppositeIso (standardSimplexWeight (ModuleCat.of A A))) ≪≫
    (SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (linearWeightEnd A (doubleOppositeDiagram X))).app
        (standardSimplexWeight (ModuleCat.of A A)).rightOp ≪≫
    (alternatingCofaceMapComplex (Complex A)).mapIso (standardWeightEndIso X)

/-- 同じ二重複体比較の横次数 n は元の自由単位重みの評価鎖写像。 -/
theorem standardWeightEndCochainIso_hom_f (X : CosimplicialObject (Complex A)) (n : ℕ) :
    (standardWeightEndCochainIso X).hom.f n =
      ((freeUnitWeightEndNatIso A (op ⦋n⦌)).app (doubleOppositeDiagram X)).hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- 標準重みからの線形 end の積全複体は、元の指定された積 Tot と同型。 -/
def standardWeightEndTotalIso (X : CosimplicialObject (Complex A)) :
    (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).obj
      (op (AlternatingFaceMapComplex.obj (standardSimplexWeight (ModuleCat.of A A)))) ≅
        (productTotalFunctor A).obj X :=
  (cochainProductTotalizationFunctor (ModuleCat.{u} A)).mapIso (standardWeightEndCochainIso X)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
