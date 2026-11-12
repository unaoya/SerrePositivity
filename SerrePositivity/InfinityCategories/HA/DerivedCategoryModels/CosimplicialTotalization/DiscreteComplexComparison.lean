module
public import SerrePositivity.HomologicalAlgebra.ProductTotalSingleRow
public import SerrePositivity.HomologicalAlgebra.MapExtendComplex
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComponents

/-!
概要：離散余単体加群の積 Tot を、交代余面複体の整数次数への零延長と自然同型で結ぶ。
方針：離散化と交代余面・零延長を交換し、一行二重複体の指定射影による同型を適用する。
規約：図式の射を含む複体の自然同型。native 極限性・錐の族は後続で証明する。
使われ方：HA 1.2.4、G10 の加群版と BS の cosimplicialCochains の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]

/-- 加群の交代余面複体を整数次数へ零延長する、比較先の全関手。 -/
def discreteCochainFunctor : CosimplicialObject (ModuleCat.{u} A) ⥤ Complex A :=
  alternatingCofaceMapComplex (ModuleCat.{u} A) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)

/-- 離散入力の二重複体は、零延長された交代余面複体を縦次数零へ置いたものと自然同型。 -/
def discreteDoubleComplexIso :
    discreteDiagramFunctor A ⋙ doubleComplexFunctor A ≅
      discreteCochainFunctor A ⋙
        SerrePositivity.HomologicalAlgebra.ProductTotal.singleRowFunctor (ModuleCat.{u} A) := by
  let S := HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0
  let h₁ := Functor.isoWhiskerRight
    (SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso S).symm
    (ComplexShape.embeddingUpNat.extendFunctor (Complex A))
  let h₂ := Functor.isoWhiskerLeft (alternatingCofaceMapComplex (ModuleCat.{u} A))
    (SerrePositivity.HomologicalAlgebra.mapExtendNatIso S ComplexShape.embeddingUpNat).symm
  exact h₁ ≪≫ h₂

/-- 同じ離散積 Tot と、零延長された交代余面複体の全関手の自然同型。 -/
def discreteTotalCochainNatIso : discreteTotalFunctor A ≅ discreteCochainFunctor A :=
  Functor.isoWhiskerRight (discreteDoubleComplexIso A)
      (SerrePositivity.HomologicalAlgebra.ProductTotal.functor (ModuleCat.{u} A)) ≪≫
    Functor.isoWhiskerLeft (discreteCochainFunctor A)
      (SerrePositivity.HomologicalAlgebra.ProductTotal.singleRowNatIso (ModuleCat.{u} A))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
