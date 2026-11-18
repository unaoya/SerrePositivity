module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedTotCone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ComplexStrictNerveComparison

/-!
概要：指定Tot錐の底図式を、同じ元のstrict余単体図式と厳密に同定する。
方針：coherent比較の既存閉零包含との全単体の等式を使う。
規約：IS-W2 C05、元の図式と添字同型を固定する。
使われ方：HA 1.2.4、指定導来極限錐の同じ全join射の移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 同じ指定導来図式は、元のstrict図式の全単体の像に等しい。 -/
theorem nativeDerivedDiagram_eq (X : CosimplicialObject (Complex A)) :
    nativeDerivedDiagram X = nativeTotIndexIso.hom ≫ strictCosimplicialComplexNerve X ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A := by
  unfold nativeDerivedDiagram nativeDGDiagram strictCoherentDiagram
  simp only [Category.assoc]
  erw [← Category.assoc
    (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent
      (ClosedCategory A (Complex A)))
    (SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison)
    (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionInfinity A), complexClosedNerve_coherentComparison]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
