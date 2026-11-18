module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.CosimplicialModuleCone
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.StrictHomology

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (A : Type u) [CommRing A]

/-- D08：整数次数へ零延長した同じ交代余面複体への全次数のホモロジー入口。 -/
def cosimplicialModuleCone_homology (M : CosimplicialObject (ModuleCat.{u} A)) (i : ℤ) :
    derivedInfinityHomology A i (cosimplicialModuleCone A M).vertex ≃ₗ[A]
      ((discreteCochainFunctor A).obj M).homology i := by
  rw [cosimplicialModuleCone_vertex]
  exact ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSourceHomologyIso A i).app
    ((discreteCochainFunctor A).obj M)).toLinearEquiv

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
