module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDGCone
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseJoinSimplexShapes

/-!
概要：同じnative Tot錐の全join射を、小さい錐形状の指定ULiftで表示する。
方針：既存uliftConeShapeIsoを前合成し、その逆射則で元の全射を復元する。
規約：IS-W2 D01の既存構成の表示・係数移送則。native錐を作り直さない。
使われ方：HA 1.2.4、既存StrictCoherentFamilyの全パラメータ評価の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 同じ全native Tot錐を、既存の小さい錐形状のULiftで読む。 -/
def smallNativeTotConeDiagram (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,u}).obj
      (join (Δ[0] : SSet.{u}) (nerve (AsSmall.{u} SimplexCategory))) ⟶ dgNerve A (Complex A) :=
  (uliftConeShapeIso (nerve (AsSmall.{u} SimplexCategory)) 0).hom ≫
    (nativeDGCone X).val

/-- 表示の同型を戻すと、元の同じ全join射そのものになる。 -/
theorem smallNativeTotConeDiagram_restore (X : CosimplicialObject (Complex A)) :
    (uliftConeShapeIso (nerve (AsSmall.{u} SimplexCategory)) 0).inv ≫
      smallNativeTotConeDiagram X = (nativeDGCone X).val := by
  rw [smallNativeTotConeDiagram, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
