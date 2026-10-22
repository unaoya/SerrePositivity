module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputHomotopies
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputTriangleEvaluations
public import SerrePositivity.InfinityCategories.Derived.Gluing.FamilyAlongHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomArrowCompositionTriangles

/-! 元の二三角形から係数模型の二三角形への全時間族と、その厳密な両時刻。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingLaxHomFirstTriangleHomotopyFamily (X Y : DGGluingObject R C D M) :=
  dgGluingFamilyAlongHomotopy (dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y)
    (dgGluingLaxHomFirstInputHomotopy R C D M X Y)

def dgGluingLaxHomLastTriangleHomotopyFamily (X Y : DGGluingObject R C D M) :=
  dgGluingFamilyAlongHomotopy (dgGluingDerivedLastInputTriangleEvaluation R C D M X Y)
    (dgGluingLaxHomLastInputHomotopy R C D M X Y)

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_zero (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ (SSet.ι₀ : _ ⟶ _)) ≫ dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      (dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  rw [dgGluingLaxHomFirstTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_zero,
    dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingLaxHomFirstCompositionInputLift_composition R C D M X Y,
    dgGluingLaxHomArrowCompositionComparison_first_triangle R C D M X Y]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_zero (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ (SSet.ι₀ : _ ⟶ _)) ≫ dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      (dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  rw [dgGluingLaxHomLastTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_zero,
    dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingLaxHomLastCompositionInputLift_composition R C D M X Y,
    dgGluingLaxHomArrowCompositionComparison_last_triangle R C D M X Y]

lemma dgGluingLaxHomFirstTriangleHomotopyFamily_one (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ (SSet.ι₁ : _ ⟶ _)) ≫ dgGluingLaxHomFirstTriangleHomotopyFamily R C D M X Y =
      dgGluingHomDerivedRightCoefficientTriangle R C D M X Y := by
  rw [dgGluingLaxHomFirstTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_one,
    dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y,
    dgGluingHomDerivedFirstComposition_triangle R C D M X Y]

lemma dgGluingLaxHomLastTriangleHomotopyFamily_one (X Y : DGGluingObject R C D M) :
    (Δ[2] ◁ (SSet.ι₁ : _ ⟶ _)) ≫ dgGluingLaxHomLastTriangleHomotopyFamily R C D M X Y =
      dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y := by
  rw [dgGluingLaxHomLastTriangleHomotopyFamily, dgGluingFamilyAlongHomotopy_one,
    dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y,
    dgGluingHomDerivedLastComposition_triangle R C D M X Y]

end SerrePositivity.InfinityCategories
