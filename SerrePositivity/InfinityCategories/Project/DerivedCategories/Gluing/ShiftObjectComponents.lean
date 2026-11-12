module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ShiftObject

/-! 選んだ同じ実シフト候補の両成分は、元の代表加群のシフトを K(C)・K(D) で表す。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (n : ℤ)

/-- 同じ実シフト候補の左成分による、標準左シフト加群の K(C) の同型。 -/
def dgGluingShiftObject_leftIso
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (moduleToHomotopy R C).obj
      ((ForgetEnrichment.of (Complex R) (representable R X.left))⟦n⟧) ≅
    (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R)
      (representable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObject R C D M X n hC hD).left)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R C X.left n hC).comparison

/-- 同じ実シフト候補の右成分による、標準右シフト加群の K(D) の同型。 -/
def dgGluingShiftObject_rightIso
    (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (moduleToHomotopy R D).obj
      ((ForgetEnrichment.of (Complex R) (representable R X.right))⟦n⟧) ≅
    (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R)
      (representable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingShiftObject R C D M X n hC hD).right)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseShiftRepresentative R D X.right n hD).comparison

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
