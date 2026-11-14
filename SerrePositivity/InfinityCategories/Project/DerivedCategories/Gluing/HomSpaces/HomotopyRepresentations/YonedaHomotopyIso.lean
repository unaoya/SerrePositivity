module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.YonedaHomotopyFull

/-! 同じ全 Hom Yoneda 同型により、代表加群の K の同型を元の H⁰ の同型へ戻す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (X Y : C)

def dgGluingYonedaHomotopyPreimageIso
    (e : (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R) (representable R X)) ≅
      (moduleToHomotopy R C).obj (ForgetEnrichment.of (Complex R) (representable R Y))) :
    (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) X) ≅
      (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) Y) := by
  let F := dgYoneda R C
  have hF (x y : C) : IsIso (F.map x y) := by
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  letI := F.onHomotopy_full_of_homIso hF
  letI := F.onHomotopy_faithful_of_homIso hF
  exact F.onHomotopy.preimageIso e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
